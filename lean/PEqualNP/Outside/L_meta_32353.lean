import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32353_aux


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
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 4 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)


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




def cuts224 : Cuts (goalAt 224) := []

def state224_0 : List Sig := roots 224
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude224_0 : Impossible true (goalAt 224) 3 state224_0.toFinset :=
  node_ok cuts224 [] 0x30100602030100a02030200c08030100c08030200a02018080602028080604018100c04028200a08028080a08028200c04018100604018080a08028200c08018100c08018080604018100c08028200a080 (by decide +kernel)

theorem lower224 : Claim 224 4 :=
  fromSearch 1432354816 (by decide +kernel) exclude224_0

def cuts193 : Cuts (goalAt 193) := []

def state193_0 : List Sig := roots 193
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude193_0 : Impossible true (goalAt 193) 3 state193_0.toFinset :=
  node_ok cuts193 [] 0x30100410130100810130200c08030100c08030200810110404410120404414010500c04020600818020404818020600c04010500414010404818020600c08010500c08010404414010500c080206008180 (by decide +kernel)

theorem lower193 : Claim 193 4 :=
  fromSearch 6 (by decide +kernel) exclude193_0

def cuts161 : Cuts (goalAt 161) := []

def state161_0 : List Sig := roots 161
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude161_0 : Impossible true (goalAt 161) 3 state161_0.toFinset :=
  node_ok cuts161 [] 0x28080210128080810128200a08028080a08028200810108404210120404212008480a02020600818020404818020600a02008480212008404818020600a08008480a08008404212008480a080206008180 (by decide +kernel)

theorem lower161 : Claim 161 4 :=
  fromSearch 5 (by decide +kernel) exclude161_0

def rule225_0 : {c : Cut // CutGood (goalAt 225) c} :=
  ruleFor 225 lower224 none (by decide +kernel)

def rule225_1 : {c : Cut // CutGood (goalAt 225) c} :=
  ruleFor 225 lower193 none (by decide +kernel)

def rule225_2 : {c : Cut // CutGood (goalAt 225) c} :=
  ruleFor 225 lower161 none (by decide +kernel)

def cuts225 : Cuts (goalAt 225) := [rule225_0,rule225_1,rule225_2]

def state225_0 : List Sig := roots 225
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude225_0 : Impossible true (goalAt 225) 5 state225_0.toFinset :=
  node_ok cuts225 [] 0x40008c04018080c04040008a02030200c08040008c04030200c08040008a02018080602040004a02018100604040004c04028200a08040004a02028200a08040004c04018100604040004602028200a08040004c08018100c08040004602018100604040004c08028200a08040000810110500414040000c04020600818040000810120600818040000c04010500414040000410120600818040000c08010500c08040000410110500414040000c08020600818040000210120600818040000a08008480a08040000210108480212040000a080206008180 (by decide +kernel)

theorem lower225 : Claim 225 6 :=
  fromSearch 5 (by decide +kernel) exclude225_0

def cuts208 : Cuts (goalAt 208) := []

def state208_0 : List Sig := roots 208
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude208_0 : Impossible true (goalAt 208) 3 state208_0.toFinset :=
  node_ok cuts208 [] 0x30100501030100901030200c08030100c08030200901014040501024040504014100c04024200908024040908024200c04014100504014040908024200c08014100c08014040504014100c080242009080 (by decide +kernel)

theorem lower208 : Claim 208 4 :=
  fromSearch 1141243904 (by decide +kernel) exclude208_0

def cuts145 : Cuts (goalAt 145) := []

def state145_0 : List Sig := roots 145
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude145_0 : Impossible true (goalAt 145) 3 state145_0.toFinset :=
  node_ok cuts145 [] 0x240401101240408101242009080240409080242008101044041101204041110044409010206008180204048180206009010044401110044048180206009080044409080044041110044409080206008180 (by decide +kernel)

theorem lower145 : Claim 145 4 :=
  fromSearch 4 (by decide +kernel) exclude145_0

def rule209_0 : {c : Cut // CutGood (goalAt 209) c} :=
  ruleFor 209 lower208 none (by decide +kernel)

def rule209_1 : {c : Cut // CutGood (goalAt 209) c} :=
  ruleFor 209 lower193 none (by decide +kernel)

def rule209_2 : {c : Cut // CutGood (goalAt 209) c} :=
  ruleFor 209 lower145 none (by decide +kernel)

def cuts209 : Cuts (goalAt 209) := [rule209_0,rule209_1,rule209_2]

def state209_0 : List Sig := roots 209
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude209_0 : Impossible true (goalAt 209) 5 state209_0.toFinset :=
  node_ok cuts209 [] 0x40008c04014040c04040008901030200c08040008c04030200c08040008901014040501040004901014100504040004c04024200908040004901024200908040004c04014100504040004501024200908040004c08014100c08040004501014100504040004c08024200908040000810110500414040000c04020600818040000810120600818040000c04010500414040000410120600818040000c08010500c08040000410110500414040000c080206008180400001101206008180400009080044409080400001101044401110400009080206008180 (by decide +kernel)

theorem lower209 : Claim 209 6 :=
  fromSearch 4 (by decide +kernel) exclude209_0

def cuts176 : Cuts (goalAt 176) := []

def state176_0 : List Sig := roots 176
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude176_0 : Impossible true (goalAt 176) 3 state176_0.toFinset :=
  node_ok cuts176 [] 0x28080301028080901028200a08028080a0802820090100c04030102404030200c080a02024200908024040908024200a0200c08030200c040908024200a0800c080a0800c04030200c080a080242009080 (by decide +kernel)

theorem lower176 : Claim 176 4 :=
  fromSearch 1078263808 (by decide +kernel) exclude176_0

def rule240_0 : {c : Cut // CutGood (goalAt 240) c} :=
  ruleFor 240 lower224 none (by decide +kernel)

def rule240_1 : {c : Cut // CutGood (goalAt 240) c} :=
  ruleFor 240 lower208 none (by decide +kernel)

def rule240_2 : {c : Cut // CutGood (goalAt 240) c} :=
  ruleFor 240 lower176 none (by decide +kernel)

def cuts240 : Cuts (goalAt 240) := [rule240_0,rule240_1,rule240_2]

def state240_0 : List Sig := roots 240
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude240_0 : Impossible true (goalAt 240) 5 state240_0.toFinset :=
  node_ok cuts240 [] 0x40008c04018080c04040008a02030200c08040008c04030200c08040008a02018080602040004a02018100604040004c04028200a08040004a02028200a08040004c04018100604040004602028200a08040004c08018100c08040004602018100604040004c08028200a08040000901014100504040000c04024200908040000901024200908040000c04014100504040000501024200908040000c08014100c08040000501014100504040000c08024200908040000301024200908040000a0800c080a0804000030100c080302040000a080242009080 (by decide +kernel)

theorem lower240 : Claim 240 6 :=
  fromSearch 1145372672 (by decide +kernel) exclude240_0

def cuts112 : Cuts (goalAt 112) := []

def state112_0 : List Sig := roots 112
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude112_0 : Impossible true (goalAt 112) 3 state112_0.toFinset :=
  node_ok cuts112 [] 0x1808030101808050101810060401808060401810050100c04030101404030200c08060201410050401404050401410060200c08030200c04050401410060400c08060400c04030200c0806040141005040 (by decide +kernel)

theorem lower112 : Claim 112 4 :=
  fromSearch 71630848 (by decide +kernel) exclude112_0

def cuts97 : Cuts (goalAt 97) := []

def state97_0 : List Sig := roots 97
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude97_0 : Impossible true (goalAt 97) 3 state97_0.toFinset :=
  node_ok cuts97 [] 0x180802101180804101181006040180806040181004101084042101104042120084806020105004140104044140105006020084802120084044140105006040084806040084042120084806040105004140 (by decide +kernel)

theorem lower97 : Claim 97 4 :=
  fromSearch 5 (by decide +kernel) exclude97_0

def cuts81 : Cuts (goalAt 81) := []

def state81_0 : List Sig := roots 81
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude81_0 : Impossible true (goalAt 81) 3 state81_0.toFinset :=
  node_ok cuts81 [] 0x140401101140404101141005040140405040141004101044041101104041110044405010105004140104044140105005010044401110044044140105005040044405040044041110044405040105004140 (by decide +kernel)

theorem lower81 : Claim 81 4 :=
  fromSearch 4 (by decide +kernel) exclude81_0

def rule113_0 : {c : Cut // CutGood (goalAt 113) c} :=
  ruleFor 113 lower112 none (by decide +kernel)

def rule113_1 : {c : Cut // CutGood (goalAt 113) c} :=
  ruleFor 113 lower97 none (by decide +kernel)

def rule113_2 : {c : Cut // CutGood (goalAt 113) c} :=
  ruleFor 113 lower81 none (by decide +kernel)

def cuts113 : Cuts (goalAt 113) := [rule113_0,rule113_1,rule113_2]

def state113_0 : List Sig := roots 113
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude113_0 : Impossible true (goalAt 113) 5 state113_0.toFinset :=
  node_ok cuts113 [] 0x4000860200c04060204000850101810060404000860201810060404000850100c04030104000450100c08030204000460201410050404000450101410050404000460200c08030204000430101410050404000460400c08060404000430100c0803020400046040141005040400004101084802120400006020105004140400004101105004140400006020084802120400002101105004140400006040084806040400002101084802120400006040105004140400001101105004140400005040044405040400001101044401110400005040105004140 (by decide +kernel)

theorem lower113 : Claim 113 6 :=
  fromSearch 4 (by decide +kernel) exclude113_0

def rule241_0 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower225 none (by decide +kernel)

def rule241_1 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower209 none (by decide +kernel)

def rule241_2 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower240 none (by decide +kernel)

def rule241_3 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower113 none (by decide +kernel)

def cuts241 : Cuts (goalAt 241) := [rule241_0,rule241_1,rule241_2,rule241_3]

def state241_0 : List Sig := roots 241
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_0 : Impossible true (goalAt 241) 7 state241_0.toFinset :=
  node_ok cuts241 [] 0x4000cc04018080c0404000ca02030200c0804000cc04030200c0804000ca02018080602040004a02018100604040004c04028200a08040004a02028200a08040004c04018100604040004602028200a08040004c08018100c08040004602018100604040004c08028200a08040000901014100504040000c04024200908040000901024200908040000c04014100504040000501024200908040000c08014100c08040000501014100504040000c08024200908040000301024200908040000a0800c080a0804000030100c080302040000a0802420090804000c81011050041404000cc0402060081804000c81012060081804000cc04010500414040008410120600818040008c08010500c08040008410110500414040008c08020600818040004210120600818040004a08008480a08040004210108480212040004a080206008180400001101206008180400009080044409080400001101044401110400009080206008180 (by decide +kernel)

theorem lower241 : Claim 241 8 :=
  fromSearch 4 (by decide +kernel) exclude241_0

theorem lower226 : Claim 226 5 :=
  fromLift 5 2 1427112016 lower224 (by decide +kernel)

theorem lower210 : Claim 210 5 :=
  fromLift 5 2 1140916288 lower208 (by decide +kernel)

theorem lower178 : Claim 178 5 :=
  fromLift 5 2 1074856000 lower176 (by decide +kernel)

theorem lower114 : Claim 114 5 :=
  fromLift 5 2 68223040 lower112 (by decide +kernel)

def cuts50 : Cuts (goalAt 50) := []

def state50_0 : List Sig := roots 50
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude50_0 : Impossible true (goalAt 50) 3 state50_0.toFinset :=
  node_ok cuts50 [] 0xc04012020c04022020c08030200c04030200c0802202048081202088081210048403010088802220088082220088803010048401210048082220088803020048403020048081210048403020088802220 (by decide +kernel)

theorem lower50 : Claim 50 4 :=
  fromSearch 1114176 (by decide +kernel) exclude50_0

def rule242_0 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower240 none (by decide +kernel)

def rule242_1 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower226 none (by decide +kernel)

def rule242_2 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower210 none (by decide +kernel)

def rule242_3 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower178 none (by decide +kernel)

def rule242_4 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower114 none (by decide +kernel)

def rule242_5 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower50 none (by decide +kernel)

def rule242_6 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower176 none (by decide +kernel)

def rule242_7 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower224 none (by decide +kernel)

def rule242_8 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower208 none (by decide +kernel)

def rule242_9 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower112 none (by decide +kernel)

def cuts242 : Cuts (goalAt 242) := [rule242_0,rule242_1,rule242_2,rule242_3,rule242_4,rule242_5,rule242_6,rule242_7,rule242_8,rule242_9]

def state242_0 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_0 : Impossible true (goalAt 242) 4 state242_0.toFinset :=
  node_ok cuts242 [] 0xc04228080c04208880c08230200c08208880c04230208c0820c080a02030108a02030108222004840222004840302030208302030208a28214108924228080504208880504214109000624a08928214108c082 (by decide +kernel)

def state242_1 : List Sig := [0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000,input 5,input 4,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_1 : Impossible true (goalAt 242) 4 state242_1.toFinset :=
  node_ok cuts242 [] 0x30108a02030108222030208c0803020900001410892422404050420c08050421410822201410860420c080504224a08604228908a02018108222018108604204840a28230108c082302090005 (by decide +kernel)

def state242_2 : List Sig := [0xffffffff00000000ffff000000000000ffffffff00000000ffff0000,input 5,input 4,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_2 : Impossible true (goalAt 242) 4 state242_2.toFinset :=
  node_ok cuts242 [] 0xc04228080c04208880504224908901014108302014108504208880b28228a08302028a08a02028a08a28218a08a08028a08a08228208c04230208c08228080c08030208c08208880928224a085042302086042 (by decide +kernel)

def state242_3 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_3 : Impossible true (goalAt 242) 5 state242_3.toFinset :=
  node_ok cuts242 [⟨state242_0,exclude242_0⟩,⟨state242_1,exclude242_1⟩,⟨state242_2,exclude242_2⟩] 0xa02018108604230108a28228a08a02028a08a28230108604218108222028200a08004840a28228a08222028a08a08204840a0802820a000228a08a2823020860423020a000118108604230208a28228a08c04208880c04228081000628080c04240014c04228080222008880c08208880c08240000121030200c08204840c08240000222008880901014108504230109000724908901040014901030108504214108301014108504228a09000728a08301080000301028a08504228a0812104001812100888050421410812101410850420888100070888100034000c928230109000530108a02030208c08230108c08230208a02040014a020 (by decide +kernel)

def state242_4 : List Sig := [0xffff0000ffff0000ffff000000000000ffff0000ffff0000ffff00000000,input 4,input 5,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_4 : Impossible true (goalAt 242) 4 state242_4.toFinset :=
  node_ok cuts242 [] 0xc04228080c04208880604228908a02018108222018108604204840901024a08928214a08908024a0890822420892822ca08301024a08c04230208c08224040c08030208c08204840a28228a086042302085042 (by decide +kernel)

def state242_5 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_5 : Impossible true (goalAt 242) 4 state242_5.toFinset :=
  node_ok cuts242 [] 0xc04228080c04208880c08230200c08204840c04230208c0820c040302030108901030108302008880121008880301030208302030208928218108a24228080604208880604218109000628a08a28218108c082 (by decide +kernel)

def state242_6 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_6 : Impossible true (goalAt 242) 5 state242_6.toFinset :=
  node_ok cuts242 [⟨state242_1,exclude242_1⟩,⟨state242_4,exclude242_4⟩,⟨state242_5,exclude242_5⟩] 0x901014108504230108928224a08901024a08928230108504214108121024200908008880928224a08121024a08908208880908024209000824a0892821810830201810a00020c080302018108928224a0a000124a0892823020850423020a000014108504230208928224a08c04208880c04228081000628080c04240014c04228080222008880c08204840c08240000222030200c08208880c08240000121004840a02018108604230109000828908a02040014a0203010860421810822204001822200484060421810822201810860420484100080484100034000ca28230109000530108901030208c08230108c082302089010400149010 (by decide +kernel)

def state242_7 : List Sig := [0x333333333333000000000000000000003333333333330000,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_7 : Impossible true (goalAt 242) 4 state242_7.toFinset :=
  node_ok cuts242 [] 0xc04230208c08228080604228a08a28218108a28230208604228a08504224a08928214108928230208504224a08928228a08302024a08222030108a02030108602028208a08208880a2822420890820c0809282 (by decide +kernel)

def state242_8 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_8 : Impossible true (goalAt 242) 5 state242_8.toFinset :=
  node_ok cuts242 [⟨state242_1,exclude242_1⟩,⟨state242_0,exclude242_0⟩,⟨state242_5,exclude242_5⟩,⟨state242_7,exclude242_7⟩] 0x30108c08230208a02030200c04228080c04208880a02030108a0203010830103020a000230208222004840222004840a2820c080c04224040c0420c080c08280004c0820c08022200484022200c04030204001c928228080c04228080c0424000cc08280000c082088820003088810006 (by decide +kernel)

def state242_9 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_9 : Impossible true (goalAt 242) 6 state242_9.toFinset :=
  node_ok cuts242 [⟨state242_3,exclude242_3⟩,⟨state242_6,exclude242_6⟩,⟨state242_8,exclude242_8⟩] 0x40014a02018108604240020c04228a08a28240014a02028a08a28240020c0421810860424000d000328a08a2824000cc08218108c0824000e00011810860424000cc08228a08a28240018222028200a08040020121028a08a28240018222028a08a08240020121028200a0824001490101410850424001cc04224a08928240014901024a0892824001cc04214108504240020301024a0892824001ca2820c080a2828000830100c08030204001ca28224a0892824000d000324a0892824000cc08214108c0824000e00001410850424000cc08224a0892824001812102420090804001c222024a08928240018121024a0890824001c22202420090824000cc04240014c0424000ca02030208c0824000cc04230208c0824000ca0204000ca02040001000040000c08040018c04208880c04240018a02040018a02040018c04240014c04240018a020088802220 (by decide +kernel)

def state242_10 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_10 : Impossible true (goalAt 242) 4 state242_10.toFinset :=
  node_ok cuts242 [] 0x602030208c08208880c04230208c0820c080c04230100c04208880602030208602030208222004840222004840302030108302030108a08224208c08218080908208880908224209000914908908224208c042 (by decide +kernel)

def state242_11 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 5,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_11 : Impossible true (goalAt 242) 4 state242_11.toFinset :=
  node_ok cuts242 [] 0x18080c08230208222030108c08230209000630108c04030109000024208c0821404090820c080908224208222024208a0820c080908214908a08230208602028208222028208a082048406242 (by decide +kernel)

def state242_12 : List Sig := [0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,input 5,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_12 : Impossible true (goalAt 242) 4 state242_12.toFinset :=
  node_ok cuts242 [] 0x602030208c08208880908230208501024208302024208908208880908218908302024208602030208624230208604018908604218108c08230108c08218080c04030108c04208880908214908908230108a082 (by decide +kernel)

def state242_13 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_13 : Impossible true (goalAt 242) 5 state242_13.toFinset :=
  node_ok cuts242 [⟨state242_10,exclude242_10⟩,⟨state242_11,exclude242_11⟩,⟨state242_12,exclude242_12⟩] 0x1000518080602008880c08230209000530208c08208880602008880c04218080c04240018c08230208c04230208c08240018602018080602028208a08230208624230208602018908624230208a08228208222018100604004840a08228208222028208a0820484060401810a000218908624230108a0822820a000128208a08230108624218908c04208880c04240000121030100c04204840c042400002220088805010242089082302090007302085010400145010302089082242083010242089082282090007282083010800003010282089082242081210400241210088809082242081210242089082088810007088810004400105242 (by decide +kernel)

def state242_14 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000,input 4,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_14 : Impossible true (goalAt 242) 4 state242_14.toFinset :=
  node_ok cuts242 [] 0x602030208c08208880a08230208602028208222028208a08204840501030208524230208504014908504214108524228208301028208c08230108c08214040c04030108c04204840a08218908a082301089082 (by decide +kernel)

def state242_15 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_15 : Impossible true (goalAt 242) 4 state242_15.toFinset :=
  node_ok cuts242 [] 0x602030208c08208880c04230208c0820c040c04230100c04204840302030208501030208302008880121008880301030108302030108908228208c08218080a08208880a08228209000918908a08228208c042 (by decide +kernel)

def state242_16 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_16 : Impossible true (goalAt 242) 5 state242_16.toFinset :=
  node_ok cuts242 [⟨state242_11,exclude242_11⟩,⟨state242_14,exclude242_14⟩,⟨state242_15,exclude242_15⟩] 0x1000518080602008880c08230209000530208c08208880602008880c04214040c04240018c08230208c04230208c0824001850101404050102420890823020852423020850101490852423020890822420812101410050400888090822420812102420890820888050401410900082420890822820830202820a00020c08030202820890822420a00011490852423010890822420a000024208908230108524214908c04204840c04240000222030100c04208880c04240000121004840602028208a08230209000830208602040014602030208a08228208222040024222004840a08228208222028208a082048410008048410004400106242 (by decide +kernel)

def state242_17 : List Sig := [0x33333333333300003333333333330000,input 4,input 5,input 7,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_17 : Impossible true (goalAt 242) 4 state242_17.toFinset :=
  node_ok cuts242 [] 0xc04230208c08218080a08230208624228208624228208a08218908908230208524224208524224208908214908908228208302024208222030208602030208a02018108a08208880a0821410890820c0809082 (by decide +kernel)

def state242_18 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_18 : Impossible true (goalAt 242) 5 state242_18.toFinset :=
  node_ok cuts242 [⟨state242_11,exclude242_11⟩,⟨state242_10,exclude242_10⟩,⟨state242_15,exclude242_15⟩,⟨state242_17,exclude242_17⟩] 0x30108c08230208602018080c0823020822203010060203020860203020830103010a000230108222004840222004840a0820c080c08214040c0820c080c04280004c0420c08022200484022200c04030204001c908218080c08218080c08240010c04280000c042088820003088810009 (by decide +kernel)

def state242_19 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_19 : Impossible true (goalAt 242) 6 state242_19.toFinset :=
  node_ok cuts242 [⟨state242_13,exclude242_13⟩,⟨state242_16,exclude242_16⟩,⟨state242_18,exclude242_18⟩] 0x40010c04218080c04240011000630208c08240010c04230208c08240011000418080602040015000518080602040018222030208c08240015000530208c08240018222018080222040018602028208a08240020c08218908c08240014602018908624240020c08228208a08240011000418908624240010c04228208a08240012000128208a08240010c04218908624240024222018100604040020121028208a08240024222028208a0824002012101810060424001850102420890824001cc08214908c0824001450101490852424001cc0822420890824002030102420890824001ca0820c080a0828000830100c08030204001ca08224208908240011000414908524240010c04224208908240012000024208908240010c0421490852424002412101410050404001c22202420890824002412102420890824001c222014100504240001000040000c040 (by decide +kernel)

def state242_20 : List Sig := [0xffffffffffffffff3333333333330000,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_20 : Impossible true (goalAt 242) 3 state242_20.toFinset :=
  node_ok cuts242 [] 0x28208c08218108a08224208a0820c080908224208c08214108908218108a08218108a08214108908214108908208880c08230108c082 (by decide +kernel)

def state242_21 : List Sig := [0xffffffffffffffff3333333333330000ffffffffffffffff3333333333330000,input 6,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_21 : Impossible true (goalAt 242) 4 state242_21.toFinset :=
  node_ok cuts242 [⟨state242_20,exclude242_20⟩] 0x604228a08a28218108a28218108604228a08a08228208604228a08504224a08928214108928228a08302024a08928214108504224a08908224208504224a08c04228080c04218080c0823010a0000301082220 (by decide +kernel)

def state242_22 : List Sig := [0xffffffffffffffff00000000000000003333333333330000,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_22 : Impossible true (goalAt 242) 3 state242_22.toFinset :=
  node_ok cuts242 [] 0x18108a08228208604224208a0820c080908214108908224208504228208604228208c08224208504224208c08208880c08230208c042 (by decide +kernel)

def state242_23 : List Sig := [0xffffffffffffffffffffffffffffffff33333333333300003333333333330000,input 7,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_23 : Impossible true (goalAt 242) 4 state242_23.toFinset :=
  node_ok cuts242 [⟨state242_22,exclude242_22⟩] 0x602030208c08218082000030208c08208880a08230208624228208624228208a08218908604228208a08218908908230208524224208908228208302024208524224208908214908504224208908214908c042 (by decide +kernel)

def state242_24 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_24 : Impossible true (goalAt 242) 5 state242_24.toFinset :=
  node_ok cuts242 [⟨state242_7,exclude242_7⟩,⟨state242_17,exclude242_17⟩,⟨state242_21,exclude242_21⟩,⟨state242_23,exclude242_23⟩] 0x30108602030108a02030208c08230108c08230208a02018080602028080624218908c04228a08a28228080a28228a08c04218908624218080a28228a08c08218908c08218080624218908c08228a08a28224040524214908c04224a08928224040928224a08c04214908524214040928224a08c08214908c08214040524214908c08224a0892820c040928224a08a2820c080a2820c04030200c080a28224a08928228080222008880c04280004c04228082000328080c04208880c04218080222008880c08280000c08218082000218080c08208880c0820c040121028208a28208880a0820c040222008880a28204840a2820c08022202420892820484090820c08012100c0809282088809282 (by decide +kernel)

def state242_25 : List Sig := [0xffffffffffffffffffffffffffff0000,input 6,input 4,input 5,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_25 : Impossible true (goalAt 242) 4 state242_25.toFinset :=
  node_ok cuts242 [] 0x28a08a08028208a08224a08908024208908230a08c08030208c08228a08c28218908a28224a08a2820c080928224a08c28214908928230108c04230908c04018908a28218908a28214908928214908928218080c28230908c282 (by decide +kernel)

def state242_26 : List Sig := [0x3333333333333333333333333333000033333333333333333333333333330000,input 6,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_26 : Impossible true (goalAt 242) 4 state242_26.toFinset :=
  node_ok cuts242 [] 0x18908a28228a08624228a08c28218908a28214908928224a08524224a08a2820c080928224a08c28214908928230908c28230a08602030108c04230100c24228208a08218100a28224208908214100928230208c08218080c282 (by decide +kernel)

def state242_27 : List Sig := [0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000,input 6,input 4,input 5,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_27 : Impossible true (goalAt 242) 5 state242_27.toFinset :=
  node_ok cuts242 [⟨state242_1,exclude242_1⟩,⟨state242_25,exclude242_25⟩,⟨state242_26,exclude242_26⟩] 0xc24230100c04230108624218100604218108524214100504214108222018082000008882000208880222040000624230908a02018908602018908624208908a28214908c2422404052421490862420c08052420c080524214908302024a08c24228080c24218080c2823090a0001309090004 (by decide +kernel)

def state242_28 : List Sig := [0xffffffffffff00000000000000000000ffffffffffff0000,input 6,input 4,input 5,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_28 : Impossible true (goalAt 242) 5 state242_28.toFinset :=
  node_ok cuts242 [⟨state242_7,exclude242_7⟩] 0xc24230100c04230108624218100604218108524214100504214108c28230200c08230208624230908a02018908e28230a08624230a08524230908901014908524218908302014908d28230a08524230a08c24230a08c28228080a02030908a02030908222080000222040000a28228a08301018908928224a083020149086020 (by decide +kernel)

def state242_29 : List Sig := [0x3333333333333333333333333333333333333333333300003333333333330000,input 7,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_29 : Impossible true (goalAt 242) 4 state242_29.toFinset :=
  node_ok cuts242 [] 0x30908c28230a08602028a08c28218908a28218908a28228a08624224a08c28214908928224a08a2820c080928214908928224a08524230208c08230200c28228208a08228200a28224208908224200928230108c04228080c242 (by decide +kernel)

def state242_30 : List Sig := [0xffffffffffffffff0000000000000000ffffffffffff0000,input 7,input 4,input 5,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_30 : Impossible true (goalAt 242) 4 state242_30.toFinset :=
  node_ok cuts242 [] 0x28a08a08028208a08224a08908024208908230908c04030108c04218908a28228a08624224a08a2820c080928214908928224a08524230208c08230a08c08028a08624228a08c28224a08524224a08c28218080c28230a08c242 (by decide +kernel)

def state242_31 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_31 : Impossible true (goalAt 242) 5 state242_31.toFinset :=
  node_ok cuts242 [⟨state242_11,exclude242_11⟩,⟨state242_29,exclude242_29⟩,⟨state242_30,exclude242_30⟩] 0x602030a08c28218082000230a08c2824000cc28230200c08230208a28228200a08228208928224200908224208222028082000008882000108880222040000a28230a08602028a08a02028a08a28208a08624224a08c28214040928224a08a2820c08092820c080928224a08302014908c242 (by decide +kernel)

def state242_32 : List Sig := [0xffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_32 : Impossible true (goalAt 242) 5 state242_32.toFinset :=
  node_ok cuts242 [⟨state242_17,exclude242_17⟩] 0xc24230a08c28218080c28230200c08230208a28228200a08228208928224200908224208c24230100c04230108a28230a08602028a08e24228a08a28230908928230a08501024a08928228a08302024a08d24224a08928230908602030a08602030a08222080000222040000624228a08301028a08524224a08302024a08a020 (by decide +kernel)

def state242_33 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_33 : Impossible true (goalAt 242) 4 state242_33.toFinset :=
  node_ok cuts242 [] 0x30908c04030108c04214908504014108504208880302004840222004840222008880121014908b24228080524224a08928214908224228a08a28214908124230908a02030908302030a08c2820c0810001309089010309083010 (by decide +kernel)

def state242_34 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_34 : Impossible true (goalAt 242) 5 state242_34.toFinset :=
  node_ok cuts242 [⟨state242_0,exclude242_0⟩,⟨state242_33,exclude242_33⟩] 0x30908c04030108c04204840222008880121014908504014108504208880501080000222008880302004840222028080c24228080c24228a0830101404200010c04030200c040302040008524230908a02014908501014908524204908928224a08524240008c24228080c24228080c28230908a020309083020 (by decide +kernel)

def state242_35 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_35 : Impossible true (goalAt 242) 4 state242_35.toFinset :=
  node_ok cuts242 [] 0x18080c28230a08302014040c28230a08301030a08c08030208c08224a08908024208908208880302004840222004840222008880121024a08c28218080928214908928224a08228218908928224a08128230908c2420c0810001 (by decide +kernel)

def state242_36 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_36 : Impossible true (goalAt 242) 5 state242_36.toFinset :=
  node_ok cuts242 [⟨state242_10,exclude242_10⟩,⟨state242_35,exclude242_35⟩] 0x18080c28230a08602018080c28230a08302030a08c08030208c08204840222008880121024a08908024208908208880901080000222008880302004840222018080c28218080c28228a0830102404200010c04030200c040302040008928230a08602024a08901024a08928204a08524224a08928240008c242 (by decide +kernel)

def state242_37 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_37 : Impossible true (goalAt 242) 5 state242_37.toFinset :=
  node_ok cuts242 [⟨state242_33,exclude242_33⟩,⟨state242_5,exclude242_5⟩] 0x30908c04030108c0420888030200484022201890860401810860420888060208000422200484022200888012100c080c24224040c24224a0830201408200000c08030100c080302040004624230908a02018908602018908624208908a28228a08624240004c24228080c24218080c282309089010309083010 (by decide +kernel)

def state242_38 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_38 : Impossible true (goalAt 242) 5 state242_38.toFinset :=
  node_ok cuts242 [⟨state242_35,exclude242_35⟩,⟨state242_15,exclude242_15⟩] 0x18080c28230a08602014040c28230a08301030a08c08030208c08208880302004840222028a08a08028208a08208880a0208000422200484022200888012100c080c28214040c28224a0830202408200000c08030100c080302040004a28230a08602028a08a02028a08a28208a08624228a08a28240004c242 (by decide +kernel)

def state242_39 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_39 : Impossible true (goalAt 242) 5 state242_39.toFinset :=
  node_ok cuts242 [] 0x30108c08230208602028080c04228080c04218080c08218080c08228a0830203010890103010830203020850103020830100c081000724a08a02030108a02030108602030208602030208222030108a020301082220302086020302081210088802220048402220048403020088810000 (by decide +kernel)

def state242_40 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_40 : Impossible true (goalAt 242) 6 state242_40.toFinset :=
  node_ok cuts242 [⟨state242_8,exclude242_8⟩,⟨state242_18,exclude242_18⟩,⟨state242_24,exclude242_24⟩,⟨state242_27,exclude242_27⟩,⟨state242_28,exclude242_28⟩,⟨state242_31,exclude242_31⟩,⟨state242_32,exclude242_32⟩,⟨state242_34,exclude242_34⟩,⟨state242_36,exclude242_36⟩,⟨state242_37,exclude242_37⟩,⟨state242_38,exclude242_38⟩,⟨state242_39,exclude242_39⟩] 0xc24218080c24228080c28230a08c24230a08c28228080602018080c24208880c24230101000730100c24280004c04230100222030108c28208880c28230201000730200c28280000c0823020022203020900020484012100c04022200888100070888022200c04012100484100010888022200c08012100c08100070484012100c08022200888100078002e000240000222008881000708880222040001000740000a0200c040a02030909000230908a02080028a0203090830103090860200c040602030a09000230a08602080024602030a08301030a09000140004a2822404030200c080c24240004c24224042000824040c2420c080c2421404030200c080c28240004c28214042000714040c2820c080c2820c04100020c04100010c080302040005000140005000140008928228081000428080c24280018c24228082000528080c24240010c24218081000318080c28280010c28218082000318080c2824000cc282 (by decide +kernel)

def state242_41 : List Sig := [0xffffffff00000000ffff000000000000ffffffff00000000ffff0000,input 5,input 4,input 6,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_41 : Impossible true (goalAt 242) 5 state242_41.toFinset :=
  node_ok cuts242 [⟨state242_2,exclude242_2⟩] 0xc24230100c04230108222018082000008880524214100504214108a28228200a08228208c24228080c2421808052423090890101490830201490852420c080b28228a08302028a08a02028a08a28230908a28238a08602028a08c24228080c24228080121008880121008880c28230a08501018080928224a0852420c0806242 (by decide +kernel)

def state242_42 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_42 : Impossible true (goalAt 242) 5 state242_42.toFinset :=
  node_ok cuts242 [⟨state242_33,exclude242_33⟩] 0x30908c04030108c04214908504014108504208880602004840222018908604018108604204840222008880121014908c24224040524224a0852421890a000014908501014908524204908c24228080c24218080c28230a08602040004624230908a02018908602018908624208908a282309089010309085010 (by decide +kernel)

def state242_43 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 1,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_43 : Impossible true (goalAt 242) 6 state242_43.toFinset :=
  node_ok cuts242 [⟨state242_34,exclude242_34⟩,⟨state242_3,exclude242_3⟩,⟨state242_27,exclude242_27⟩,⟨state242_41,exclude242_41⟩,⟨state242_42,exclude242_42⟩] 0xa02018908624230908a28228a08a02028a08a28230908624218909000328a08a2821404062421890a000418908624214040a28228a0a000328a08a2824000862421890a000218908624240008a28228a08c24208880c24230101000730100c24240014c04230100222030108a28204840a28228200222028200a28208880a0822820012102820900030888022201404100031404100074000e000114040222008880524208880524214100121014100524204840504214100222014109000708880222040000121004841000704840121040000222008880c24214040c24228081000328080c24240014c24228080501028081000140004c28224040524214908c24240004c24224041000524040c2421490852420c040524214908a28240004a2820c04200000c040a28214908a2821404100031404100011490852424000500010490900014000c928230909000430908a02040014a02030909000530908a02040010a020 (by decide +kernel)

def state242_44 : List Sig := [0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,input 5,input 4,input 7,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_44 : Impossible true (goalAt 242) 5 state242_44.toFinset :=
  node_ok cuts242 [⟨state242_12,exclude242_12⟩] 0x602030a08c28218080c28230200c08230208222028082000008880928224200908224208624218100604218108928230a08501024a08302024a0892820c080928218908302024a08602030a08624230a08624238908a02018908c28218080c28218080121008880121008880c2423090890102808092821490892820c080a282 (by decide +kernel)

def state242_45 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_45 : Impossible true (goalAt 242) 5 state242_45.toFinset :=
  node_ok cuts242 [⟨state242_35,exclude242_35⟩] 0x18080c28230a08602014040c28230a08501030a08c08030208c08224a08908024208908208880a02004840222028a08a08028208a08204840222008880121024a08c28214040928214908928228a0a000024a08901024a08928204a08c24230908a02040004a28230a08602028a08a02028a08a28208a086242 (by decide +kernel)

def state242_46 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_46 : Impossible true (goalAt 242) 6 state242_46.toFinset :=
  node_ok cuts242 [⟨state242_36,exclude242_36⟩,⟨state242_13,exclude242_13⟩,⟨state242_31,exclude242_31⟩,⟨state242_44,exclude242_44⟩,⟨state242_45,exclude242_45⟩] 0x1000418080602024040c28230a09000530a08c2822404060201808100051808060204000cc28230a09000530a08c2824000c602018080602028a08a28230a08624230a08602018908624230a08a28228a09000418908624224040a28228a0a000428a08a2822404062421890a000318908624240008a28228a0a000228a08a28240008624218908c28208880c28230201000730200c28240014c08230200222030208a28204840a28228200222028200a28208880a08228200121028209000408880222024041000424041000740012000124040222008880928208880928224200121024200928204840908224200222024209000708880222040000121004841000704840121040000222008881000140004c24214040928224a08c28240004c28214041000514040c28224a0892820c040928224a08a28240004a2820c04200000c040a28224a08928224041000424041000124a08928240005000104a090001400105242 (by decide +kernel)

def state242_47 : List Sig := [0xffff0000ffff0000ffff000000000000ffff0000ffff0000ffff00000000,input 4,input 5,input 6,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_47 : Impossible true (goalAt 242) 5 state242_47.toFinset :=
  node_ok cuts242 [⟨state242_4,exclude242_4⟩] 0xc24230100c04230108222018082000008880624218100604218108928224200908224208c24228080c24218080624230908a02018908602018908624208908901024a08928230908928234a08501024a0892822ca08301024a08c24224040c24224040222004840222004840c28230a08602014040a28228a0862420c0405242 (by decide +kernel)

def state242_48 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_48 : Impossible true (goalAt 242) 6 state242_48.toFinset :=
  node_ok cuts242 [⟨state242_6,exclude242_6⟩,⟨state242_27,exclude242_27⟩,⟨state242_37,exclude242_37⟩,⟨state242_42,exclude242_42⟩,⟨state242_47,exclude242_47⟩] 0x901014908524230908928224a08901024a08928230908524214909000324a0892821808052421490a000314908524218080928224a09000224a0892821890830201890a00020c080302018908928224a0a000424a0892824000452421490a000114908524240004928224a08c24208880c24230101000830100c24240014c0423010022203010892820888092822420012102420092820484090822420022202420900030888022201808100031808100084000e000018080222008880624204840624218100222018100624208880604218100121018109000804840121040000222008881000808880222040000121004840c24218080c24228081000328080c24240014c24228080602018081000240008c28228080624218908c24240008c24228081000528080c2421890862421808100031808100021890862424000900020890900024000ca282309090004309089010400149010309090005309089010400109010 (by decide +kernel)

def state242_49 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000,input 4,input 5,input 7,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_49 : Impossible true (goalAt 242) 5 state242_49.toFinset :=
  node_ok cuts242 [⟨state242_14,exclude242_14⟩] 0x602030a08c28218080c28230200c08230208222028082000008880a28228200a08228208524214100504214108a28230a08602028a08a02028a08a28208a08501030a08524230a08524234908901014908524228a08301028a08c28214040c28214040222004840222004840c24230908a02024040a28218908a2820c0409282 (by decide +kernel)

def state242_50 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_50 : Impossible true (goalAt 242) 6 state242_50.toFinset :=
  node_ok cuts242 [⟨state242_16,exclude242_16⟩,⟨state242_31,exclude242_31⟩,⟨state242_38,exclude242_38⟩,⟨state242_45,exclude242_45⟩,⟨state242_49,exclude242_49⟩] 0x1000418080602028080c28230a09000530a08c2822808060201808100051404050104000cc28230a09000530a08c2824000c501014040501024a08928230a08524230a08501014908524230a08928224a09000414908524228080928224a0a000324a08928228080524214909000224a08928228a08302028a0a00020c080302028a08928224a0a000414908524240004928224a0a000124a08928240004524214908c28208880c28230201000830200c28240014c08230200222030208928208880928224200121024200928204840908224200222024209000408880222028081000428081000840012000028080222008880a28204840a28228200222028200a28208880a08228200121028209000804840121040000222008881000808880222040000121004841000240008c24218080a28228a08c28240008c28218081000518080c28228a08a28228081000428081000228a08a28240009000208a090002400106242 (by decide +kernel)

def state242_51 : List Sig := roots 242
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_51 : Impossible true (goalAt 242) 7 state242_51.toFinset :=
  node_ok cuts242 [⟨state242_9,exclude242_9⟩,⟨state242_19,exclude242_19⟩,⟨state242_40,exclude242_40⟩,⟨state242_43,exclude242_43⟩,⟨state242_46,exclude242_46⟩,⟨state242_48,exclude242_48⟩,⟨state242_50,exclude242_50⟩] 0x40010c24218080c2424000ca02030a08c28240014c24230a08c2824000ca02018080602040010a02018908624240008c24228a08a28280018a02028a08a28240008c2421890862424000c602028a08a28240008c28218908c28280014602018908624240008c28228a08a28240010901014908524240004c24224a08928280010901024a08928240004c2421490852424000c501024a08928240004c28214908c2828000c501014908524240004c28224a08928240008301024a08928240004a2820c080a2828000830100c080302040004a28224a08928240000c24208880c24240000c04040000c04040000c24280004c04240000c04008880c04240000c28208880c28240000c08040000c08040000c28280000c08240000c08008880c08240000a28204840a28240000a08008880a08040000a28208880a08240000a08004840a082400009282088809282400009080048409080400009282048409082400009080088809082 (by decide +kernel)

theorem lower242 : Claim 242 8 :=
  fromSearch 1141964864 (by decide +kernel) exclude242_51

def rule177_0 : {c : Cut // CutGood (goalAt 177) c} :=
  ruleFor 177 lower176 none (by decide +kernel)

def rule177_1 : {c : Cut // CutGood (goalAt 177) c} :=
  ruleFor 177 lower161 none (by decide +kernel)

def rule177_2 : {c : Cut // CutGood (goalAt 177) c} :=
  ruleFor 177 lower145 none (by decide +kernel)

def cuts177 : Cuts (goalAt 177) := [rule177_0,rule177_1,rule177_2]

def state177_0 : List Sig := roots 177
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude177_0 : Impossible true (goalAt 177) 5 state177_0.toFinset :=
  node_ok cuts177 [] 0x40008a0200c040a02040008901028200a08040008a02028200a0804000890100c04030104000490100c080302040004a02024200908040004901024200908040004a0200c080302040004301024200908040004a0800c080a0804000430100c080302040004a08024200908040000810108480212040000a02020600818040000810120600818040000a02008480212040000210120600818040000a08008480a08040000210108480212040000a080206008180400001101206008180400009080044409080400001101044401110400009080206008180 (by decide +kernel)

theorem lower177 : Claim 177 6 :=
  fromSearch 4 (by decide +kernel) exclude177_0

theorem lower163 : Claim 163 5 :=
  fromLift 5 2 85 lower161 (by decide +kernel)

theorem lower147 : Claim 147 5 :=
  fromLift 5 2 68 lower145 (by decide +kernel)

theorem lower51 : Claim 51 5 :=
  fromLift 5 1 68 lower50 (by decide +kernel)

def cuts49 : Cuts (goalAt 49) := []

def state49_0 : List Sig := roots 49
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude49_0 : Impossible true (goalAt 49) 3 state49_0.toFinset :=
  node_ok cuts49 [] 0xc04011010c04021010c08030200c04030200c0802101044041101084041110044403010084802120084042120084803010044401110044042120084803020044403020044041110044403020084802120 (by decide +kernel)

theorem lower49 : Claim 49 4 :=
  fromSearch 4 (by decide +kernel) exclude49_0

def rule179_0 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower177 none (by decide +kernel)

def rule179_1 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower163 none (by decide +kernel)

def rule179_2 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower178 none (by decide +kernel)

def rule179_3 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower147 none (by decide +kernel)

def rule179_4 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower50 none (by decide +kernel)

def rule179_5 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower51 none (by decide +kernel)

def rule179_6 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower176 none (by decide +kernel)

def rule179_7 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower49 none (by decide +kernel)

def rule179_8 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower161 none (by decide +kernel)

def rule179_9 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower145 none (by decide +kernel)

def cuts179 : Cuts (goalAt 179) := [rule179_0,rule179_1,rule179_2,rule179_3,rule179_4,rule179_5,rule179_6,rule179_7,rule179_8,rule179_9]

def state179_0 : List Sig := [0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaa,input 5,input 4,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_0 : Impossible true (goalAt 179) 4 state179_0.toFinset :=
  node_ok cuts179 [] 0x8480a0202040c212008480302004440212004440212008480111020e08818020e0900000c080a0202404030200c04030200c080110324608a02024040a0200c040a18228080838220e090007 (by decide +kernel)

def state179_1 : List Sig := [0xffffaaaa00000000ffffaaaa00000000ffffaaaa00000000ffffaaaa,input 5,input 4,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_1 : Impossible true (goalAt 179) 4 state179_1.toFinset :=
  node_ok cuts179 [] 0x21202808081030848021200c080111008480a18228200a0822820830202808090100c080b18228608302028608a02028608a18208e08901020e08838228080818020e08838208480838224608110320e083010 (by decide +kernel)

def state179_2 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_2 : Impossible true (goalAt 179) 4 state179_2.toFinset :=
  node_ok cuts179 [] 0x222028080810308880838220600838208880111008880222004440110308880222040018302020e0883820c08083820c080302020e08838224608302020e08a02024040a0200c040a282280808103280801103 (by decide +kernel)

def state179_3 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 4,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_3 : Impossible true (goalAt 179) 5 state179_3.toFinset :=
  node_ok cuts179 [⟨state179_0,exclude179_0⟩,⟨state179_1,exclude179_1⟩,⟨state179_2,exclude179_2⟩] 0xa0200c040a02024040a28228a08a02028a08a28224040301008a08810308880222028081000628080810340010810328080222008880a28204440a28228200222028200a28208880a0822820011102820811030888022204001811100444011030444011104001822200888083820888083824000011102060083820444083824000022200888090100440c90102808100082808090104001090102808011032808030100440c301028a09000828a08301080008301028a08110328a09000240008918224041000724040a02020e08838224040838220e08a0204001ca0200c040838220e08a28280004a1820c04200000c040a28220e088382 (by decide +kernel)

def state179_4 : List Sig := [0xffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa,input 4,input 5,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_4 : Impossible true (goalAt 179) 4 state179_4.toFinset :=
  node_ok cuts179 [] 0x212028080810308480111008480212004440918224200908224208a02024040a0200c04090102460891822808091822c608301024608a02020e08838224040818020e08838204440838228608210320e083020 (by decide +kernel)

def state179_5 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_5 : Impossible true (goalAt 179) 4 state179_5.toFinset :=
  node_ok cuts179 [] 0x21202808081030848083822060083820484021200c080121008480210308480212040018a02020e0883820c040838228608301020e0830202808090100c080301020e08302020e089282280808103280802103 (by decide +kernel)

def state179_6 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 5,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_6 : Impossible true (goalAt 179) 5 state179_6.toFinset :=
  node_ok cuts179 [⟨state179_0,exclude179_0⟩,⟨state179_4,exclude179_4⟩,⟨state179_5,exclude179_5⟩] 0x90100c080302028080928224a08901024a0892822808030200c081000924a0892820840c30200c08200020c08030200840c928224a0a000124a08918220e08302020e0a00000c080302020e08928220e08810308480212028081000628080810340010810328080212008480928208480928224200121024200928204840908224200212024208210304840121040018212008480210308480212040018121004840838204840838240000212020600838208480838240000121004840a0200840ca02024041000424040a02040010a02024040210324041000240008a18228081000728080901020e08838228080838220e0890104001c9010 (by decide +kernel)

def state179_7 : List Sig := [0x1111111111110000111111111111000011111111111100001111111111110000,input 4,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_7 : Impossible true (goalAt 179) 4 state179_7.toFinset :=
  node_ok cuts179 [] 0x810320e08838228080838228608210320e08838224608110320e08a02028a08a28208a00302024a0892820c080928228a08302024a0822202040ca02008880212028208a08208880a2822420890820c0809282 (by decide +kernel)

def state179_8 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_8 : Impossible true (goalAt 179) 5 state179_8.toFinset :=
  node_ok cuts179 [⟨state179_0,exclude179_0⟩,⟨state179_2,exclude179_2⟩,⟨state179_5,exclude179_5⟩,⟨state179_7,exclude179_7⟩] 0x2040c838220e08a0202060083820c042000220e0883820c082000120e0883824000a000020e0822202808081030888012100888022200484022200c080121008882000308880222040018a02024040a0200c040a2820c080a0202404030200c0403020400209282280808103280808103 (by decide +kernel)

def state179_9 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_9 : Impossible true (goalAt 179) 6 state179_9.toFinset :=
  node_ok cuts179 [⟨state179_3,exclude179_3⟩,⟨state179_6,exclude179_6⟩,⟨state179_8,exclude179_8⟩] 0x4001ca0200c040a02040010901028a08a28240010a02028a08a2824001c90100c04022824001c90100c080302040020a02024a08928240010901024a0892824001ca0200c080302040024301024a08928240020a2820c080a2828000830100c080302040020a28224a0892824000881034001c810340008a02020e08838240008810320e08838240008a02040008a02040008210320e08838240008a28240008a18240008210380004210340008a28220e08838240008110320e08838240008928240008918240008110380000110340008928220e08838240001000040000818040018810308880222040018a02040018a02040018810340010810340018a02008880222040018a28204840a28240018a08008880a08040018a28208880a08240018a08004840a082400189282088809282400189080048409080400189282048409082400189080088809082 (by decide +kernel)

def state179_10 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_10 : Impossible true (goalAt 179) 4 state179_10.toFinset :=
  node_ok cuts179 [] 0x212020e08838208480212020e08838208480838208480212020e08838224208212020e0822200c08012100888022200484022200484030200c04030202040ca0820888090822420900070c0809082242088103 (by decide +kernel)

def state179_11 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 5,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_11 : Impossible true (goalAt 179) 4 state179_11.toFinset :=
  node_ok cuts179 [] 0x8480838220e08212020e08908204440838220e08a0820848083822040c838220e0900062040c22200888100000c080908224208222024208a0820c080908204c0c222028208a082048402303 (by decide +kernel)

def state179_12 : List Sig := [0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,input 5,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_12 : Impossible true (goalAt 179) 4 state179_12.toFinset :=
  node_ok cuts179 [] 0x212020e08838208480838224208111020e08838208480212020e0830202420890820888090820c08030202420822200484022200484083820848083820848012100888012100888090820c08090820c080a082 (by decide +kernel)

def state179_13 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_13 : Impossible true (goalAt 179) 5 state179_13.toFinset :=
  node_ok cuts179 [⟨state179_10,exclude179_10⟩,⟨state179_11,exclude179_11⟩,⟨state179_12,exclude179_12⟩] 0x22200c040222004840a08228208222028208a08204840301004842000208c0c23032040ca0822820a000128208a0822040c230308a00230320e08838228208212028208230308480212028208838220e09000708480212008880838220e09000420e08838208880212008481000820e08838224208111024209000404440111024208838220e08810308480212040018838220e08810320e0883824001821200848081030888022204000012102808081030484012104000022200888030102420890822820900082820830108000030102820890822420812104001c1210088809082242081210242089082088810007088810005400143020 (by decide +kernel)

def state179_14 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000,input 4,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_14 : Impossible true (goalAt 179) 4 state179_14.toFinset :=
  node_ok cuts179 [] 0x212020e08838208480838228208212020e08838204440111020e08222028208a08204840121008880121008880301028208301028208838204440838204440222004840222004840a0820c040a0820c0409082 (by decide +kernel)

def state179_15 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_15 : Impossible true (goalAt 179) 4 state179_15.toFinset :=
  node_ok cuts179 [] 0x212020e08838208480111020e0883820444083820c080111020e08838228208212020e0812100888022200484030200888012100888030100c08030202040c908208880a0822820900070c040a082282088103 (by decide +kernel)

def state179_16 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_16 : Impossible true (goalAt 179) 5 state179_16.toFinset :=
  node_ok cuts179 [⟨state179_11,exclude179_11⟩,⟨state179_14,exclude179_14⟩,⟨state179_15,exclude179_15⟩] 0x12100c08030200888090822420812102420890820888030200888100092420890822820830202820a00020c08030202820890822420a000104c0c13032040c90822420a00002420890822040c130304a00130320e08838224208111024208130304440111024208838220e09000708480212008880838220e09000420e08838208880212008481000420e08838228208212028209000408480212028208838220e08810304440111040018838220e08810320e0883824001811100444081030484012104000022200888081030888022204000012100484022204001c222004840a08228208222028208a082048410007048410005400143010 (by decide +kernel)

def state179_17 : List Sig := [0x33333333333300003333333333330000,input 4,input 5,input 7,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_17 : Impossible true (goalAt 179) 4 state179_17.toFinset :=
  node_ok cuts179 [] 0x212020e08838208480838228208212020e08838224208111020e08301028208a08208a0030202420890820c080908228208302024208212020e08212020e08a02004840a08208880a0820888090820c0809082 (by decide +kernel)

def state179_18 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_18 : Impossible true (goalAt 179) 5 state179_18.toFinset :=
  node_ok cuts179 [⟨state179_11,exclude179_11⟩,⟨state179_10,exclude179_10⟩,⟨state179_15,exclude179_15⟩,⟨state179_17,exclude179_17⟩] 0x8480838220e08212008480838220e08212020e08212008480838220e08302004440838220e0821200848083822808030102040e00020c040222004840222004840a0820c08081038000430200c08022200484022200c0403020400209082400148103800008103088820003088810007 (by decide +kernel)

def state179_19 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_19 : Impossible true (goalAt 179) 6 state179_19.toFinset :=
  node_ok cuts179 [⟨state179_13,exclude179_13⟩,⟨state179_16,exclude179_16⟩,⟨state179_18,exclude179_18⟩] 0x4001500050c040301040014810328208a08240016000128208a0824001481030c04022804001c22200c04022204001c121028208a0824001c222028208a0824001c12100c040121040024301024208908240020a0820c080a0828000830100c080302040020a0822420890824001500050c08030204001481032420890824001600002420890824001481030c08030204001c12100c08030204001c22202420890824001c12102420890824001c22200c080222040010230320e08838240018a08208480a08240010230308480212040018a08220e08838240020130320e08838240018908204440908240010130304440111040018908220e08838240014810308480212040015000620e08838240014810320e0883824001500050848021204001d000708480212040018222020e0883824001d000420e08838240018222008480212040001000040000a020 (by decide +kernel)

def state179_20 : List Sig := [0xffffffffffffaaaaffffffffffffaaaa,input 5,input 0,input 4,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_20 : Impossible true (goalAt 179) 4 state179_20.toFinset :=
  node_ok cuts179 [] 0x24a08908024208908228a08a08028208a08224a08a2820c080928220600838220e08818220e08928204440838220e08a28208480838208880810308880a0200c08092820c080928208480838208480838208a08a28228080a282 (by decide +kernel)

def state179_21 : List Sig := [0x3333333333332222333333333333222233333333333322223333333333332222,input 5,input 0,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_21 : Impossible true (goalAt 179) 4 state179_21.toFinset :=
  node_ok cuts179 [] 0xc080928224a08302024a08a2820c080928208480838220e08212020e08928204440838220e08a28208480838228080a28228a0822800888081032808022202420890820c080928220608838208480838228208a08208880a282 (by decide +kernel)

def state179_22 : List Sig := [0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaa,input 5,input 0,input 4,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_22 : Impossible true (goalAt 179) 5 state179_22.toFinset :=
  node_ok cuts179 [⟨state179_0,exclude179_0⟩,⟨state179_20,exclude179_20⟩,⟨state179_21,exclude179_21⟩] 0x22202808081030888022200c08012100888012100888022200484200020888022204000030202808090100c08030100c080302004c0c928208480a02020c0c212008480222080000212008480302004440212004440212008480111020e08a02024040a0200c040a282280820001280810005 (by decide +kernel)

def state179_23 : List Sig := [0xffffaaaa00000000ffffaaaa00000000ffffaaaa00000000ffffaaaa,input 5,input 0,input 4,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_23 : Impossible true (goalAt 179) 5 state179_23.toFinset :=
  node_ok cuts179 [⟨state179_1,exclude179_1⟩] 0x22202808081030888022200c080121008880a28228200a0822820830202808090100c080b28228a08302028a0821202808083030848021200888200000848021200c080111008480a38228a08212028a08a02028a08a28208a08901028080901028080121008880121008880928224a0813030c080838220e081110084803010 (by decide +kernel)

def state179_24 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_24 : Impossible true (goalAt 179) 4 state179_24.toFinset :=
  node_ok cuts179 [] 0x8880a0202040c222008880212004840212004840222008880111004c0c222008880110308480912024040212020e08838208481000124a08928208480220328080901028080111028a08a282044401203280808303280801303 (by decide +kernel)

def state179_25 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 5,0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 4,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_25 : Impossible true (goalAt 179) 5 state179_25.toFinset :=
  node_ok cuts179 [⟨state179_24,exclude179_24⟩] 0x8880a0202040c222008880121004840222008880212004840212004840222008880121004840222008880111024040a02024040a02024a08130308c0e000004c0c111004c0c11100480c21202808090100848023030848021200880c838220e08212040004a02024040a02024040a282280809010280801110 (by decide +kernel)

def state179_26 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_26 : Impossible true (goalAt 179) 5 state179_26.toFinset :=
  node_ok cuts179 [⟨state179_24,exclude179_24⟩,⟨state179_2,exclude179_2⟩] 0x8880a0202040c222008880302004840222004840222008880121004c0c222008880110304440a02020c0ca02004440222080004222020e0811100844200000444013030444011100480c30202808090100c08030100c08030204000c928224a08302040008a02024040a0200c040a282280808303280801303 (by decide +kernel)

def state179_27 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 0,input 4,input 1,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_27 : Impossible true (goalAt 179) 6 state179_27.toFinset :=
  node_ok cuts179 [⟨state179_3,exclude179_3⟩,⟨state179_22,exclude179_22⟩,⟨state179_23,exclude179_23⟩,⟨state179_25,exclude179_25⟩,⟨state179_26,exclude179_26⟩] 0xa0200c040a02024040a28228a08a02028a08a28224040301008a08830308880222028081000628080830340010810328080222008880a28204840a28228200222028200a28208880a08228200121028208130308880222004404121004840130304840121004404222008881000608880222040000121004841000604840121040000222008880901004c0c901028081000128080901040010901028080130328080301004c0c301028a09000128a08301080010301028a08130328a09000140008928220c0c111004440a02040008a02020c0d000420c0ca02004440a02008c0c111004440a28240008a28208c0e000308c0ca28204440a28240008111004440222040008222040009000680000222004440222004c0d000104c0d00020444011104000500010480d000140004838224041000524040a02040010a02024041000424040a02040014a0200c04100030c040a28280008a2820c04200010c040a2824000ca282 (by decide +kernel)

def state179_28 : List Sig := [0xffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa,input 4,input 0,input 5,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_28 : Impossible true (goalAt 179) 5 state179_28.toFinset :=
  node_ok cuts179 [⟨state179_4,exclude179_4⟩] 0x222028080810308880121008880222004840928224200908224208a02024040a0200c040212028080830308480212008882000008480111008480212004440938224a08111024a08901024a0892822808092822ca08301024a08a02024040a02024040222004840222004840a28228a0823030c040838220e082120044403020 (by decide +kernel)

def state179_29 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_29 : Impossible true (goalAt 179) 5 state179_29.toFinset :=
  node_ok cuts179 [⟨state179_24,exclude179_24⟩,⟨state179_5,exclude179_5⟩] 0x8880a0202040c222004840222008880121008880302004840222008c0c222008880210308480a02020c0c212008480222080004212020e0821200c08200000848023030848021200880ca02024040a0200c040a28228a0830104000430202808090100c08030100c0803020400049282280808303280802303 (by decide +kernel)

def state179_30 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 5,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_30 : Impossible true (goalAt 179) 6 state179_30.toFinset :=
  node_ok cuts179 [⟨state179_6,exclude179_6⟩,⟨state179_25,exclude179_25⟩,⟨state179_22,exclude179_22⟩,⟨state179_28,exclude179_28⟩,⟨state179_29,exclude179_29⟩] 0x90100c080302028080928224a08901024a0892822808030200c081000324a08928208c0c30200c08200040c080302008c0c928224a0a000324a0892824000430200c08200020c080302040004928224a08830308880222028081000628080830340010810328080222008880928208880928224200121024200928204840908224200222024208230304840121008404222008880230308880222008404121004841000604840121040000222008881000608880222040000121004840a02008c0ca02024041000324040a02040010a02024040230324041000240008a28220c0c212008480a02040008a02020c0d000420c0ca02008480212004c0c212008480928240008928204c0e000104c0c928208480928240008212008480222040008222040009000680000222008480212008c0d000308c0d00020848021204000900020880d00024000c8382280810005280809010400109010280810004280809010400149010 (by decide +kernel)

def state179_31 : List Sig := [0xbbbbbbbbbbbbaaaabbbbbbbbbbbbaaaa,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_31 : Impossible true (goalAt 179) 3 state179_31.toFinset :=
  node_ok cuts179 [] 0x24208a0820c080908220e08a08208480838220e08908204440838204840a08208880a0820888090820c0809082084808382084808382 (by decide +kernel)

def state179_32 : List Sig := [0xbbbbbbbbbbbbaaaabbbbbbbbbbbbaaaabbbbbbbbbbbbaaaabbbbbbbbbbbbaaaa,input 0,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_32 : Impossible true (goalAt 179) 4 state179_32.toFinset :=
  node_ok cuts179 [⟨state179_31,exclude179_31⟩] 0xa02028a08a28208a00302024a0892820c080928228a08302024a08212028080810308480111028a08212028a08212024a08111024a08838208882000028080222028208a08208880a2822420890820c0809282 (by decide +kernel)

def state179_33 : List Sig := [0x5555555555555555555555555555555511111111111100001111111111110000,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_33 : Impossible true (goalAt 179) 3 state179_33.toFinset :=
  node_ok cuts179 [] 0x28080a08228208301024208a0820c08090820c080908224208302020e08212028208838220e08111024208838208480838220e082120 (by decide +kernel)

def state179_34 : List Sig := [0xffffffffffffffffffffffffffffffff33333333333300003333333333330000,input 7,input 4,input 5,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_34 : Impossible true (goalAt 179) 4 state179_34.toFinset :=
  node_ok cuts179 [⟨state179_33,exclude179_33⟩] 0x838228208212020e08838224208111020e08212020e08838208482000020e08838208880a02028208a0820c040222028208a0820484090822820830202420830202420890820c0801210242089082088808103 (by decide +kernel)

def state179_35 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,input 4,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_35 : Impossible true (goalAt 179) 5 state179_35.toFinset :=
  node_ok cuts179 [⟨state179_7,exclude179_7⟩,⟨state179_17,exclude179_17⟩,⟨state179_32,exclude179_32⟩,⟨state179_34,exclude179_34⟩] 0x2040c212008480a02020e0883822040c838220e08a02008480212008c0c838220e08a28208480a28208c0c212008480a28220e08838204c0c838220e08928204440928204c0c111004440928220e08838228080301028080901028a08a28228080a28228a0890100c04022802404030200c080a02024a08928224040928224a08a0200c08030200c040928224a08a2820c080a2820c04030200c080a28224a0892822808022200888081038000481032808200032808081030888022200848022200848083828000083820848200020848083820888083820c040121028208a28208880a0820c040222008880a28204840a2820c08022202420892820484090820c08012100c0809282088809282 (by decide +kernel)

def state179_36 : List Sig := [0x5555555555555555555555555555555555555555555500005555555555550000,input 7,input 4,input 5,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_36 : Impossible true (goalAt 179) 4 state179_36.toFinset :=
  node_ok cuts179 [] 0x28a08a08028208a08224a08908024208908208880a0202040c222028080a28228a08228224a08a2820c08092820c080928224a08302020608838220e08818020e08212028a08838220e08111024a08838208480838220e082120 (by decide +kernel)

def state179_37 : List Sig := [0x3333333333333333333333333333333333333333333300003333333333330000,input 7,input 4,input 5,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_37 : Impossible true (goalAt 179) 4 state179_37.toFinset :=
  node_ok cuts179 [] 0x20e08a28208480838220e08928204440838208480838220e08212028080a28228a08228224a08a2820c08092820c080928224a08302020608838220600838228208a08228200a282242089082242009282088808103280802220 (by decide +kernel)

def state179_38 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_38 : Impossible true (goalAt 179) 5 state179_38.toFinset :=
  node_ok cuts179 [⟨state179_11,exclude179_11⟩,⟨state179_36,exclude179_36⟩,⟨state179_37,exclude179_37⟩] 0xa28228200a08228208928224200908224208222028082000008882000208880222040000818020e08838220608838228a08212020e08838224a08111020e08212020e08838208482000120e08838240008a02028a08a28208a08230324a08a2820c08092820c080928224a08302004c0c8303 (by decide +kernel)

def state179_39 : List Sig := [0xffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_39 : Impossible true (goalAt 179) 5 state179_39.toFinset :=
  node_ok cuts179 [⟨state179_17,exclude179_17⟩] 0xa28228200a08228208928224200908224208222020404810308880818020e08838220608838228a08212020e08838224a08111020e08212020e08838208480301028a08a2820c040928228a08302024a08302024a0892820c080222080000222040000212020e08212020e08301028a08301028a08302024a08302024a08a020 (by decide +kernel)

def state179_40 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_40 : Impossible true (goalAt 179) 4 state179_40.toFinset :=
  node_ok cuts179 [] 0x24a08908024208908208880302004840222004840222008880121020600838220e08818220e08928208480838208480838220e08212004440838220e0811100c080928224a0822820c040928224a0812820c04030200c0810001 (by decide +kernel)

def state179_41 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_41 : Impossible true (goalAt 179) 5 state179_41.toFinset :=
  node_ok cuts179 [⟨state179_10,exclude179_10⟩,⟨state179_40,exclude179_40⟩] 0x4840222008880121024a08908024208908208880901080000222008880302004840222020600838220e08818220e08212008480838220e08928208480838208480838220e08212008480838220e08212028a0830102404200010c04030200c04030204000c901024a08928204a08302024a0892824000ca020 (by decide +kernel)

def state179_42 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_42 : Impossible true (goalAt 179) 5 state179_42.toFinset :=
  node_ok cuts179 [⟨state179_40,exclude179_40⟩,⟨state179_15,exclude179_15⟩] 0x8880302004840222028a08a08028208a08208880a02080004222004840222008880121020600838220e08818220e08302004440838220e08a28208480838208480838220e08212004440838220e08111024a0830202408200000c08030100c080302040004a02028a08a28208a08301028a08a282400049010 (by decide +kernel)

def state179_43 : List Sig := [0x5555555555550000555555555555000055555555555500005555555555550000,input 0,input 4,input 5,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_43 : Impossible true (goalAt 179) 5 state179_43.toFinset :=
  node_ok cuts179 [⟨state179_7,exclude179_7⟩] 0x22202808081030888012100888022200484022200c080121008880a02024040a0200c04030202808090100c08030100c080302004c0c830320e08838228080818020e08838220608838228e08230320e08838224e08130320e08a02020c0ca02020c0c222080000222040000a28228a08301008c0c928224a08302004c0c2120 (by decide +kernel)

def state179_44 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_44 : Impossible true (goalAt 179) 5 state179_44.toFinset :=
  node_ok cuts179 [] 0x8480838220e08212020e08212008480838220e08302004440838220e08212008480838228080901028080301028a0830202808090100c08030100c081000824a08a0202040ca0202040c22202040ca02008880212020e08212020e081210088802220048402220048403020088810000 (by decide +kernel)

def state179_45 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_45 : Impossible true (goalAt 179) 6 state179_45.toFinset :=
  node_ok cuts179 [⟨state179_22,exclude179_22⟩,⟨state179_26,exclude179_26⟩,⟨state179_29,exclude179_29⟩,⟨state179_8,exclude179_8⟩,⟨state179_18,exclude179_18⟩,⟨state179_35,exclude179_35⟩,⟨state179_38,exclude179_38⟩,⟨state179_39,exclude179_39⟩,⟨state179_41,exclude179_41⟩,⟨state179_42,exclude179_42⟩,⟨state179_43,exclude179_43⟩,⟨state179_44,exclude179_44⟩] 0x83030888022202808100082808083038001081032808022200888100030484012100c04022200888100080888022200c04012100484100010888022200c08012100c08100080484012100c08022200888100088002e000540000222008881000808880222040001000840000830308480212028080838220e08830320e08838228080212008481000820600818008880838220e0a000320e08838208880818020609000320e0883820c04021200848200020848021200c040838220e09000120e0883820c08011100c08200010444011100c080838220e0a000a20e08838240008212008482000008480212040008838220e08a0200c040a02024041000324040a02080024a0202404030100c041000140004a2822404030200c080a02040004a02024042000824040a0200c08030200c04100030c04100010c08030204000500014000500014000c92822808100052808083038001c8303280820006280808303400148303 (by decide +kernel)

def state179_46 : List Sig := [0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,input 5,input 4,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_46 : Impossible true (goalAt 179) 5 state179_46.toFinset :=
  node_ok cuts179 [⟨state179_12,exclude179_12⟩] 0x222028082000008880928224200908224208121008880222004840818020e08838220608212020e08838208480838224a08111020e08838208480212020e08302024a0892820c08092820c080302024a08a02024040a0202404012100888012100888083820848083820848090102808090102808092820c08092820c080a282 (by decide +kernel)

def state179_47 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_47 : Impossible true (goalAt 179) 5 state179_47.toFinset :=
  node_ok cuts179 [⟨state179_40,exclude179_40⟩] 0x24a08908024208908208880a02004840222028a08a08028208a08204840222008880121020600838220e08818220e08928204440838208480838220e08212020e08a28208480838204440838220e0811100c080928228a0a000024a08901024a08928204a08901028080a02040004a02028a08a28208a083010 (by decide +kernel)

def state179_48 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_48 : Impossible true (goalAt 179) 6 state179_48.toFinset :=
  node_ok cuts179 [⟨state179_41,exclude179_41⟩,⟨state179_13,exclude179_13⟩,⟨state179_38,exclude179_38⟩,⟨state179_46,exclude179_46⟩,⟨state179_47,exclude179_47⟩] 0x100050c040301024040a28228a0a000428a08a2822404030100c042000308c0c23034000ca28228a0a000228a08a2824000c230308c0ca28204840a28228200222028200a28208880a08228200121028209000508880222024041000524041000740016000124040222008880928208880928224200121024200928204840908224200222024209000708880222040000121004841000704840121040000222008880230320e08838228a08212028a08230308480212028a08838220e09000720600818008880838220e09000420e08838208880818020609000508480212024040838220e09000420e08838224040212008481000120e08838224a08111024a09000404440111024a08838220e09000408480212040008838220e09000420e08838240008212008481000140004a0200c040928224a08a28240004a2820c04200000c040a28224a08928224041000524041000124a08928240005000104a090001400143020 (by decide +kernel)

def state179_49 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000,input 4,input 5,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_49 : Impossible true (goalAt 179) 5 state179_49.toFinset :=
  node_ok cuts179 [⟨state179_14,exclude179_14⟩] 0x222028082000008880a28228200a08228208222004840121008880818020e08838220608212020e08838208480838228a08212020e08838204440111020e08a02028a08a28208a08901028080901028080301028a08301028a08222004840222004840838204440838204440a02024040a02024040a2820c040a2820c0409282 (by decide +kernel)

def state179_50 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_50 : Impossible true (goalAt 179) 6 state179_50.toFinset :=
  node_ok cuts179 [⟨state179_16,exclude179_16⟩,⟨state179_38,exclude179_38⟩,⟨state179_42,exclude179_42⟩,⟨state179_47,exclude179_47⟩,⟨state179_49,exclude179_49⟩] 0x100050c080302028080928224a0a000324a0892822808030200c081000324a08928228a08302028a0a00020c080302028a08928224a0a000404c0c130340004928224a0a000124a08928240004130304c0c928208880928224200121024200928204840908224200222024209000508880222028081000528081000740016000028080222008880a28204840a28228200222028200a28208880a08228200121028209000704840121040000222008881000708880222040000121004840130320e08838224a08111024a08130304440111024a08838220e09000720600818008880838220e09000420e08838208880818020609000508480212028080838220e09000420e08838228080212008481000320e08838228a08212028a09000408480212028a08838220e09000404440111040008838220e09000420e0883824000811100444100034000c901028081000528081000328a08a2824000d000308a090003400143010 (by decide +kernel)

def state179_51 : List Sig := roots 179
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_51 : Impossible true (goalAt 179) 7 state179_51.toFinset :=
  node_ok cuts179 [⟨state179_9,exclude179_9⟩,⟨state179_19,exclude179_19⟩,⟨state179_27,exclude179_27⟩,⟨state179_30,exclude179_30⟩,⟨state179_45,exclude179_45⟩,⟨state179_48,exclude179_48⟩,⟨state179_50,exclude179_50⟩] 0x40014a0200c040a0204000c901028a08a28280018a02028a08a2824000c90100c04022824001490100c080302040004a02024a08928280014901024a08928240004a0200c08030204000c301024a08928240004a2820c080a2828001030100c080302040004a28224a08928240000830308880222040000a02040000a02040000830380004810340000a02008880222040000a28204840a28240000a08008880a08040000a28208880a08240000a08004840a08240000928208880928240000908004840908040000928204840908240000908008880908240014830308480212040008a02020e08838240010830320e08838240008a0200848021204000c230320e08838240008a28208480a2828000c230308480212040008a28220e08838240004130320e08838240008928204440928280008130304440111040004928220e08838240001000020600818040000222020e08838240002000020e088382400002220206008182 (by decide +kernel)

theorem lower179 : Claim 179 8 :=
  fromSearch 68 (by decide +kernel) exclude179_51

theorem lower99 : Claim 99 5 :=
  fromLift 5 2 85 lower97 (by decide +kernel)

theorem lower83 : Claim 83 5 :=
  fromLift 5 2 68 lower81 (by decide +kernel)

def rule115_0 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower113 none (by decide +kernel)

def rule115_1 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower99 none (by decide +kernel)

def rule115_2 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower114 none (by decide +kernel)

def rule115_3 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower83 none (by decide +kernel)

def rule115_4 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower50 none (by decide +kernel)

def rule115_5 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower51 none (by decide +kernel)

def rule115_6 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower112 none (by decide +kernel)

def rule115_7 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower49 none (by decide +kernel)

def rule115_8 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower97 none (by decide +kernel)

def rule115_9 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower81 none (by decide +kernel)

def cuts115 : Cuts (goalAt 115) := [rule115_0,rule115_1,rule115_2,rule115_3,rule115_4,rule115_5,rule115_6,rule115_7,rule115_8,rule115_9]

def state115_0 : List Sig := [0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaa,input 5,input 4,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_0 : Impossible true (goalAt 115) 4 state115_0.toFinset :=
  node_ok cuts115 [] 0x848060201040c212008480302004440212004440212008480111010d08414010d0900000c08060201404030200c04030200c08011031450860201404060200c040614218080434210d090007 (by decide +kernel)

def state115_1 : List Sig := [0xffffaaaa00000000ffffaaaa00000000ffffaaaa00000000ffffaaaa,input 5,input 4,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_1 : Impossible true (goalAt 115) 4 state115_1.toFinset :=
  node_ok cuts115 [] 0x21201808041030848021200c08011100848061421810060421810830201808050100c080714218508302018508602018508614208d08501010d08434218080414010d08434208480434214508110310d083010 (by decide +kernel)

def state115_2 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_2 : Impossible true (goalAt 115) 4 state115_2.toFinset :=
  node_ok cuts115 [] 0x222018080410308880434210500434208880111008880222004440110308880222040018302010d0843420c08043420c080302010d08434214508302010d0860201404060200c0406242180804103180801103 (by decide +kernel)

def state115_3 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 4,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_3 : Impossible true (goalAt 115) 5 state115_3.toFinset :=
  node_ok cuts115 [⟨state115_0,exclude115_0⟩,⟨state115_1,exclude115_1⟩,⟨state115_2,exclude115_2⟩] 0x60200c04060201404062421890860201890862421404030100890841030888022201808100061808041034001041031808022200888062420444062421810022201810062420888060421810011101810811030888022204001811100444011030444011104001822200888043420888043424000011101050043420444043424000022200888050100440c50101808100081808050104001050101808011031808030100440c301018909000818908301080008301018908110318909000240008514214041000714040602010d08434214040434210d0860204001c60200c040434210d0862428000461420c04200000c040624210d084342 (by decide +kernel)

def state115_4 : List Sig := [0xffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa,input 4,input 5,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_4 : Impossible true (goalAt 115) 4 state115_4.toFinset :=
  node_ok cuts115 [] 0x21201808041030848011100848021200444051421410050421410860201404060200c04050101450851421808051421c508301014508602010d08434214040414010d08434204440434218508210310d083020 (by decide +kernel)

def state115_5 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_5 : Impossible true (goalAt 115) 4 state115_5.toFinset :=
  node_ok cuts115 [] 0x21201808041030848043421050043420484021200c080121008480210308480212040018602010d0843420c040434218508301010d0830201808050100c080301010d08302010d085242180804103180802103 (by decide +kernel)

def state115_6 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 5,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_6 : Impossible true (goalAt 115) 5 state115_6.toFinset :=
  node_ok cuts115 [⟨state115_0,exclude115_0⟩,⟨state115_4,exclude115_4⟩,⟨state115_5,exclude115_5⟩] 0x50100c08030201808052421490850101490852421808030200c08100091490852420840c30200c08200020c08030200840c52421490a000114908514210d08302010d0a00000c080302010d08524210d0841030848021201808100061808041034001041031808021200848052420848052421410012101410052420484050421410021201410821030484012104001821200848021030848021204001812100484043420484043424000021201050043420848043424000012100484060200840c602014041000414040602040010602014040210314041000240008614218081000718080501010d08434218080434210d0850104001c5010 (by decide +kernel)

def state115_7 : List Sig := [0x1111111111110000111111111111000011111111111100001111111111110000,input 4,input 5,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_7 : Impossible true (goalAt 115) 4 state115_7.toFinset :=
  node_ok cuts115 [] 0x410310d08434218080434218508210310d08434214508110310d0860201890862420890030201490852420c08052421890830201490822201040c60200888021201810860420888062421410850420c0805242 (by decide +kernel)

def state115_8 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_8 : Impossible true (goalAt 115) 5 state115_8.toFinset :=
  node_ok cuts115 [⟨state115_0,exclude115_0⟩,⟨state115_2,exclude115_2⟩,⟨state115_5,exclude115_5⟩,⟨state115_7,exclude115_7⟩] 0x1040c434210d0860201050043420c042000210d0843420c082000110d0843424000a000010d0822201808041030888012100888022200484022200c08012100888200030888022204001860201404060200c04062420c08060201404030200c0403020400205242180804103180804103 (by decide +kernel)

def state115_9 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_9 : Impossible true (goalAt 115) 6 state115_9.toFinset :=
  node_ok cuts115 [⟨state115_3,exclude115_3⟩,⟨state115_6,exclude115_6⟩,⟨state115_8,exclude115_8⟩] 0x4001c60200c04060204001050101890862424001060201890862424001c50100c04022424001c50100c08030204002060201490852424001050101490852424001c60200c08030204002430101490852424002062420c08062428000830100c08030204002062421490852424000841034001c410340008602010d08434240008410310d08434240008602040008602040008210310d08434240008624240008614240008210380004210340008624210d08434240008110310d08434240008524240008514240008110380000110340008524210d084342400010000400004140400184103088802220400186020400186020400184103400104103400186020088802220400186242048406242400186040088806040400186242088806042400186040048406042400185242088805242400185040048405040400185242048405042400185040088805042 (by decide +kernel)

def state115_10 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_10 : Impossible true (goalAt 115) 4 state115_10.toFinset :=
  node_ok cuts115 [] 0x212010d08434208480212010d08434208480434208480212010d08434214108212010d0822200c08012100888022200484022200484030200c04030201040c60420888050421410900070c0805042141084103 (by decide +kernel)

def state115_11 : List Sig := [0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000,input 5,input 4,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_11 : Impossible true (goalAt 115) 4 state115_11.toFinset :=
  node_ok cuts115 [] 0x8480434210d08212010d08504204440434210d0860420848043421040c434210d0900061040c22200888100000c08050421410822201410860420c080504204c0c2220181086042048402303 (by decide +kernel)

def state115_12 : List Sig := [0xffffffff00000000ffff000000000000ffffffff00000000ffff0000,input 5,input 4,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_12 : Impossible true (goalAt 115) 4 state115_12.toFinset :=
  node_ok cuts115 [] 0x212010d08434208480434214108111010d08434208480212010d0830201410850420888050420c08030201410822200484022200484043420848043420848012100888012100888050420c08050420c0806042 (by decide +kernel)

def state115_13 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_13 : Impossible true (goalAt 115) 5 state115_13.toFinset :=
  node_ok cuts115 [⟨state115_10,exclude115_10⟩,⟨state115_11,exclude115_11⟩,⟨state115_12,exclude115_12⟩] 0x22200c040222004840604218108222018108604204840301004842000208c0c23031040c60421810a00011810860421040c230308900230310d08434218108212018108230308480212018108434210d09000708480212008880434210d09000410d08434208880212008481000810d08434214108111014109000404440111014108434210d08410308480212040018434210d08410310d0843424001821200848041030888022204000012101808041030484012104000022200888030101410850421810900081810830108000030101810850421410812104001c1210088805042141081210141085042088810007088810005400143020 (by decide +kernel)

def state115_14 : List Sig := [0xffff0000ffff0000ffff000000000000ffff0000ffff0000ffff00000000,input 4,input 5,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_14 : Impossible true (goalAt 115) 4 state115_14.toFinset :=
  node_ok cuts115 [] 0x212010d08434208480434218108212010d08434204440111010d0822201810860420484012100888012100888030101810830101810843420444043420444022200484022200484060420c04060420c0405042 (by decide +kernel)

def state115_15 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_15 : Impossible true (goalAt 115) 4 state115_15.toFinset :=
  node_ok cuts115 [] 0x212010d08434208480111010d0843420444043420c080111010d08434218108212010d0812100888022200484030200888012100888030100c08030201040c50420888060421810900070c0406042181084103 (by decide +kernel)

def state115_16 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_16 : Impossible true (goalAt 115) 5 state115_16.toFinset :=
  node_ok cuts115 [⟨state115_11,exclude115_11⟩,⟨state115_14,exclude115_14⟩,⟨state115_15,exclude115_15⟩] 0x12100c08030200888050421410812101410850420888030200888100091410850421810830201810a00020c08030201810850421410a000104c0c13031040c50421410a00001410850421040c130304900130310d08434214108111014108130304440111014108434210d09000708480212008880434210d09000410d08434208880212008481000410d08434218108212018109000408480212018108434210d08410304440111040018434210d08410310d0843424001811100444041030484012104000022200888041030888022204000012100484022204001c2220048406042181082220181086042048410007048410005400143010 (by decide +kernel)

def state115_17 : List Sig := [0x333333333333000000000000000000003333333333330000,input 4,input 5,input 6,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_17 : Impossible true (goalAt 115) 4 state115_17.toFinset :=
  node_ok cuts115 [] 0x212010d08434208480434218108212010d08434214108111010d0830101810860420890030201410850420c080504218108302014108212010d08212010d0860200484060420888060420888050420c0805042 (by decide +kernel)

def state115_18 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_18 : Impossible true (goalAt 115) 5 state115_18.toFinset :=
  node_ok cuts115 [⟨state115_11,exclude115_11⟩,⟨state115_10,exclude115_10⟩,⟨state115_15,exclude115_15⟩,⟨state115_17,exclude115_17⟩] 0x8480434210d08212008480434210d08212010d08212008480434210d08302004440434210d0821200848043421808030101040e00020c04022200484022200484060420c08041038000430200c08022200484022200c0403020400205042400144103800004103088820003088810007 (by decide +kernel)

def state115_19 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_19 : Impossible true (goalAt 115) 6 state115_19.toFinset :=
  node_ok cuts115 [⟨state115_13,exclude115_13⟩,⟨state115_16,exclude115_16⟩,⟨state115_18,exclude115_18⟩] 0x4001500050c04030104001441031810860424001600011810860424001441030c04022404001c22200c04022204001c12101810860424001c22201810860424001c12100c04012104002430101410850424002060420c08060428000830100c08030204002060421410850424001500050c08030204001441031410850424001600001410850424001441030c08030204001c12100c08030204001c22201410850424001c12101410850424001c22200c080222040010230310d08434240018604208480604240010230308480212040018604210d08434240020130310d08434240018504204440504240010130304440111040018504210d08434240014410308480212040015000610d08434240014410310d0843424001500050848021204001d000708480212040018222010d0843424001d000410d084342400182220084802120400010000400006020 (by decide +kernel)

def state115_20 : List Sig := [0xffffffffffffaaaa0000000000000000ffffffffffffaaaa,input 5,input 0,input 4,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_20 : Impossible true (goalAt 115) 4 state115_20.toFinset :=
  node_ok cuts115 [] 0x1490850401410850421890860401810860421490862420c080524210500434210d08414210d08524204440434210d0862420848043420888041030888060200c08052420c0805242084804342084804342089086242180806242 (by decide +kernel)

def state115_21 : List Sig := [0x3333333333332222333333333333222233333333333322223333333333332222,input 5,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_21 : Impossible true (goalAt 115) 4 state115_21.toFinset :=
  node_ok cuts115 [] 0xc08052421490830201490862420c080524208480434210d08212010d08524204440434210d0862420848043421808062421890822400888041031808022201410850420c0805242105084342084804342181086042088806242 (by decide +kernel)

def state115_22 : List Sig := [0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaa,input 5,input 0,input 4,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_22 : Impossible true (goalAt 115) 5 state115_22.toFinset :=
  node_ok cuts115 [⟨state115_0,exclude115_0⟩,⟨state115_20,exclude115_20⟩,⟨state115_21,exclude115_21⟩] 0x22201808041030888022200c08012100888012100888022200484200020888022204000030201808050100c08030100c080302004c0c524208480602010c0c212008480222080000212008480302004440212004440212008480111010d0860201404060200c0406242180820001180810005 (by decide +kernel)

def state115_23 : List Sig := [0xffffaaaa00000000ffffaaaa00000000ffffaaaa00000000ffffaaaa,input 5,input 0,input 4,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_23 : Impossible true (goalAt 115) 5 state115_23.toFinset :=
  node_ok cuts115 [⟨state115_1,exclude115_1⟩] 0x22201808041030888022200c08012100888062421810060421810830201808050100c08072421890830201890821201808043030848021200888200000848021200c08011100848063421890821201890860201890862420890850101808050101808012100888012100888052421490813030c080434210d081110084803010 (by decide +kernel)

def state115_24 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_24 : Impossible true (goalAt 115) 4 state115_24.toFinset :=
  node_ok cuts115 [] 0x888060201040c222008880212004840212004840222008880111004c0c222008880110308480512014040212010d084342084810001149085242084802203180805010180801110189086242044401203180804303180801303 (by decide +kernel)

def state115_25 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 5,0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 4,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_25 : Impossible true (goalAt 115) 5 state115_25.toFinset :=
  node_ok cuts115 [⟨state115_24,exclude115_24⟩] 0x888060201040c222008880121004840222008880212004840212004840222008880121004840222008880111014040602014040602014908130308c0e000004c0c111004c0c11100480c21201808050100848023030848021200880c434210d082120400046020140406020140406242180805010180801110 (by decide +kernel)

def state115_26 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_26 : Impossible true (goalAt 115) 5 state115_26.toFinset :=
  node_ok cuts115 [⟨state115_24,exclude115_24⟩,⟨state115_2,exclude115_2⟩] 0x888060201040c222008880302004840222004840222008880121004c0c222008880110304440602010c0c602004440222080004222010d0811100844200000444013030444011100480c30201808050100c08030100c08030204000c52421490830204000860201404060200c0406242180804303180801303 (by decide +kernel)

def state115_27 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 0,input 4,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_27 : Impossible true (goalAt 115) 6 state115_27.toFinset :=
  node_ok cuts115 [⟨state115_3,exclude115_3⟩,⟨state115_22,exclude115_22⟩,⟨state115_23,exclude115_23⟩,⟨state115_25,exclude115_25⟩,⟨state115_26,exclude115_26⟩] 0x60200c040602014040624218908602018908624214040301008908430308880222018081000618080430340010410318080222008880624204840624218100222018100624208880604218100121018108130308880222004404121004840130304840121004404222008881000608880222040000121004841000604840121040000222008880501004c0c501018081000118080501040010501018080130318080301004c0c301018909000118908301080010301018908130318909000140008524210c0c111004440602040008602010c0d000410c0c602004440602008c0c111004440624240008624208c0e000308c0c624204440624240008111004440222040008222040009000680000222004440222004c0d000104c0d00020444011104000500010480d00014000443421404100051404060204001060201404100041404060204001460200c04100030c04062428000862420c04200010c04062424000c6242 (by decide +kernel)

def state115_28 : List Sig := [0xffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa,input 4,input 0,input 5,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_28 : Impossible true (goalAt 115) 5 state115_28.toFinset :=
  node_ok cuts115 [⟨state115_4,exclude115_4⟩] 0x22201808041030888012100888022200484052421410050421410860201404060200c04021201808043030848021200888200000848011100848021200444053421490811101490850101490852421808052421c90830101490860201404060201404022200484022200484062421890823030c040434210d082120044403020 (by decide +kernel)

def state115_29 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_29 : Impossible true (goalAt 115) 5 state115_29.toFinset :=
  node_ok cuts115 [⟨state115_24,exclude115_24⟩,⟨state115_5,exclude115_5⟩] 0x888060201040c222004840222008880121008880302004840222008c0c222008880210308480602010c0c212008480222080004212010d0821200c08200000848023030848021200880c60201404060200c04062421890830104000430201808050100c08030100c0803020400045242180804303180802303 (by decide +kernel)

def state115_30 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 5,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_30 : Impossible true (goalAt 115) 6 state115_30.toFinset :=
  node_ok cuts115 [⟨state115_6,exclude115_6⟩,⟨state115_25,exclude115_25⟩,⟨state115_22,exclude115_22⟩,⟨state115_28,exclude115_28⟩,⟨state115_29,exclude115_29⟩] 0x50100c08030201808052421490850101490852421808030200c081000314908524208c0c30200c08200040c080302008c0c52421490a00031490852424000430200c08200020c080302040004524214908430308880222018081000618080430340010410318080222008880524208880524214100121014100524204840504214100222014108230304840121008404222008880230308880222008404121004841000604840121040000222008881000608880222040000121004840602008c0c602014041000314040602040010602014040230314041000240008624210c0c212008480602040008602010c0d000410c0c602008480212004c0c212008480524240008524204c0e000104c0c524208480524240008212008480222040008222040009000680000222008480212008c0d000308c0d00020848021204000900020880d00024000c4342180810005180805010400105010180810004180805010400145010 (by decide +kernel)

def state115_31 : List Sig := [0xbbbbbbbbbbbbaaaa0000000000000000bbbbbbbbbbbbaaaa,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_31 : Impossible true (goalAt 115) 3 state115_31.toFinset :=
  node_ok cuts115 [] 0x1410860420c080504210d08604208480434210d0850420444043420484060420888060420888050420c0805042084804342084804342 (by decide +kernel)

def state115_32 : List Sig := [0xbbbbbbbbbbbbaaaabbbbbbbbbbbbaaaabbbbbbbbbbbbaaaabbbbbbbbbbbbaaaa,input 0,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_32 : Impossible true (goalAt 115) 4 state115_32.toFinset :=
  node_ok cuts115 [⟨state115_31,exclude115_31⟩] 0x60201890862420890030201490852420c08052421890830201490821201808041030848011101890821201890821201490811101490843420888200001808022201810860420888062421410850420c0805242 (by decide +kernel)

def state115_33 : List Sig := [0x5555555555555555111111111111000055555555555555551111111111110000,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_33 : Impossible true (goalAt 115) 3 state115_33.toFinset :=
  node_ok cuts115 [] 0x1808060421810830101410860420c08050420c080504214108302010d08212018108434210d08111014108434208480434210d082120 (by decide +kernel)

def state115_34 : List Sig := [0xffffffffffffffff3333333333330000ffffffffffffffff3333333333330000,input 6,input 4,input 5,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_34 : Impossible true (goalAt 115) 4 state115_34.toFinset :=
  node_ok cuts115 [⟨state115_33,exclude115_33⟩] 0x434218108212010d08434214108111010d08212010d08434208482000010d0843420888060201810860420c04022201810860420484050421810830201410830201410850420c0801210141085042088804103 (by decide +kernel)

def state115_35 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,input 4,input 5,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_35 : Impossible true (goalAt 115) 5 state115_35.toFinset :=
  node_ok cuts115 [⟨state115_7,exclude115_7⟩,⟨state115_17,exclude115_17⟩,⟨state115_32,exclude115_32⟩,⟨state115_34,exclude115_34⟩] 0x1040c212008480602010d0843421040c434210d08602008480212008c0c434210d08624208480624208c0c212008480624210d08434204c0c434210d08524204440524204c0c111004440524210d0843421808030101808050101890862421808062421890850100c04022401404030200c08060201490852421404052421490860200c08030200c04052421490862420c08062420c04030200c08062421490852421808022200888041038000441031808200031808041030888022200848022200848043428000043420848200020848043420888043420c04012101810862420888060420c04022200888062420484062420c08022201410852420484050420c08012100c0805242088805242 (by decide +kernel)

def state115_36 : List Sig := [0x5555555555555555555555555555000055555555555555555555555555550000,input 6,input 4,input 5,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_36 : Impossible true (goalAt 115) 4 state115_36.toFinset :=
  node_ok cuts115 [] 0x1890860401810860421490850401410850420888060201040c22201808062421890822421490862420c08052420c080524214908302010508434210d08414010d08212018908434210d08111014908434208480434210d082120 (by decide +kernel)

def state115_37 : List Sig := [0x3333333333333333333333333333000033333333333333333333333333330000,input 6,input 4,input 5,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_37 : Impossible true (goalAt 115) 4 state115_37.toFinset :=
  node_ok cuts115 [] 0x10d08624208480434210d08524204440434208480434210d0821201808062421890822421490862420c08052420c0805242149083020105084342105004342181086042181006242141085042141005242088804103180802220 (by decide +kernel)

def state115_38 : List Sig := [0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000,input 6,input 4,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_38 : Impossible true (goalAt 115) 5 state115_38.toFinset :=
  node_ok cuts115 [⟨state115_11,exclude115_11⟩,⟨state115_36,exclude115_36⟩,⟨state115_37,exclude115_37⟩] 0x624218100604218108524214100504214108222018082000008882000208880222040000414010d08434210508434218908212010d08434214908111010d08212010d08434208482000110d0843424000860201890862420890823031490862420c08052420c080524214908302004c0c4303 (by decide +kernel)

def state115_39 : List Sig := [0xffffffffffff00000000000000000000ffffffffffff0000,input 6,input 4,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_39 : Impossible true (goalAt 115) 5 state115_39.toFinset :=
  node_ok cuts115 [⟨state115_17,exclude115_17⟩] 0x624218100604218108524214100504214108222010404410308880414010d08434210508434218908212010d08434214908111010d08212010d0843420848030101890862420c04052421890830201490830201490852420c080222080000222040000212010d08212010d083010189083010189083020149083020149086020 (by decide +kernel)

def state115_40 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_40 : Impossible true (goalAt 115) 4 state115_40.toFinset :=
  node_ok cuts115 [] 0x14908504014108504208880302004840222004840222008880121010500434210d08414210d08524208480434208480434210d08212004440434210d0811100c08052421490822420c04052421490812420c04030200c0810001 (by decide +kernel)

def state115_41 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_41 : Impossible true (goalAt 115) 5 state115_41.toFinset :=
  node_ok cuts115 [⟨state115_10,exclude115_10⟩,⟨state115_40,exclude115_40⟩] 0x4840222008880121014908504014108504208880501080000222008880302004840222010500434210d08414210d08212008480434210d08524208480434208480434210d08212008480434210d0821201890830101404200010c04030200c04030204000c50101490852420490830201490852424000c6020 (by decide +kernel)

def state115_42 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_42 : Impossible true (goalAt 115) 5 state115_42.toFinset :=
  node_ok cuts115 [⟨state115_40,exclude115_40⟩,⟨state115_15,exclude115_15⟩] 0x8880302004840222018908604018108604208880602080004222004840222008880121010500434210d08414210d08302004440434210d08624208480434208480434210d08212004440434210d0811101490830201408200000c08030100c0803020400046020189086242089083010189086242400045010 (by decide +kernel)

def state115_43 : List Sig := [0x5555555555550000555555555555000055555555555500005555555555550000,input 0,input 4,input 5,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_43 : Impossible true (goalAt 115) 5 state115_43.toFinset :=
  node_ok cuts115 [⟨state115_7,exclude115_7⟩] 0x22201808041030888012100888022200484022200c08012100888060201404060200c04030201808050100c08030100c080302004c0c430310d08434218080414010d08434210508434218d08230310d08434214d08130310d08602010c0c602010c0c222080000222040000624218908301008c0c524214908302004c0c2120 (by decide +kernel)

def state115_44 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_44 : Impossible true (goalAt 115) 5 state115_44.toFinset :=
  node_ok cuts115 [] 0x8480434210d08212010d08212008480434210d08302004440434210d0821200848043421808050101808030101890830201808050100c08030100c08100081490860201040c60201040c22201040c602008880212010d08212010d081210088802220048402220048403020088810000 (by decide +kernel)

def state115_45 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_45 : Impossible true (goalAt 115) 6 state115_45.toFinset :=
  node_ok cuts115 [⟨state115_22,exclude115_22⟩,⟨state115_26,exclude115_26⟩,⟨state115_29,exclude115_29⟩,⟨state115_8,exclude115_8⟩,⟨state115_18,exclude115_18⟩,⟨state115_35,exclude115_35⟩,⟨state115_38,exclude115_38⟩,⟨state115_39,exclude115_39⟩,⟨state115_41,exclude115_41⟩,⟨state115_42,exclude115_42⟩,⟨state115_43,exclude115_43⟩,⟨state115_44,exclude115_44⟩] 0x43030888022201808100081808043038001041031808022200888100030484012100c04022200888100080888022200c04012100484100010888022200c08012100c08100080484012100c08022200888100088002e000540000222008881000808880222040001000840000430308480212018080434210d08430310d08434218080212008481000810500414008880434210d0a000310d08434208880414010509000310d0843420c04021200848200020848021200c040434210d09000110d0843420c08011100c08200010444011100c080434210d0a000a10d08434240008212008482000008480212040008434210d0860200c04060201404100031404060208002460201404030100c04100014000462421404030200c08060204000460201404200081404060200c08030200c04100030c04100010c08030204000500014000500014000c52421808100051808043038001c4303180820006180804303400144303 (by decide +kernel)

def state115_46 : List Sig := [0xffffffff00000000ffff000000000000ffffffff00000000ffff0000,input 5,input 4,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_46 : Impossible true (goalAt 115) 5 state115_46.toFinset :=
  node_ok cuts115 [⟨state115_12,exclude115_12⟩] 0x222018082000008880524214100504214108121008880222004840414010d08434210508212010d08434208480434214908111010d08434208480212010d0830201490852420c08052420c08030201490860201404060201404012100888012100888043420848043420848050101808050101808052420c08052420c0806242 (by decide +kernel)

def state115_47 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_47 : Impossible true (goalAt 115) 5 state115_47.toFinset :=
  node_ok cuts115 [⟨state115_40,exclude115_40⟩] 0x14908504014108504208880602004840222018908604018108604204840222008880121010500434210d08414210d08524204440434208480434210d08212010d08624208480434204440434210d0811100c08052421890a0000149085010149085242049085010180806020400046020189086242089083010 (by decide +kernel)

def state115_48 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_48 : Impossible true (goalAt 115) 6 state115_48.toFinset :=
  node_ok cuts115 [⟨state115_41,exclude115_41⟩,⟨state115_13,exclude115_13⟩,⟨state115_38,exclude115_38⟩,⟨state115_46,exclude115_46⟩,⟨state115_47,exclude115_47⟩] 0x100050c04030101404062421890a00041890862421404030100c042000308c0c23034000c62421890a00021890862424000c230308c0c624204840624218100222018100624208880604218100121018109000508880222014041000514041000740016000114040222008880524208880524214100121014100524204840504214100222014109000708880222040000121004841000704840121040000222008880230310d08434218908212018908230308480212018908434210d09000710500414008880434210d09000410d08434208880414010509000508480212014040434210d09000410d08434214040212008481000110d08434214908111014909000404440111014908434210d09000408480212040008434210d09000410d0843424000821200848100014000460200c04052421490862424000462420c04200000c0406242149085242140410005140410001149085242400050001049090001400143020 (by decide +kernel)

def state115_49 : List Sig := [0xffff0000ffff0000ffff000000000000ffff0000ffff0000ffff00000000,input 4,input 5,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_49 : Impossible true (goalAt 115) 5 state115_49.toFinset :=
  node_ok cuts115 [⟨state115_14,exclude115_14⟩] 0x222018082000008880624218100604218108222004840121008880414010d08434210508212010d08434208480434218908212010d08434204440111010d0860201890862420890850101808050101808030101890830101890822200484022200484043420444043420444060201404060201404062420c04062420c0405242 (by decide +kernel)

def state115_50 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_50 : Impossible true (goalAt 115) 6 state115_50.toFinset :=
  node_ok cuts115 [⟨state115_16,exclude115_16⟩,⟨state115_38,exclude115_38⟩,⟨state115_42,exclude115_42⟩,⟨state115_47,exclude115_47⟩,⟨state115_49,exclude115_49⟩] 0x100050c08030201808052421490a00031490852421808030200c08100031490852421890830201890a00020c08030201890852421490a000404c0c13034000452421490a000114908524240004130304c0c524208880524214100121014100524204840504214100222014109000508880222018081000518081000740016000018080222008880624204840624218100222018100624208880604218100121018109000704840121040000222008881000708880222040000121004840130310d08434214908111014908130304440111014908434210d09000710500414008880434210d09000410d08434208880414010509000508480212018080434210d09000410d08434218080212008481000310d08434218908212018909000408480212018908434210d09000404440111040008434210d09000410d0843424000811100444100034000c50101808100051808100031890862424000d0003089090003400143010 (by decide +kernel)

def state115_51 : List Sig := roots 115
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_51 : Impossible true (goalAt 115) 7 state115_51.toFinset :=
  node_ok cuts115 [⟨state115_9,exclude115_9⟩,⟨state115_19,exclude115_19⟩,⟨state115_27,exclude115_27⟩,⟨state115_30,exclude115_30⟩,⟨state115_45,exclude115_45⟩,⟨state115_48,exclude115_48⟩,⟨state115_50,exclude115_50⟩] 0x4001460200c04060204000c50101890862428001860201890862424000c50100c04022424001450100c08030204000460201490852428001450101490852424000460200c08030204000c30101490852424000462420c08062428001030100c080302040004624214908524240000430308880222040000602040000602040000430380004410340000602008880222040000624204840624240000604008880604040000624208880604240000604004840604240000524208880524240000504004840504040000524204840504240000504008880504240014430308480212040008602010d08434240010430310d0843424000860200848021204000c230310d0843424000862420848062428000c230308480212040008624210d08434240004130310d08434240008524204440524280008130304440111040004524210d08434240001000010500414040000222010d08434240002000010d084342400002220105004142 (by decide +kernel)

theorem lower115 : Claim 115 8 :=
  fromSearch 68 (by decide +kernel) exclude115_51

theorem lower227 : Claim 227 7 :=
  fromLift 7 2 85 lower225 (by decide +kernel)

theorem lower211 : Claim 211 7 :=
  fromLift 7 2 68 lower209 (by decide +kernel)

def rule243_0 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower241 none (by decide +kernel)

def rule243_1 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower242 none (by decide +kernel)

def rule243_2 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower179 none (by decide +kernel)

def rule243_3 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower115 none (by decide +kernel)

def rule243_4 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower227 none (by decide +kernel)

def rule243_5 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower211 none (by decide +kernel)

def rule243_6 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower163 none (by decide +kernel)

def rule243_7 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower179 (some (1,input 4,input 5)) (by decide +kernel)

def rule243_8 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower193 none (by decide +kernel)

def rule243_9 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower99 none (by decide +kernel)

def rule243_10 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower115 (some (1,input 4,input 5)) (by decide +kernel)

def rule243_11 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower226 none (by decide +kernel)

def rule243_12 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower242 (some (1,input 4,input 5)) (by decide +kernel)

def rule243_13 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower225 none (by decide +kernel)

def rule243_14 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower224 none (by decide +kernel)

def rule243_15 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower81 none (by decide +kernel)

def rule243_16 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower209 none (by decide +kernel)

def rule243_17 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower145 none (by decide +kernel)

def cuts243 : Cuts (goalAt 243) := [rule243_0,rule243_1,rule243_2,rule243_3,rule243_4,rule243_5,rule243_6,rule243_7,rule243_8,rule243_9,rule243_10,rule243_11,rule243_12,rule243_13,rule243_14,rule243_15,rule243_16,rule243_17]

def state243_0 : List Sig := [0xffffffffffffffffbbbbbbbbbbbbaaaa,input 6,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_0 : Impossible true (goalAt 243) 4 state243_0.toFinset :=
  node_ok cuts243 [] 0x28208c08218108a08224208a0820c080908224208c08214108908220e08a08208480838220e08908204440838220e08c08210d08838218108a08218108a08214108908214108908210d08838210d08838208880c08230108c082 (by decide +kernel)

def state243_1 : List Sig := [0xffffffffffffffffbbbbbbbbbbbbaaaaffffffffffffffffbbbbbbbbbbbbaaaa,input 6,input 0,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_1 : Impossible true (goalAt 243) 5 state243_1.toFinset :=
  node_ok cuts243 [⟨state243_0,exclude243_0⟩] 0x18108a28228a08604228a08604218108a28228208a08218108a28214108928224a08504224a08a2820c080928224a08504214108928224208908214108928210d08c0422040c434210d08a28208480a28210d08928204440928208480434210d08212020e08c04228080c04218080c0823010a0000301082220 (by decide +kernel)

def state243_2 : List Sig := [0xbbbbbbbbbbbbaaaa0000000000000000bbbbbbbbbbbbaaaa,input 6,input 0,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_2 : Impossible true (goalAt 243) 5 state243_2.toFinset :=
  node_ok cuts243 [] 0x604228a08a28218108a28230208604228a08504224a08928214108928228a08302024a08928230208504224a08434230108810310d08434228a08212028a08434224a08111024a08c18230208434230208c04230208c08228080222030108a02030108a08228208222028a08908224208302024a08838220e08212010d086020 (by decide +kernel)

def state243_3 : List Sig := [0xffffffffffffffff0000000000000000bbbbbbbbbbbbaaaa,input 7,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_3 : Impossible true (goalAt 243) 4 state243_3.toFinset :=
  node_ok cuts243 [] 0x18108a08228208604224208a0820c080908214108908224208504220e08a08208480838220e08908204440838210d08838220e08434228208604228208c08224208504224208c08220e08434220e08c08208880c08230208c042 (by decide +kernel)

def state243_4 : List Sig := [0xffffffffffffffffffffffffffffffffbbbbbbbbbbbbaaaabbbbbbbbbbbbaaaa,input 7,input 0,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_4 : Impossible true (goalAt 243) 5 state243_4.toFinset :=
  node_ok cuts243 [⟨state243_3,exclude243_3⟩] 0x18080c08230208602080000c08230208222028208c08218908a08218908a08228208624218108a08228208624224208c08214908908224208a0820c080908214908908224208524214108908224208524220e08c0821040c838220e08a08208480838220e08908204440838208480838220e08212010d08c042 (by decide +kernel)

def state243_5 : List Sig := [0xbbbbbbbbbbbbaaaabbbbbbbbbbbbaaaa,input 7,input 0,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_5 : Impossible true (goalAt 243) 5 state243_5.toFinset :=
  node_ok cuts243 [] 0xc04230208c08218080a08230208624228208624228208a08218908908230208524224208908228208302024208524224208908214908838230208410320e08838228208212020e08838224208111020e08c14220e08838230108222030208602030208604228208222028208504224208302024208434220e08212020e08a020 (by decide +kernel)

def state243_6 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 6,0xbbbbbbbbbbbbaaaabbbbbbbbbbbbaaaabbbbbbbbbbbbaaaabbbbbbbbbbbbaaaa,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_6 : Impossible true (goalAt 243) 5 state243_6.toFinset :=
  node_ok cuts243 [] 0x624228a08a28218908a28218908624228a08a28218908624228a08524224a08928214908928228a08302024a08928214908524224a08928214908524224a08434230108a02010d08a08228208222028a08908224208302024a08222010d08434208880838220e08434208880c04228080c04228080c08230108a020301082120 (by decide +kernel)

def state243_7 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xbbbbbbbbbbbbaaaabbbbbbbbbbbbaaaabbbbbbbbbbbbaaaabbbbbbbbbbbbaaaa,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_7 : Impossible true (goalAt 243) 5 state243_7.toFinset :=
  node_ok cuts243 [] 0x602030208c08218080602030208c08208480a28230208624228a08624228a08a28218908624228a08a28218908928230208524224a08928228a08302024a08524224a08928214908524224a08928214908838230208602020e08838228208222020e08838224208302020e08222020e08838208880434220e08838208880c042 (by decide +kernel)

def state243_8 : List Sig := [0xbbbbbbbbbbbbaaaabbbbbbbbbbbbaaaabbbbbbbbbbbbaaaabbbbbbbbbbbbaaaa,input 0,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_8 : Impossible true (goalAt 243) 6 state243_8.toFinset :=
  node_ok cuts243 [⟨state243_1,exclude243_1⟩,⟨state243_2,exclude243_2⟩,⟨state243_4,exclude243_4⟩,⟨state243_5,exclude243_5⟩,⟨state243_6,exclude243_6⟩,⟨state243_7,exclude243_7⟩] 0xc04218080c04228080c08230208c04230208c08228080602018080a02018908624230108a28228a08a02028a08a28230108624218908602028a08a28230208624230208602018908624230208a28228a08901014908524230108928224a08901024a08928230108524214908501024a08928230208524230208501014908524230208928224a08301024a08928228a08302028a0830100c080302028a08928224a08810308480212030109000e30108810380014810330108212030108410308480212030209000e30208410380010410330208212030208210304440111028a08212028a08210308480212028a08111028a08110308480212024a08111024a08110304440111024a08212024a09000e40020838228080222008880c0428000cc04228082000228080c04208880c04218080222008880c08280004c08218082000018080c08208880c0820c040121028208a28208880a0820c040222008880a28204840a2820c08022202420892820484090820c08012100c0809282088809282 (by decide +kernel)

def state243_9 : List Sig := [0x5555555555555555555555555555555555555555555555551111111111110000,input 7,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_9 : Impossible true (goalAt 243) 4 state243_9.toFinset :=
  node_ok cuts243 [] 0x28208c08218108a08218108a08228208604224208a0820c080908224208c08214108908214108908224208504230108c08230208602020e08212028208838220e08111024208838220e08434230208838210d08838220e084342 (by decide +kernel)

def state243_10 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff3333333333330000,input 7,input 6,input 4,input 5,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_10 : Impossible true (goalAt 243) 5 state243_10.toFinset :=
  node_ok cuts243 [⟨state243_9,exclude243_9⟩] 0x20e08a08208480838220e08908204440838220e08c08210d08838210d08838220e08434280000838220e08222028208c08218108a08218108a08228208604208880a08228208121024208a0820c080908224208c08214108908214108908224208504204840908224208222030108c0823020860201040c8103 (by decide +kernel)

def state243_11 : List Sig := [0xffffffffffffffff3333333333330000,input 7,input 6,input 4,input 5,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_11 : Impossible true (goalAt 243) 5 state243_11.toFinset :=
  node_ok cuts243 [] 0x838228208212020e08838224208111020e08838230208434220e08434220e08838210d08a08230208604228208604228208a08218108908228208302024208908230208504224208504224208908214108602030208c08218080434220e08434220e08604228208604228208504224208504224208222030208602030208c042 (by decide +kernel)

def state243_12 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffff3333333333330000ffffffffffffffff3333333333330000,input 4,input 5,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_12 : Impossible true (goalAt 243) 5 state243_12.toFinset :=
  node_ok cuts243 [] 0x838228a08212020e08838224a08111020e08838230208434220e08434220e08838210d08212020e08838208480a08228208604228a08604228a08a28218108602028a08a2820c040928228a08302024a08908224208504224a08504224a08928214108302024a0892820c080c04230208c08208880222030208c08208880a020 (by decide +kernel)

def state243_13 : List Sig := [0x5555555555555555111111111111000055555555555555551111111111110000,input 0,input 6,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_13 : Impossible true (goalAt 243) 5 state243_13.toFinset :=
  node_ok cuts243 [] 0x604228a08a28218108a28218108604228a08504224a08928214108928228a08302024a08928214108504224a08c04228080c04218080810320e08838230108838228608210320e08838224608110320e08838230608410320e08c0422040cc04208880a08228208604228a08908224208504224a08c082302086020088804342 (by decide +kernel)

def state243_14 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,0xffffffffffffffff3333333333330000ffffffffffffffff3333333333330000,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_14 : Impossible true (goalAt 243) 5 state243_14.toFinset :=
  node_ok cuts243 [] 0x604228a08a28218108a08228208604228a08a28218108604228a08504224a08928214108928228a08302024a08908224208504224a08928214108504224a08c0422040cc04208880c08230208602008880434230108810310d08434228a08230328a08434224a08130324a08410310d08434208880838230108a020301086020 (by decide +kernel)

def state243_15 : List Sig := [0xffffffffffffffff3333333333330000ffffffffffffffff3333333333330000,input 6,input 4,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_15 : Impossible true (goalAt 243) 6 state243_15.toFinset :=
  node_ok cuts243 [⟨state243_1,exclude243_1⟩,⟨state243_10,exclude243_10⟩,⟨state243_11,exclude243_11⟩,⟨state243_12,exclude243_12⟩,⟨state243_13,exclude243_13⟩,⟨state243_14,exclude243_14⟩] 0x810310d08434230108838220e08810320e08838230108434210d08230320e08838228a08212028a08230308480212028a08838220e08130320e08838224a08111024a08130304440111024a08838220e09001120e08838218080434210d0a000510d08434218080838220e0a000420e08838208880434210d0a000010d08434208880838220e08a02018108604230108a28228a08a02028a08a28230108604218108602028a08a28214040604218108602018108604214040a28228a08222028a08a08204840604228208222018108604204840a28228a08901014108504230108928224a08901024a08928230108504214108301024a08928228a08302028a0830100c080302028a08928224a08501024a08928218080504214108501014108504218080928224a08121024a08908208880504224208121014108504208880928224a08c04218080c04228081001128080c0428000cc04228080602018081000840020c0823010822203010881038000881033010a0001301088103088802220 (by decide +kernel)

def state243_16 : List Sig := [0x5555555555555555555555555555555511111111111100001111111111110000,input 0,input 7,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_16 : Impossible true (goalAt 243) 5 state243_16.toFinset :=
  node_ok cuts243 [] 0x602030208c08218080a08230208624228208624228208a08218908908230208524224208908228208302024208524224208908214908410330208434230208434228208210328208434224208110324208434230508810310d08c0821040cc08208880a08218108a08218908908214108908214908c04230108a020088808382 (by decide +kernel)

def state243_17 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,0xffffffffffffffffffffffffffffffff33333333333300003333333333330000,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_17 : Impossible true (goalAt 243) 5 state243_17.toFinset :=
  node_ok cuts243 [] 0x410330208c08208880602030208c08218080a08230208624228208604228208a08218908624228208a08218908908230208524224208908228208302024208504224208908214908524224208908214908c04230108a02008880838230208410320e08838228208230320e08838224208130320e08810320e088382088804342 (by decide +kernel)

def state243_18 : List Sig := [0xffffffffffffffff00000000000000003333333333330000,input 6,input 7,input 4,input 5,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_18 : Impossible true (goalAt 243) 5 state243_18.toFinset :=
  node_ok cuts243 [] 0x838228208212020e08838224208111020e08434220e08838210d08838210d08434220e08604228208a08218108a08218108604228208908228208302024208504224208908214108908214108504224208c04228080c04228080838210d08838210d08a08218108a08218108908214108908214108222030108a02030108c082 (by decide +kernel)

def state243_19 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffff33333333333300003333333333330000,input 4,input 5,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_19 : Impossible true (goalAt 243) 5 state243_19.toFinset :=
  node_ok cuts243 [] 0x838228208212020e08838224208111020e08434220e08838210d08838230208434220e08212020e08838208480604228208a08218908a08230208624228208a02028208a0820c04090822820830202420850422420890821490890823020852422420830202420890820c080222030108c04208880c04230208c082088806020 (by decide +kernel)

def state243_20 : List Sig := [0xffffffffffffffffffffffffffffffff33333333333300003333333333330000,input 7,input 4,input 5,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_20 : Impossible true (goalAt 243) 6 state243_20.toFinset :=
  node_ok cuts243 [⟨state243_4,exclude243_4⟩,⟨state243_10,exclude243_10⟩,⟨state243_16,exclude243_16⟩,⟨state243_17,exclude243_17⟩,⟨state243_18,exclude243_18⟩,⟨state243_19,exclude243_19⟩] 0x1000f18080602028080c0823020a000530208c0822808060201808200041040c410308880c0823020a000130208c08208880410308880410320e08838230208434230208410310d08434230208838220e08230320e08838228208212028208230308480212028208838220e08130320e08838224208111024208130304440111024208838220e09000f10d08434228080838220e0a000320e08838228080434210d0a000210d08434208880838220e0a000020e08838208880434210d08602028208a08230208624230208602018908624230208a08228208a02018908624224040a08228208a02028208a08224040624218908222018908604204840a08228208222028208a0820484062421890850102420890823020852423020850101490852423020890822420830102420890822820830202820830100c080302028208908224208901014908524228080908224208901024208908228080524214908121014908504208880908224208121024208908208880524214909000f40020c042 (by decide +kernel)

def state243_21 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 6,0x3333333333330000333333333333000033333333333300003333333333330000,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_21 : Impossible true (goalAt 243) 6 state243_21.toFinset :=
  node_ok cuts243 [⟨state243_1,exclude243_1⟩,⟨state243_6,exclude243_6⟩,⟨state243_14,exclude243_14⟩] 0x624228a08a28218908a28218908624228a08a28218908624228a08524224a08928214908928228a08302024a08928214908524224a08928214908524224a08222030108a02030108a08228208222028a08908224208302024a0822201040e000208880222010d0a000110d08222040022000008880c04228080c04228080c08210d08c0422040c434210d08a28208c0ca28210d08928204c0c92821040c434240038838230108a02030108a020 (by decide +kernel)

def state243_22 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,0x3333333333330000333333333333000033333333333300003333333333330000,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_22 : Impossible true (goalAt 243) 6 state243_22.toFinset :=
  node_ok cuts243 [⟨state243_4,exclude243_4⟩,⟨state243_7,exclude243_7⟩,⟨state243_17,exclude243_17⟩] 0x602030208c08218080602030208c08218080a28230208624228a08624228a08a28218908624228a08a28218908928230208524224a08928228a08302024a08524224a08928214908524224a08928214908222030208602030208a08228208222028a08908224208302024a0822202040e000208880222020e0a000120e08222040022000008880c04220e08c0821040c838220e08a28208c0c838220e08928204c0c83822040c83824003c4342 (by decide +kernel)

def state243_23 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0x3333333333330000333333333333000033333333333300003333333333330000,input 4,input 5,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_23 : Impossible true (goalAt 243) 6 state243_23.toFinset :=
  node_ok cuts243 [⟨state243_10,exclude243_10⟩,⟨state243_12,exclude243_12⟩,⟨state243_19,exclude243_19⟩] 0x838228a08212020e08838224a08111020e08434220e08838210d08838230208434220e08212020e08838208480624228a08a28218908a28230208624228a08301028a08a2820c040928228a08302024a08524224a08928214908928230208524224a08302024a0892820c080212020e08212020e08a08228208222028a08908224208302024a0822203010a00023010822203020a000130208222040022000008880a02030108c0824003c6020 (by decide +kernel)

def state243_24 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,input 4,input 5,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_24 : Impossible true (goalAt 243) 7 state243_24.toFinset :=
  node_ok cuts243 [⟨state243_8,exclude243_8⟩,⟨state243_15,exclude243_15⟩,⟨state243_20,exclude243_20⟩,⟨state243_21,exclude243_21⟩,⟨state243_22,exclude243_22⟩,⟨state243_23,exclude243_23⟩] 0x4003cc04218080c04240044a02030208c08280014c04230208c0824003ca0201808060204003c810310d08434240038c04220e08838280010810320e0883824003cc04210d08434240044410320e08838240038c08210d08c0828000c410310d08434240038c08220e08838240040230320e08838240040a28208480a28240040230308480212040040a28220e08838240034130320e08838240034928204440928240034130304440111040034928220e08838240040a02018908624240040c04228a08a28240040a02028a08a28240040c04218908624240040602028a08a28240040c08218908c08240040602018908624240040c08228a08a28240034901014908524240034c04224a08928240034901024a08928240034c04214908524240034501024a08928240034c08214908c08240034501014908524240034c08224a08928240034301024a08928240034a2820c080a2824003430100c080302040034a28224a0892824003ca02008880222040020c04240020c04240020a02080008a0204003cc04208880c04240020602008880222040020c08240020c08240020602080004602040020c08208880c08240038212008880212040020838240020838240020212080000212040038838208880838240034301004840a08240034a28208880a08240034301008880222040034a28204840a282400343020088809082400349282048409082400343020048403020400349282088809282 (by decide +kernel)

def state243_25 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_25 : Impossible true (goalAt 243) 8 state243_25.toFinset :=
  node_ok cuts243 [⟨state243_24,exclude243_24⟩] 0x40024c24218080c24240018a02030a08c28240028c24230a08c28240018a02018080602040034c24208880c24240034c04040034c04040034c24240028c04240034c04008880c04240034c28208880c28240034c08040034c08040034c2824001cc08240034c08008880c08240015000504840121040014301008880222040015000d08880222040014301004840121040011000408880222040010302004840302040011000d04840121040010302008880222040035000d40022000040035000008880222040035000d08880222040035000040035000040024830310d0843424002cc24220e08838240028830320e08838240024c24210d08434240018430320e0883824002cc28210d08c2824001c430310d08434240018c28220e08838240035000d20600818040034222020e08838240035000c20e08838240034222020600818240015000520e08838240014301008480212040015000c08480212040014301020e08838240011000420e08838240010302004440302040011000c04440111040010302020e08838240021000820e0883824002d000108480212040021000c0848021204002d000120e08838240014a0200c040a02040014c24240014c24240014a02040028a02040014c2420c040c2424001460200c040602040014c28240014c2824001460204001c602040014c2820c040c28240011000440010a2824001090100c080302040010c24240010c24240010901040028901040010c2420c080c2424001050100c080302040010c28240010c2824001050104001c501040010c2820c080c2824001030104001430104001100040c080302040011000440011000440011000440014928240024a0204000ca02040020c24240020c24240020a02040028a02040024c2424000cc24240018602040008602040020c28240020c2824002060204001c602040018c28240008c282 (by decide +kernel)

def state243_26 : List Sig := roots 243
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_26 : Impossible true (goalAt 243) 9 state243_26.toFinset :=
  node_ok cuts243 [⟨state243_25,exclude243_25⟩] 0x4000cc24218080c2424000ca02030a08c2824000cc24230a08c2824000ca0201808060204000ca0201890862424000cc24228a08a2824000ca02028a08a2824000cc24218908624240008602028a08a28240008c28218908c28240008602018908624240008c28228a08a2824000c90101490852424000cc24224a0892824000c901024a0892824000cc24214908524240008501024a08928240008c28214908c28240008501014908524240008c28224a08928240014301024a08928240010a2820c080a2828000030100c080302040010a28224a08928240000c24208880c24240000c04040000c04040000c2424000cc04240000c04008880c04240000c28208880c28240000c08040000c08040000c28240008c08240000c08008880c08240000a28204840a28240000a08008880a08040000a28208880a08240000a08004840a0824000092820888092824000090800484090804000092820484090824000090800888090824000c830310d0843424000cc24220e0883824000c830320e0883824000cc24210d08434240008430320e08838240008c28210d08c28240008430310d08434240008c28220e08838240004230320e08838240004a28208480a28240004230308480212040004a28220e08838240004130320e08838240004928204440928240004130304440111040004928220e08838240001000020600818040000222020e08838240001000120e088382400002220206008182 (by decide +kernel)

theorem lower243 : Claim 243 10 :=
  fromSearch 68 (by decide +kernel) exclude243_26


open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

def smallCircuit : Circuit := ⟨[⟨.or, [0, 7]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [9, 11]⟩, ⟨.and, [4, 5]⟩, ⟨.and, [12, 7]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [19, 17]⟩], 20⟩

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


def lowRow (i : Fin 8) : Row := Fin.ofNat 256 (1 <<< ([4, 4, 6, 7, 0, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 256 ((1 <<< i.val) ||| (1 <<< ([4, 4, 6, 7, 0, 0, 0, 0] : List Nat).getD i.val 0))

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
  (ruleFor 255 lower243 none (by decide +kernel)).property 11 eightInputs
    (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_32353_aux

open PEqualNP.Outside.L_meta_32353_aux in
theorem PEqualNP.Outside.L_meta_32353 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true))  := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct

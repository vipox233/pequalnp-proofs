import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31215_aux


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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)


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

theorem lower248 : Claim 248 6 :=
  fromLift 6 16 859197440 lower232 (by decide +kernel)

theorem lower234 : Claim 234 6 :=
  fromLift 6 2 856707152 lower232 (by decide +kernel)

theorem lower184 : Claim 184 5 :=
  fromLift 5 16 808931328 lower168 (by decide +kernel)

theorem lower186 : Claim 186 6 :=
  fromLift 6 2 806441024 lower184 (by decide +kernel)

def cuts120 : Cuts (goalAt 120) := []

def state120_0 : List Sig := roots 120
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude120_0 : Impossible true (goalAt 120) 3 state120_0.toFinset :=
  node_ok cuts120 [] 0x1c0c05818140c050301c0c070601c18048181410070601c18050600e0c068601a18038301210068601a18048601a18070600e0c06860 (by decide +kernel)

theorem lower120 : Claim 120 4 :=
  fromSearch 53891072 (by decide +kernel) exclude120_0

def cuts114 : Cuts (goalAt 114) := []

def state114_0 : List Sig := roots 114
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude114_0 : Impossible true (goalAt 114) 3 state114_0.toFinset :=
  node_ok cuts114 [] 0x1c0c062421890850301c0c070601c18012421490870601c18050600c8c06260189803230189086260189801230189807060141086260 (by decide +kernel)

theorem lower114 : Claim 114 4 :=
  fromSearch 68223040 (by decide +kernel) exclude114_0

def cuts106 : Cuts (goalAt 106) := []

def state106_0 : List Sig := roots 106
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude106_0 : Impossible true (goalAt 106) 3 state106_0.toFinset :=
  node_ok cuts106 [] 0xa82862421890822420a08068601a18028601290868601a180486008880626018980226018908626018980280a189806860121086260 (by decide +kernel)

theorem lower106 : Claim 106 4 :=
  fromSearch 51400784 (by decide +kernel) exclude106_0

def cuts90 : Cuts (goalAt 90) := []

def state90_0 : List Sig := roots 90
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude90_0 : Impossible true (goalAt 90) 3 state90_0.toFinset :=
  node_ok cuts90 [] 0x160605242149084818160604a42129085018129085242048284a42068605818120281a18149085040141085042129084840121084842 (by decide +kernel)

theorem lower90 : Claim 90 4 :=
  fromSearch 50421824 (by decide +kernel) exclude90_0

def cuts58 : Cuts (goalAt 58) := []

def state58_0 : List Sig := roots 58
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude58_0 : Impossible true (goalAt 58) 3 state58_0.toFinset :=
  node_ok cuts58 [] 0xe0602a0a0a06028180e06038300e0c0220a0a08038300e0c028300686032300c8c01a180888032300c8c022300c8c03830068603230 (by decide +kernel)

theorem lower58 : Claim 58 4 :=
  fromSearch 1134656 (by decide +kernel) exclude58_0

def rule122_0 : {c : Cut // CutGood (goalAt 122) c} :=
  ruleFor 122 lower120 none (by decide +kernel)

def rule122_1 : {c : Cut // CutGood (goalAt 122) c} :=
  ruleFor 122 lower114 none (by decide +kernel)

def rule122_2 : {c : Cut // CutGood (goalAt 122) c} :=
  ruleFor 122 lower106 none (by decide +kernel)

def rule122_3 : {c : Cut // CutGood (goalAt 122) c} :=
  ruleFor 122 lower90 none (by decide +kernel)

def rule122_4 : {c : Cut // CutGood (goalAt 122) c} :=
  ruleFor 122 lower58 none (by decide +kernel)

def cuts122 : Cuts (goalAt 122) := [rule122_0,rule122_1,rule122_2,rule122_3,rule122_4]

def state122_0 : List Sig := [0xffccffcc00000000ffccffcc00000000ffccffcc00000000ffccffcc,input 1,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_0 : Impossible true (goalAt 122) 4 state122_0.toFinset :=
  node_ok cuts122 [] 0x140c070601c18048180e0c068601a18038301a18070600e0c068600c8c06260189803230189807060149086260189806860121086260089086242189085030149087060149087060121806860129086860068606260189086260 (by decide +kernel)

def state122_1 : List Sig := [0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_1 : Impossible true (goalAt 122) 5 state122_1.toFinset :=
  node_ok cuts122 [⟨state122_0,exclude122_0⟩] 0x7030189086242140c070301c18070601206052421c1807060141805818129084a421c0c04a42189083818129084a421c180120a1c1806860068607030120287030189083818189081a18149087060149087060129081a181210862601606070301606070301890a0000189090003149087060149087060 (by decide +kernel)

def state122_2 : List Sig := [0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 1,input 4,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_2 : Impossible true (goalAt 122) 5 state122_2.toFinset :=
  node_ok cuts122 [] 0x7030189086242140c038301a18068600e0c04a421a18068601218068601490838301a1806860129084a421a18070301490852420490852421890838181490870600c8c07030128283230189083230189081a181290868601290868601490832301410862601c0c048081c0c04808189082808189082808 (by decide +kernel)

def state122_3 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 1,input 5,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_3 : Impossible true (goalAt 122) 5 state122_3.toFinset :=
  node_ok cuts122 [] 0x70301c18070601206052421c18070601490850401c18070601410038301a18068600e0c068601c18038301a1804a421a18068601290848401a18068601210070301890862420890838180c8c06260189803230189807060149086260189806860129086260189086260048c01a181c0c058181c0c05818 (by decide +kernel)

def state122_4 : List Sig := [0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc,input 1,input 6,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_4 : Impossible true (goalAt 122) 4 state122_4.toFinset :=
  node_ok cuts122 [] 0x1c0c062421890850301290868601a18048600e0c068601a1803830189086260189801a181898068601210862600c8c062601898032301418070601c18052421a18038301a18070601206070601c1807030189805042189807060 (by decide +kernel)

def state122_5 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 1,input 6,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_5 : Impossible true (goalAt 122) 5 state122_5.toFinset :=
  node_ok cuts122 [⟨state122_4,exclude122_4⟩] 0x38181890862420890838181890862420e06052421c1807060141801a0a1c18070600490a00001c1807060400084a421a18068601218068601c18038301a18038301a18068600e0c038301a18068600e0c07030189086260189803818189807060141086260189806860121086260128286260089803230 (by decide +kernel)

def state122_6 : List Sig := [0xffffff00ffffff000000000000000000ffffff00ffffff00,input 3,input 4,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_6 : Impossible true (goalAt 122) 4 state122_6.toFinset :=
  node_ok cuts122 [] 0x189086260189801a181898070601410862601898068601210862601490870601c18050601290868601a18048601a18070600e0c06860140c062421c0c062420c8c062600c8c062601206070601c0c070600e0c068600e0c06860 (by decide +kernel)

def state122_7 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,input 4,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_7 : Impossible true (goalAt 122) 5 state122_7.toFinset :=
  node_ok cuts122 [⟨state122_6,exclude122_6⟩] 0x7030189086242140c032301898062600c8c062421898062600686062600c8c032301898062600e0c01a181898062600c8c032301898070301282870301206038181890828181890870600e0c070301406038300e06062420e0c062420682838300a0c068601c0c200001c0c100040e06062420e0606242 (by decide +kernel)

def state122_8 : List Sig := [0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 3,input 5,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_8 : Impossible true (goalAt 122) 5 state122_8.toFinset :=
  node_ok cuts122 [] 0x70301c18070601206052421c18070601490852421c18070601490832301898062600c8c062601c1805042189801a181898062600686062601a1801a181898012101898062600484070301606070300e06062420e0c068601a18038301a18070600e0c068600e0606860121804a421c0c050101c0c05010 (by decide +kernel)

def state122_9 : List Sig := [0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00,input 3,input 6,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_9 : Impossible true (goalAt 122) 5 state122_9.toFinset :=
  node_ok cuts122 [] 0x38181890862420e06022021890862420880852421c18070601418058181c18070601206012021c18070600480862421898062600686062601c18050421898032301898062600c8c062601a18048421898032301898062600c8c070301290868601a18048601a18070600682868601606068600a1803830 (by decide +kernel)

def state122_10 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,input 4,input 5,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_10 : Impossible true (goalAt 122) 4 state122_10.toFinset :=
  node_ok cuts122 [] 0xe0c068601a18038301210868601a18048421a18070600e0c068601c0c062421890850301c0c070601c18012401490870601c18050600c8c062601898032301898048421a18062600686062601898062421898050421c1806260 (by decide +kernel)

def state122_11 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 1,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_11 : Impossible true (goalAt 122) 5 state122_11.toFinset :=
  node_ok cuts122 [⟨state122_10,exclude122_10⟩] 0x38301a18068600e0c04a421a18068601290868601c18038301a1804a421a18068601290832301898062600c8c062601a1804842189801a181898062600686062601c1803230189820000189806260400007030160605030140c062421c0c070601c1804a0a0e06070601418052421c0c04a0a1c0c04a0a (by decide +kernel)

def state122_12 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 1,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_12 : Impossible true (goalAt 122) 5 state122_12.toFinset :=
  node_ok cuts122 [] 0x7030189086242140c02a0a1890862420a8284a421a18068601218038301a18068600e0c068601c18038301a18028201a18068600a08062421898062600686062601a18048421898032301898062600c8c062601c1805042189802220189806260088804a0a1490870601c18050601c0c07060120601a0a (by decide +kernel)

def state122_13 : List Sig := [0xff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000,input 5,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_13 : Impossible true (goalAt 122) 4 state122_13.toFinset :=
  node_ok cuts122 [] 0x1c0c070601c18048181490870601c18050601898070601410862600c8c06260189803230189086260189801a181c0c062421890850301a18038301c18068601898048421898068600e0c068601a18038301218068601a1804a42 (by decide +kernel)

def state122_14 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 1,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_14 : Impossible true (goalAt 122) 5 state122_14.toFinset :=
  node_ok cuts122 [⟨state122_13,exclude122_13⟩] 0x70301c18070600682852421c1807060141801a0a1c18070600682868601c18038301a18038301a18068600e0c04a421a18068601218200001a18068604000462601c18050421898062601a18048421898032301898062600c8c06242189806260068601a181898062600686058181c0c06242140c03818 (by decide +kernel)

def state122_15 : List Sig := roots 122
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_15 : Impossible true (goalAt 122) 6 state122_15.toFinset :=
  node_ok cuts122 [⟨state122_1,exclude122_1⟩,⟨state122_2,exclude122_2⟩,⟨state122_3,exclude122_3⟩,⟨state122_5,exclude122_5⟩,⟨state122_7,exclude122_7⟩,⟨state122_8,exclude122_8⟩,⟨state122_9,exclude122_9⟩,⟨state122_11,exclude122_11⟩,⟨state122_12,exclude122_12⟩,⟨state122_14,exclude122_14⟩] 0x4001070300e06070304000c58181890862428002470301890862424000c58180e0605030400107030068287030400084a0a1c18070608002070301c1807060400084a0a0682848184000c38181490852424000862421c18070608001c38181c18070604000862421490850604001058180e0c038304000470301a18068608001858181a18068604000470300e0c038304000c3818129084a424000462421a18068608001438181a1806860400046242129084860400081a0a1a18068604000470600e0c07060800101a0a0e0c038304000470601a1806860400104a0a0c8c032304000070301898062608000c4a0a1898062604000070300c8c032304000c6242068606242400003818189806260800086242189806260400003818068601a184000852421898062604000070600c8c070608000452420c8c05042400007060189806260400044a42189806260400006860068606860800004a42068604842400006860189806260 (by decide +kernel)

theorem lower122 : Claim 122 7 :=
  fromSearch 51466304 (by decide +kernel) exclude122_15

theorem lower170 : Claim 170 5 :=
  fromLift 5 2 806375504 lower168 (by decide +kernel)

def cuts154 : Cuts (goalAt 154) := []

def state154_0 : List Sig := roots 154
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude154_0 : Impossible true (goalAt 154) 3 state154_0.toFinset :=
  node_ok cuts154 [] 0x26060928224a088818260608a8222a08901822a089282048288a82068609818220281a1824a08908024208908222a088880222088882 (by decide +kernel)

theorem lower154 : Claim 154 4 :=
  fromSearch 805400640 (by decide +kernel) exclude154_0

theorem lower218 : Claim 218 5 :=
  fromLift 5 64 855728192 lower154 (by decide +kernel)

def cuts240 : Cuts (goalAt 240) := []

def state240_0 : List Sig := roots 240
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude240_0 : Impossible true (goalAt 240) 3 state240_0.toFinset :=
  node_ok cuts240 [] 0x38180b03028180a06038180e0c038300903028200e0c038300a0c01c180d0c034300706024200d0c03430090c034300e0c01c180d0c0 (by decide +kernel)

theorem lower240 : Claim 240 4 :=
  fromSearch 1148583936 (by decide +kernel) exclude240_0

theorem lower242 : Claim 242 5 :=
  fromLift 5 2 1141964864 lower240 (by decide +kernel)

def rule250_0 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower248 none (by decide +kernel)

def rule250_1 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower234 none (by decide +kernel)

def rule250_2 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower232 none (by decide +kernel)

def rule250_3 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower184 none (by decide +kernel)

def rule250_4 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower186 none (by decide +kernel)

def rule250_5 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower122 none (by decide +kernel)

def rule250_6 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower170 none (by decide +kernel)

def rule250_7 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower218 none (by decide +kernel)

def rule250_8 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower240 none (by decide +kernel)

def rule250_9 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower122 (some (1,input 1,input 3)) (by decide +kernel)

def rule250_10 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower242 none (by decide +kernel)

def rule250_11 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower114 none (by decide +kernel)

def rule250_12 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower122 (some (1,input 1,input 5)) (by decide +kernel)

def rule250_13 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower90 none (by decide +kernel)

def rule250_14 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower122 (some (1,input 3,input 4)) (by decide +kernel)

def rule250_15 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower168 none (by decide +kernel)

def rule250_16 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower154 none (by decide +kernel)

def rule250_17 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower122 (some (1,input 3,input 5)) (by decide +kernel)

def rule250_18 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower122 (some (1,input 3,input 6)) (by decide +kernel)

def rule250_19 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower122 (some (1,input 4,input 5)) (by decide +kernel)

def rule250_20 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower122 (some (1,input 5,input 6)) (by decide +kernel)

def cuts250 : Cuts (goalAt 250) := [rule250_0,rule250_1,rule250_2,rule250_3,rule250_4,rule250_5,rule250_6,rule250_7,rule250_8,rule250_9,rule250_10,rule250_11,rule250_12,rule250_13,rule250_14,rule250_15,rule250_16,rule250_17,rule250_18,rule250_19,rule250_20]

def state250_0 : List Sig := [0xffffffffffccffccffffffffffccffccffffffffffccffccffffffffffccffcc,input 5,input 1,input 3,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_0 : Impossible true (goalAt 250) 6 state250_0.toFinset :=
  node_ok cuts250 [] 0xe0602c0c0a06028180706034b08d2c21c180928234b08d2c224b08d2c238b08706034b08d0c034b08d2c234300686032b08cac21a1808a8232b08cac222b08cac234b08383032b08cac238b08686032b08c8c018980e0602202862600c8c0626018980323034b08d0c034b08d0c032b08686032308c8c238b08626038308e0c204840e06038b08e2c218b08a28238b08e2c228b08e0c03818090103818090101c0c050101c0c05010 (by decide +kernel)

def state250_1 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 3,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_1 : Impossible true (goalAt 250) 6 state250_1.toFinset :=
  node_ok cuts250 [] 0x38180b03028180a0601c180d2c234b08706024a08d2c234b0892c234b08e2c21c180d2c234300d2c234b08d0c012908cac232b08e06022a08cac232b088ac232b08d2c204828cac232300cac238b08220a32b081a1832b08c8c23230862603818098181898032301898062600c8c0d2c234300d2c234300e2c218980e0c2383081a1818980626040028e06038b08e2c218b08a28238b08e2c228b08e0c0381809818381801a181c0c058181c0c01a18 (by decide +kernel)

def state250_2 : List Sig := [0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 5,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 1,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_2 : Impossible true (goalAt 250) 6 state250_2.toFinset :=
  node_ok cuts250 [] 0x38180b03028180a0601c180d2c234b08706024a08d2c234b0892c234b0870601c180d2c234b08cac21c180cac206860e06022028e06006860703012028703034b08d0c034b08d0c0189801a180c860220a06860cac206860c8c23230868603818098181a18038301a18068600e0c0d2c234300d2c23430038181a180686012180cac232300cac240000e06026060e0600e06070301606070300e060e2c238180cac232b084ac222a08cac232b088ac2 (by decide +kernel)

def state250_3 : List Sig := [0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 1,input 3,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_3 : Impossible true (goalAt 250) 7 state250_3.toFinset :=
  node_ok cuts250 [⟨state250_0,exclude250_0⟩,⟨state250_1,exclude250_1⟩,⟨state250_2,exclude250_2⟩] 0xe0601c0c0e0602c0c100032c0c0e06040024a0602c0c0703028180e06018908e06026060e2c238b08e06038b08e2c226060624218b08703028a08a28216060e2c238b08703038b08e2c216060a28228b08b0301c180706038180d2c234b08b03034b08d2c23818070601c180703024a08928212828d2c234b08703034b08d2c212828928224b08381834b08d2c238b08706038b0838181c180706038b08d2c234b089818129084a4238180cac232b08981832b08cac2381804a4238180581822a088a821c0c0cac232b08581832b08cac21c0c08a8222b08381832b08cac238b09000838b08381880008381838b08cac232b081a0a32b08cac234b09000234b081a0a40008120a34b08cac232b09000040000c8c0228281a1806860e06040000e06022829000922028e06006860e060128281a1806860703040000703012829000312028703006860703038b081a1838b08e0c040000e0c038b0a000138b08e0c006860e0c034b09000234b08d0c006860d0c034b081a1834b08d0c040000d0c032b09000a32b090000068601a1840001000032309000040028626026061000526060e06040020e06026061000926060e06040014e0601606100041606070304000c703016061000316060703040010703038b09000738b08e0c040020e0c038b0a000038b08e0c04001ce0c034b09000134b08d0c040008d0c034b09000234b08d0c040004d0c0 (by decide +kernel)

def state250_4 : List Sig := [0xffff3300ffff3300ffff3300ffff3300ffff3300ffff3300ffff3300ffff3300,input 1,input 3,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_4 : Impossible true (goalAt 250) 6 state250_4.toFinset :=
  node_ok cuts250 [] 0x38180703038180b0304002cb03038181000b28180b0301c0c0a06038180624238180881838b08e2c238180e2c238b0888181890862c21c0c0a28228a08481838b08e2c21c0c0e2c238b08481828a08a2c2220604a4212908e06032b08cac222060cac232b08e06012908e060120608a8222a08703032b08cac212060cac232b08703022a088ac20a060cac232b08e2c20e0c0e2c20a06038300e0c0e2c232b08cac206828cac232b08d2c20e0c0d2c20682838300e0c0d2c232b08cac222828626018980e06040008e06022829000b22828e0601898062601282832300c8c070301898062601282862601898070300c8c0323038b081a1838b08e0c018980e0c038b08626038308e0c006860e0c232b08626032b08383006860cac032b081a1832b08383018980626034b08626034b08d0c00c8c0d0c034b08323034308d0c018980d0c22c0c070601c180e06034b08d2c22c0c0d2c234b08e0601c18070601c0c0928224a084a0a34b08d2c21c0c0d2c234b084a0a24a0892c20a060d2c234b08e2c21c180e2c20a06070601c180e2c234b08d2c2 (by decide +kernel)

def state250_5 : List Sig := [0xffffffff33003300ffffffff33003300ffffffff33003300ffffffff33003300,input 5,input 1,input 3,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_5 : Impossible true (goalAt 250) 6 state250_5.toFinset :=
  node_ok cuts250 [] 0xe0602c0c0a06028180706034b08d2c21c180928234b08d2c224b08d2c21c180706034b08d2c21c180706034b08686032b08cac21a1808a8232b08cac222b08cac234b08383032b08cac21a180686032b08cac232300686032b086260381808a0a1898032301898062600c8c0d2c234300d0c234308cac232b00cac2189803a181898062600e060121018980626006860e06026060e0600e06070301606070300e060e2c23818090103818090101c0c050101c0c05010 (by decide +kernel)

def state250_6 : List Sig := [0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 5,0x3300330033003300330033003300330033003300330033003300330033003300,input 1,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_6 : Impossible true (goalAt 250) 6 state250_6.toFinset :=
  node_ok cuts250 [] 0xe0602c0c0a06028180706034b08d2c21c180928234b08d2c224b08d2c21c180706034b08d2c232b08706032b086260381808a0a1898032301898062600c8c0d2c234300d0c234308121018980626012980cac232b00cac20484068603818098181a18038301a18068600e0c0686034b08383034b081a180e06068601a180486032300e06026060e0600e06070301606070300e060e2c238180cac232b084ac222a08cac232b088ac2 (by decide +kernel)

def state250_7 : List Sig := [0x3300330033003300330033003300330033003300330033003300330033003300,input 1,input 3,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_7 : Impossible true (goalAt 250) 7 state250_7.toFinset :=
  node_ok cuts250 [⟨state250_4,exclude250_4⟩,⟨state250_5,exclude250_5⟩,⟨state250_6,exclude250_6⟩] 0xe0601c0c0e0602c0c100032c0c0e0604002ca0602c0c0703028180e06018908e06026060e2c238b08e06038b08e2c226060624218b08703028a08a28216060e2c238b08703038b08e2c216060a28228b08b0301c180706038180d2c234b08b03034b08d2c23818070601c180703024a08928212828d2c234b08703034b08d2c212828928224b08381834b08d2c238b08706038b0838181c180706038b08d2c234b089818129084a4238180cac232b08981832b08cac2381804a4238180581822a088a821c0c0cac232b08581832b08cac21c0c08a8222b08381832b08cac238b09000a38b08381880008381838b08cac232b081a0a32b08cac234b09000a34b081a0a40008120a34b08cac232b088a0a189806260381810000381808a0a4002c8a0a381806260189804a0a0c8c032301c0c06260189804a0a1898062601c0c032300c8c0e2c204840e2c238300626038300e2c218980e0c238300121038308d2c218980d2c234300323034300d2c20c8c0d0c234300626034309000040000cac032b09000a32b09000018980626026061000526060e06040028e06026061000b26060e06040014e0601606100041606070304002870301606100031606070304001070300e06100070e060e2c240028e2c20e06200010e060e2c240028e2c240029000140004d2c240028d2c240029000280000d2c240004d2c240001000032301000a400001a18 (by decide +kernel)

def state250_8 : List Sig := [0xff00ff00cc00cc00ff00ff00cc00cc00ff00ff00cc00cc00ff00ff00cc00cc,input 3,input 1,input 5,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_8 : Impossible true (goalAt 250) 6 state250_8.toFinset :=
  node_ok cuts250 [] 0xe0602c0c0a06028180706034b08d2c21c180928234b08d2c224b08d2c238b08706034b08e06038b08e2c218b08a28238b08e2c228b08626038180880a1898032301898062600c8c0d2c234300d2c234300e2c218980e0c238308cac0323001a1832300484032300c8c038180888032300c8c022300c8c034b081a0a34b08c8c038b08381838b08e06026060e06026060703016060703016060d2c234300d2c234300e2c238300e2c20e060626006860626006860cac2 (by decide +kernel)

def state250_9 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 1,input 5,input 3,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_9 : Impossible true (goalAt 250) 7 state250_9.toFinset :=
  node_ok cuts250 [⟨state250_1,exclude250_1⟩,⟨state250_0,exclude250_0⟩,⟨state250_8,exclude250_8⟩] 0xe0601c0c0e0602c0c100032c0c0e06040030a0602c0c0703028180b0301c180706038180d2c234b08b03034b08d2c23818070601c180703024a08928212828d2c234b08703034b08d2c212828928224b09000234b08d2c238b08706038b0900021c180706038b08d2c234b09000234300d0c040004d2c234b09000234b08d2c240004d0c03430098181a180686038180cac232b08981832b08cac23818068601a180581822a088a821c0c0cac232b08581832b08cac21c0c08a8222b081a0a32b08cac234b08383034b081a0a0e0c0383034b08cac232b082a0a32b08cac238b08686038b082a0a1a180686038b08cac232b0a000232300c8c040028cac232b0a000132b08cac240028c8c032300e06018908e06026060e2c238b08e06038b08e2c226060624218b08703028a08a28216060e2c238b08703038b08e2c216060a28228b09000040000e0c022828626018980e06040000e06022829000c22828e0601898062601282832300c8c070301898062601282862601898070300c8c0323034b08626034b08d0c00c8c0d0c034b08323034b08d0c018980d0c032b08626032b08c8c040000c8c032b0a000032b08c8c018980c8c038b09000738b0900001898062604000100003830900004001c1a1838181000538180981840030981838181000c3818098184001498181c0c100041c0c058184000c58181c0c100031c0c05818400105818 (by decide +kernel)

def state250_10 : List Sig := [0xff33ff33ff00ff00ff33ff33ff00ff00ff33ff33ff00ff00ff33ff33ff00ff00,input 3,input 1,input 5,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_10 : Impossible true (goalAt 250) 6 state250_10.toFinset :=
  node_ok cuts250 [] 0xe0602c0c0a06028180706034b08d2c21c180928234b08d2c224b08d2c238b08706034b08e06038b08e2c218b08a28238b08e2c228b081a1838180880a381801a181c0c0480a1c0c0d2c234300d0c234308e2c238b00e2c2068606a601a1801a181a18012100686062601898068603818098181a18038301a18068600e0c0686034b08383034b08381838b08686038b08cac23818090103818090101c0c050101c0c050101c180d2c21c180d2c238300e2c20e060e2c2 (by decide +kernel)

def state250_11 : List Sig := [0x3333333300000000333333330000000033333333000000003333333300000000,input 1,input 5,input 3,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_11 : Impossible true (goalAt 250) 7 state250_11.toFinset :=
  node_ok cuts250 [⟨state250_10,exclude250_10⟩] 0xe0601c0c0e0602c0c100032c0c0e06040034a0602c0c0703028180b0301c180706038180d2c234b08b03034b08d2c23818070601c180703024a08928212828d2c234b08703034b08d2c212828928224b09000234b08d2c238b08706038b0900021c180706038b08d2c234b0898181a180686038180cac232b08981832b08cac23818068601a180581822a088a821c0c0cac232b08581832b08cac21c0c08a8222b081a0a32b08cac234b08383034b081a0a0e0c0383034b08cac232b082a0a32b08cac238b08686038b082a0a1a180686038b08cac232b08e06018908e06026060e2c238b08e06038b08e2c226060624218b08703028a08a28216060e2c238b08703038b08e2c216060a28228b088a0a068601a18381810000381808a0a40034880a381801a18381804a0a068601a181c0c100001c0c04a0a4000c480a1c0c01a181c0c0d2c240008d2c2343001a1834300d2c206860d0c234301000034308cac204840cac2323001a1832300cac206860c8c232300121032309000040000e2c038b09000738b090000068601a183818100053818098184001c981838181000d3818098184001498181c0c100041c0c058184001c58181c0c100031c0c058184001058181c18100011c180d2c240008d2c21c18100021c180d2c240004d2c21a181000a1a180cac24001ccac21a18200001a180cac240028cac2400010000383010007400006260 (by decide +kernel)

def state250_12 : List Sig := [0xffffffffffffffffffffffffffffffff0000000000000000ffffff00ffffff00,input 7,input 3,input 4,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_12 : Impossible true (goalAt 250) 5 state250_12.toFinset :=
  node_ok cuts250 [] 0x624238b08e2c218908624238b08e2c218908e2c238300e0c238308d2c234300d0c234308cac232300c8c23230862602c0c0880a1898062600c8c0323018980d2c238b08706034b08706034b08d2c21c180706034b08d2c21c180cac238b08686032b08cac234b08383032b08686032b08cac21a180686032b08cac21a180a060 (by decide +kernel)

def state250_13 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,0xffffff00ffffff00,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_13 : Impossible true (goalAt 250) 4 state250_13.toFinset :=
  node_ok cuts250 [] 0x18980e0c2383081a1834308e0c21c180d0c21c180d0c234308626032308e0c21a180c8c232308d0c20e0c0c8c21a180c8c2323086260140c0e0c21c0c0e0c212060d0c21c0c0d0c20e0c0c8c20e0c0c8c20c8c062600c8c06260 (by decide +kernel)

def state250_14 : List Sig := [0xffffff00ffffff00,input 7,input 3,input 4,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_14 : Impossible true (goalAt 250) 5 state250_14.toFinset :=
  node_ok cuts250 [⟨state250_13,exclude250_13⟩] 0xa06038b08e2c218a08e2c238300e0c238308d2c234300d0c234308cac232300c8c232308626028182000018980d2c238b08706034b08706034b08d2c21c180cac238b08686032b08cac234b08383032b08686032b08cac21a180503038b08703038b08323018980323018980481834b08703034b08383032b08383032b08b030 (by decide +kernel)

def state250_15 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,0xffffff00ffffff000000000000000000ffffff00ffffff00,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_15 : Impossible true (goalAt 250) 5 state250_15.toFinset :=
  node_ok cuts250 [⟨state250_13,exclude250_13⟩] 0x624238308e0c218a00626038308e0c206860d0c238308706034308706034308d0c21c180706034308d0c218980c8c238308686032308c8c234308383032308686032308c8c21a180686032308c8c21898050303830870303830892c0343087030343088ac032308383032308703080000880a1c0c0323018980323018980a060 (by decide +kernel)

def state250_16 : List Sig := [0xffffff00ffffff000000000000000000ffffff00ffffff00,input 3,input 4,input 1,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_16 : Impossible true (goalAt 250) 6 state250_16.toFinset :=
  node_ok cuts250 [⟨state250_12,exclude250_12⟩,⟨state250_14,exclude250_14⟩,⟨state250_15,exclude250_15⟩] 0x28180624228180981838b08e2c228180e2c238b08981818908628222828626018980a0604003ca0602282a000222028a06018980626038b081a1838b08e0c018980e0c038b08626038308e0c006860e0c234b08626034b08d0c00c8c0d0c034b08323034308d0c018980d0c232b08626032b08c8c006860c8c032b081a1832308c8c018980c8c22c0c070601c180a06034b08d2c22c0c0d2c234b08a0601c18070600e060d2c234b08e2c21c180e2c20e06070601c180e2c234b08d2c22606068601a180a06032b08cac226060cac232b08a0601a18068600e060cac232b08e2c21a180e2c20e06068601a180e2c232b08cac206828cac232b08d2c20e0c0d2c20682838300e0c0d2c232b08cac22c0c070301c0c0a06080004a0602c0c200002c0c0a0601c0c0a0600e0605818140c0e2c21c0c0e2c20e06070301c0c0e2c216060e2c20c8c070300c8c062601282862600c8c04a0a0c8c062601c0c06260068284a0a24b08d2c21c0c0d2c20682870301c0c0d2c212828d2c20e0c0703022b08cac216060cac20e0c058180e0c0cac21c0c0cac2 (by decide +kernel)

def state250_17 : List Sig := [0xffffffffffffff000000000000000000ffffffffffffff00,input 5,input 3,input 4,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_17 : Impossible true (goalAt 250) 5 state250_17.toFinset :=
  node_ok cuts250 [] 0x18980e06022028626034b08d0c034308d0c232b08c8c032308c8c238b08e0c038308e0c21c180d2c234b08706034b08e2c21c180d2c21a180cac232b08686032b08d2c20e0c0cac232b08e2c21a180cac238180e2c238b08628228180a0602c0c0e0600c8c062600c8c0626024b08d2c21c0c0d2c222b08cac20e0c0cac228b08e2c21c0c0e2c2 (by decide +kernel)

def state250_18 : List Sig := [0xffffffffffffff00ffffffffffffff00,input 5,input 3,input 4,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_18 : Impossible true (goalAt 250) 5 state250_18.toFinset :=
  node_ok cuts250 [] 0xc8c0626018980323034b08d0c034308d0c232b08c8c032308c8c238b08e0c038308e0c224a08d2c234b0892c234b08e2c21c180d2c222a08cac232b088ac232b08d2c20e0c0cac232b08e2c21a180cac228a08e2c238b08a2c228180a06038180b03018980880a18980e0601c180d2c21c180d2c21a180cac21a180cac218b08e2c238180e2c2 (by decide +kernel)

def state250_19 : List Sig := [0x3333333333333300333333333333330033333333333333003333333333333300,input 5,input 3,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_19 : Impossible true (goalAt 250) 5 state250_19.toFinset :=
  node_ok cuts250 [] 0x38180b03028180a0601c180d2c234b08706024a08d2c234b0892c034b08e2c21c180d2c21a180cac232b08686022a08cac232b088ac032b08d2c20e0c0cac232b08e2c21a180cac238180e2c238b0862c028a08e2c238b08a2c018980880a3818062600c8c0626018980323034308d0c21c180d2c232308c8c21a180cac238308e0c218980e2c2 (by decide +kernel)

def state250_20 : List Sig := [0xffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00,input 5,input 3,input 4,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_20 : Impossible true (goalAt 250) 6 state250_20.toFinset :=
  node_ok cuts250 [⟨state250_17,exclude250_17⟩,⟨state250_18,exclude250_18⟩,⟨state250_19,exclude250_19⟩] 0xe0602c0c0a06028180626038180880a1898032301898062600c8c062601c18032301898062601a1801a18189801a1818980626006862000218980626040000706038180a0301c18070301c18070601206038181c180706014180d2c21a180e0602406068600e0c068601a18038301a18070600e0c068600e06068601a180486032b08e06026060e060240c07030160605030140c0e2c23818200013818100051c0c200001c0c10004 (by decide +kernel)

def state250_21 : List Sig := [0xffffff0000000000ffffff0000000000ffffff0000000000ffffff00,input 5,input 3,input 4,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_21 : Impossible true (goalAt 250) 6 state250_21.toFinset :=
  node_ok cuts250 [] 0xe0602c0c0a06028180626038180880a1898032301898062600c8c062601c18032301898062601a1801a1818980e2c238300e0c238308706038180a0301c18070301c180706012060f2c238b08706038b0868603818090181a18038301a18068600e0c068601c18038301a180eac238b08686038b08e06038b08e2c218b08a28238b08e2c228b0898183818098183818058181c0c058181c0c01a18189801a1818980d2c234b081a0a1c180cac232b0900011a1803818 (by decide +kernel)

def state250_22 : List Sig := [0xffffff00ffffff000000000000000000ffffff00ffffff00,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,input 4,input 1,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_22 : Impossible true (goalAt 250) 6 state250_22.toFinset :=
  node_ok cuts250 [] 0x28180e2c238b08628218980a06022028626038b08e0c038308e0c21898032300c8c062601898038300686062601898032300c8c062602c0c0a0602c0c0a0600e060e2c20a060e2c234b08383028180901828180381838b08383038b081a0a0e0c0283032b08b03028180b03028180381838b08381838b08703028180b03028180503038b08703038b0832301898032301898048181c0c070301282838301406038301c0c10004 (by decide +kernel)

def state250_23 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,0xffffffffffffffffff00ff0000000000ffffffffffffffffff00ff0000000000,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_23 : Impossible true (goalAt 250) 4 state250_23.toFinset :=
  node_ok cuts250 [] 0x18980e06022028626032b08c8c032308c8c20c8c0626018980323038b08e0c038308e0c21a180cac232b08686022a08cac232b088ac232b08d2c21a180cac238180903028180a06038180e2c238b0862c228a08e2c238b08a2c2 (by decide +kernel)

def state250_24 : List Sig := [0xffffffffffffffffff00ff0000000000ffffffffffffffffff00ff0000000000,input 5,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 4,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_24 : Impossible true (goalAt 250) 5 state250_24.toFinset :=
  node_ok cuts250 [⟨state250_23,exclude250_23⟩] 0x626038180880a1898062600c8c0323018980cac232300c8c232308e2c238300e0c23830832301898062600c8c0b03038180b03038180d2c204828e2c280000e2c20e0c04a0a0e0c068301a180cac232b08686032b08e2c21a180cac222a08cac232b088ac238180e2c238b0862c228a08e2c238b08a2c238180b03028180a060 (by decide +kernel)

def state250_25 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,0xffffffffffffffffffffffffffffffffff00ff0000000000ff00ff0000000000,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_25 : Impossible true (goalAt 250) 4 state250_25.toFinset :=
  node_ok cuts250 [] 0x38180383028180a0600c8c0626018980323032b08c8c032308c8c218980e06022028626038b08e0c038308e0c222a08cac232b088ac21a180cac232b08706032b08d2c21c180cac228a08e2c238b08a2c238180e2c238b0862c2 (by decide +kernel)

def state250_26 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff0000000000ff00ff0000000000,input 5,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 4,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_26 : Impossible true (goalAt 250) 5 state250_26.toFinset :=
  node_ok cuts250 [⟨state250_25,exclude250_25⟩] 0xe0600e0c0a0602818032301898062600c8c062600c8c0323018980cac232300c8c232308e2c238300e0c238308626038180880a18980703012828703012060d2c204828e2c280000e2c20e0c0e0600e0c0e06022a08cac232b088ac232b08e2c212180cac21a180cac232b08e06028a08e2c238b08a2c238180e2c238b0862c2 (by decide +kernel)

def state250_27 : List Sig := [0xffccffccccccccccffccffccccccccccffccffccccccccccffccffcccccccccc,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_27 : Impossible true (goalAt 250) 4 state250_27.toFinset :=
  node_ok cuts250 [] 0x38180903028180a0601c180cac232b08706022a08cac232b088ac232b08d2c21c180cac238180e2c238b0862c228a08e2c238b08a2c218980e0602202862600c8c0626018980323032b08c8c032308c8c238b08e0c038308e0c2 (by decide +kernel)

def state250_28 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_28 : Impossible true (goalAt 250) 5 state250_28.toFinset :=
  node_ok cuts250 [⟨state250_23,exclude250_23⟩,⟨state250_25,exclude250_25⟩,⟨state250_27,exclude250_27⟩] 0x38180903028180a06018980e0602202862600c8c0626018980323032b08c8c032308c8c218980383080008626038b08e0c038308e0c21c180cac232b08706022a08cac232b088ac232b08d2c21c180cac20e0c0e06080004e0600e0c050308000038301a1802a0a38180e2c238b0862c228a08e2c238b08a2c2 (by decide +kernel)

def state250_29 : List Sig := [0xffccffccccccccccffccffccccccccccffccffccccccccccffccffcccccccccc,input 5,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_29 : Impossible true (goalAt 250) 5 state250_29.toFinset :=
  node_ok cuts250 [⟨state250_27,exclude250_27⟩] 0xe0602c0c0a06028180b03038180b03038180703012828703012060d2c204828e2c280000e2c212908cac232b08e06022a08cac232b088ac232b08e2c212180cac238180e2c238b0862c228a08e2c238b08a2c218980e0602202862600c8c062601898032301898032300c8c0626032b08c8c032308c8c238b08e0c038308e0c2 (by decide +kernel)

def state250_30 : List Sig := [0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000,input 5,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 4,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_30 : Impossible true (goalAt 250) 6 state250_30.toFinset :=
  node_ok cuts250 [⟨state250_24,exclude250_24⟩,⟨state250_26,exclude250_26⟩,⟨state250_28,exclude250_28⟩,⟨state250_29,exclude250_29⟩] 0xe0602c0c0a06028180626038180880a1898032301898062600c8c062600c8c0323018980cac232300c8c232308e2c238300e0c23830862600e0c2000318980b03038180b03038180703012828703012060d2c204828e2c280008e2c212908cac232b08e06022a08cac232b088ac232b08e2c212180cac238180e2c238b0862c228a08e2c238b08a2c20e0c0e06080004e0600e0c070308000038304000438300e0c028301a1803818 (by decide +kernel)

def state250_31 : List Sig := [0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000,input 5,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 4,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_31 : Impossible true (goalAt 250) 6 state250_31.toFinset :=
  node_ok cuts250 [] 0x38180b03028180a06018980e0602202862600c8c062601898032301898032300c8c0626032b08c8c032308c8c2068606260189801a182c0c0e0602c0c0e0601c0c04a0a1c0c0481834b0838180a82828180a0604a4232b08cac2381808a8232b08cac222b08cac23ab08381832b08e06024060e0600e06070301406070300e060e06024060e0600e0c038301406070300e0c062600686062600e0c028300e0c0383004829000132b08686032b08e2c2 (by decide +kernel)

def state250_32 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_32 : Impossible true (goalAt 250) 6 state250_32.toFinset :=
  node_ok cuts250 [⟨state250_28,exclude250_28⟩] 0x38180b03028180a06018980e0602202862600c8c062601898032301898038300686062601898070600c8c06260068606260189801a180682862601898100020e0c0e06024060e0600e0c0683014060383032b0828180e0c03830800001a0a0e0c0383004828706038180a0301c18070301c18070604001828181c180706014180d2c234b08706040028e06026060e060240c07030160605030140c0e2c2381808a0a3818088181c0c04a0a1c0c04818 (by decide +kernel)

def state250_33 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,input 4,input 1,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_33 : Impossible true (goalAt 250) 7 state250_33.toFinset :=
  node_ok cuts250 [⟨state250_16,exclude250_16⟩,⟨state250_20,exclude250_20⟩,⟨state250_21,exclude250_21⟩,⟨state250_22,exclude250_22⟩,⟨state250_30,exclude250_30⟩,⟨state250_31,exclude250_31⟩,⟨state250_32,exclude250_32⟩] 0xe0601c0c0e0602c0c100062c0c0e06040038a0602c0c0703028180e06018908e06026060e2c238b08e06038b08e2c226060624218b08703028a08a28216060e2c238b08703038b08e2c216060a28228b088a0a189806260381810002381808a0a40038880a381806260189804a0a0c8c032301c0c06260189804a0a1898062601c0c032300c8c0e2c206860e2c238300626038300e2c218980e0c2383001a18383081a0a1898062604000832300c8c01a0a0c8c032304000462601898100021898062600e0c01a180e0c10002068601a180e0c062601898100021898062604000032300c8c100020c8c0323040000626018980b03006828b03038181000138180b03040038b030381801a0a381807030068287030128290001128287030400187030128281a0a12060381806828381838b09000138b08381880018281838b081a0a38b09000140028d2c22606038300e0c0e06040038e06026061000e24060e0600e0c0e0601606038300e0c070304001870301606100061406070300e0c038300e06200050e060e2c20e0c0e2c20e06038300e0c0e2c280010e2c206829000106829000a0e0c038304000500010a0c1000140004cac22c0c100052c0c0e06040038e0602c0c1000e2c0c0e06040014e0601c0c100041c0c200034001a00001c0c100061c0c100064001100040e06100070e060e2c280008e2c20e06200010e060e2c24001ce2c2 (by decide +kernel)

def state250_34 : List Sig := [0xccccffccccccffccccccffccccccffccccccffccccccffccccccffccccccffcc,input 3,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_34 : Impossible true (goalAt 250) 6 state250_34.toFinset :=
  node_ok cuts250 [] 0x38180703038180b0304002cb03038181000b28180b0301c0c0a06038180624238180981838b08e2c238180e2c238b0898181890862c21c0c0a28228a08581838b08e2c21c0c0e2c238b08581828a08a2c22c0c070601c180e06034b08d2c22c0c0d2c234b08e0601c18070601c0c0928224a08480a34b08d2c21c0c0d2c234b08480a24a0892c20e060d2c234b08e2c21c180e2c20e06070601c180e2c234b08d2c226060484212108e06032308c8c226060c8c232308e06012108e06016060888222208703032308c8c216060c8c2323087030222088ac20e060c8c232308e2c20e0c0e2c20e06038300e0c0e2c232308c8c206828c8c232308d2c20e0c0d2c20682838300e0c0d2c232308c8c222028626018980e0604002ce06022029000b22028e0601898062601202832300c8c070301898062601202862601898070300c8c0323038b081a1838b08e0c018980e0c038b08626038308e0c006860e0c234b08626034b08d0c00c8c0d0c034b08323034308d0c018980d0c232308626032308383006860c8c0323081a18323083830189806260 (by decide +kernel)

def state250_35 : List Sig := [0xffffffff0000ff00ffffffff0000ff00ffffffff0000ff00ffffffff0000ff00,input 5,input 3,input 4,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_35 : Impossible true (goalAt 250) 6 state250_35.toFinset :=
  node_ok cuts250 [] 0xe0602c0c0a06028180626038180880a1898032301898062600c8c0d2c234300d0c23430862601a1801a18189801a18189806260068601a1818980626006860706034b08d2c21c180928234b08d2c224b08d2c21c180706034b08d2c21c180706034b0868603818090181a18038301a18068600e0c0dac234b08383034b082a0a1a180686012180cac232b08686040004e06026060e06026060703016060703016060e2c23818098183818098181c0c058181c0c05818 (by decide +kernel)

def state250_36 : List Sig := [0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000,input 5,0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,input 4,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_36 : Impossible true (goalAt 250) 6 state250_36.toFinset :=
  node_ok cuts250 [] 0xe0602c0c0a06028180626038180880a1898032301898062600c8c0d2c234300d0c2343081a1818980626006860706034b08d2c21c180928234b08d2c226b08d2c23eb08706034b084a4232b08cac2381808a8232b08cac222b08c8c032b08c8c232308120a32b08eac20a828cac21a180e06024060e0600e06070301406070300e060e06024060e0600e0c038301406070300e0c062600686062600e0c0706034b08706034b08e2c2 (by decide +kernel)

def state250_37 : List Sig := [0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,input 3,input 4,input 1,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_37 : Impossible true (goalAt 250) 7 state250_37.toFinset :=
  node_ok cuts250 [⟨state250_34,exclude250_34⟩,⟨state250_35,exclude250_35⟩,⟨state250_36,exclude250_36⟩] 0xe0601c0c0e0602c0c100062c0c0e0604002ca0602c0c0703028180e06018908e06026060e2c238b08e06038b08e2c226060624218b08703028a08a28216060e2c238b08703038b08e2c216060a28228b088a0a189806260381810002381808a0a4002c880a381806260189804a0a0c8c032301c0c06260189804a0a1898062601c0c032300c8c0e2c206860e2c238300626038300e2c218980e0c2383001a1838308d2c218980d2c234300323034300d2c20c8c0d0c234300626034309000a1898062600e0c01a180e0c10002068601a180e0c0626018980b0301c180706038180d2c234b08b03034b08d2c23818070601c180703024a08928212828d2c234b08703034b08d2c212828928224b08381834b08d2c238b08706038b0838181c180706038b08d2c234b0898180e0c0383038181000a3818098184002c90183818038303818058180e0c038301c0c1000a1c0c058184001850181c0c038300e0c0381880008381838b08383038b0838180e0c0383038b09000a38b09000140004dac24002838300e0c0d2c240004d2c222829000522828e06040028e06022829000b22828e06040014e0601282900041282870304002870301282900061282870304001070300a82900070a828e2c240028e2c20a82a00010a828e2c240028e2c240029000040000626040028626040029000280000626040000626040029000106829000140004cac2 (by decide +kernel)

def state250_38 : List Sig := [0xffffff00ffff0000ffffff00ffff0000ffffff00ffff0000ffffff00ffff0000,input 3,input 5,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_38 : Impossible true (goalAt 250) 6 state250_38.toFinset :=
  node_ok cuts250 [] 0x38180703038180b0304002cb03038181000b28180b0301c0c0a06022828626018980e0604002ce06022829000b22028e0601898062601282832300c8c070301898062601282862601898070300c8c0323038b081a1838b08e0c018980e0c038b08626038308e0c006860e0c232b08626032b08c8c006860c8c032b081a1832308c8c018980c8c234b08626034b08d0c00c8c0d0c034b08323034308d0c018980d0c238180624238180981838b08e2c238180e2c238b0898181890862c21c0c0a28228a08581838b08e2c21c0c0e2c238b08581828a08a2c2260604a4212908e06032b08cac226060cac232b08e06012908e060160608a8222a08703032b08cac216060cac232b08703022a088ac20a060cac232b08e2c20e0c0e2c20a060383012180e2c232b08cac206828cac232b08d2c20e0c0d2c20682838300e0c0d2c232b08cac22c0c070601c180e06034b08d2c22c0c0d2c234b08e0601c18070601c0c0928224a084a0a34b08d2c21c0c0d2c234b084a0a24a0892c20a060d2c234b08e2c21c180e2c20a06070601c180e2c234b08d2c2 (by decide +kernel)

def state250_39 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xffffffffffffffffff00ff0000000000ffffffffffffffffff00ff0000000000,input 3,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_39 : Impossible true (goalAt 250) 5 state250_39.toFinset :=
  node_ok cuts250 [⟨state250_23,exclude250_23⟩] 0x626038180880a18980cac232300c8c23230832301898062600c8c062601c180323018980e2c238300e0c238308686032b08cac21a1808a8232b08cac222b08cac21c182000032b08cac238b08686032b08e060240c0a0602818070603418090301c18050301c18070600a060d2c238180e2c238b0862c228a08e2c238b08a2c2 (by decide +kernel)

def state250_40 : List Sig := [0xffffffffffffffffff00ff0000000000ffffffffffffffffff00ff0000000000,input 3,input 5,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_40 : Impossible true (goalAt 250) 6 state250_40.toFinset :=
  node_ok cuts250 [⟨state250_24,exclude250_24⟩,⟨state250_39,exclude250_39⟩] 0x2c0c070601c180e06034b08d2c22c0c0d2c234b08e0601c18070604001cd2c234b08e2c21c180e2c28000470601c180e2c234b08d2c21c0c0928224a084a0a34b08d2c21c0c0d2c234b084a0a24a0892c222828626018980e0604002ce06022829000b22028e06018980626034b08626034b08d0c00c8c0d0c034b08323034308d0c018980d0c238b081a1838b08e0c018980e0c038b08626038308e0c006860e0c232b08626032b08c8c006860c8c032b081a1832308c8c018980c8c21282832300c8c070301898062601282862601898070300c8c0323038180624238180981838b08e2c238180e2c238b0898181890862c21c0c0a28228a08581838b08e2c21c0c0e2c238b08581828a08a2c22606068601a180e06032b08cac226060cac232b08e0601a180686006828cac232b08d2c240028d2c20682a000004828d2c232b08cac240028cac232b08e2c21a180e2c24002868601a180e2c232b08cac2160608a8222a08703032b08cac216060cac232b08703022a088ac238180703038180b0304002cb03038181000b28180b0301c0c0a060 (by decide +kernel)

def state250_41 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xffffffffffffffffffffffffffffffffff00ff0000000000ff00ff0000000000,input 3,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_41 : Impossible true (goalAt 250) 5 state250_41.toFinset :=
  node_ok cuts250 [⟨state250_25,exclude250_25⟩] 0xe060240c0a0602818032301898062600c8c0cac232300c8c232308626038180880a1898062601c180323018980e2c238300e0c2383088a8232b08cac222b08686032b08cac238180cac21c182000032b08cac238b08486032b0850301c18070601282870603418090301c180d2c228a08e2c238b08a2c238180e2c238b0862c2 (by decide +kernel)

def state250_42 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff0000000000ff00ff0000000000,input 3,input 5,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_42 : Impossible true (goalAt 250) 6 state250_42.toFinset :=
  node_ok cuts250 [⟨state250_26,exclude250_26⟩,⟨state250_41,exclude250_41⟩] 0x38180703038180b0304002cb03038181000b28180b0301c0c0a0601c0c0928224a084a0a34b08d2c21c0c0d2c234b084a0a24a0892c24001cd2c234b08e2c21c180e2c28000470601c180e2c234b08d2c22c0c070601c180e06034b08d2c22c0c0d2c234b08e0601c18070601282832300c8c070301898062601282862601898070300c8c0323034b08626034b08d0c00c8c0d0c034b08323034308d0c018980d0c238b081a1838b08e0c018980e0c038b08626038308e0c006860e0c232b08626032b08c8c006860c8c032b081a1832308c8c018980c8c222828626018980e0604002ce06022829000b22028e0601898062601c0c0a28228a08581838b08e2c21c0c0e2c238b08581828a08a2c238180624238180981838b08e2c238180e2c238b0898181890862c2160608a8222a08703032b08cac216060cac232b08703022a088ac206828cac232b08d2c240028d2c20682a000004828d2c232b08cac240028cac232b08e2c240028e2c240029000712180e2c232b08cac2260604a421a180e06032b08cac226060cac232b08e06012908e060 (by decide +kernel)

def state250_43 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xffccffccccccccccffccffccccccccccffccffccccccccccffccffcccccccccc,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_43 : Impossible true (goalAt 250) 5 state250_43.toFinset :=
  node_ok cuts250 [⟨state250_27,exclude250_27⟩] 0xe060240c0a060281804a4232b08cac2381808a8232b08cac222b08c8c032b08c8c232308cac21c182000032b08cac238b08486032b08626038180880a1898032301898062600c8c062601c180323018980e2c238300e0c23830870603418090301c18050301c180706012828d2c238180e2c238b0862c228a08e2c238b08a2c2 (by decide +kernel)

def state250_44 : List Sig := [0xffccffccccccccccffccffccccccccccffccffccccccccccffccffcccccccccc,input 3,input 5,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_44 : Impossible true (goalAt 250) 6 state250_44.toFinset :=
  node_ok cuts250 [⟨state250_29,exclude250_29⟩,⟨state250_43,exclude250_43⟩] 0x38180703038180b0304002cb03038181000b28180b0301c0c0a0602c0c070601c180e06034b08d2c22c0c0d2c234b08e0601c18070601c0c0928224a084a0a34b08d2c21c0c0d2c234b084a0a24a0892c24001cd2c234b08e2c21c180e2c28000470601c180e2c234b08d2c238180624238180981838b08e2c238180e2c238b0898181890862c21c0c0a28228a08581838b08e2c21c0c0e2c238b08581828a08a2c2260604a4212908e06032b08cac226060cac232b08e06012908e060160608a8222a08703032b08cac216060cac232b08703022a088ac206828cac232b08d2c240028d2c20682a000004828d2c232b08cac20a028cac232b08e2c240028e2c20a029000712180e2c232b08cac206860c8c032300626032b08cac206860cac232308626032300c8c222828626018980e0604002ce06022829000b22028e0601898062601282832300c8c070301898062601282862601898070300c8c0323034b08626034b08d0c00c8c0d0c034b08323034308d0c018980d0c238b081a1838b08e0c018980e0c038b08626038308e0c006860e0c2 (by decide +kernel)

def state250_45 : List Sig := [0xffffff00ffff0000ffffff00ffff0000ffffff00ffff0000ffffff00ffff0000,input 4,input 3,input 5,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_45 : Impossible true (goalAt 250) 6 state250_45.toFinset :=
  node_ok cuts250 [] 0xe0602c0c0a06028180626038180880a1898032301898062600c8c0e2c238300e0c238308cac232300c8c23230862600c8c032301898062600c8c0323018980e06038b08e2c218b08a28238b08e2c228b084a4232b08cac2381808a8232b08cac222b08cac238b08486032b08cac20e0c0383032b08cac21a180383032b08b03038180b03038180703012828703012828381838b08281838b08d2c22c0c0e0602c0c0e0601c0c04a0a1c0c04a0a0e060e2c20e060e2c2 (by decide +kernel)

def state250_46 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000,input 3,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_46 : Impossible true (goalAt 250) 6 state250_46.toFinset :=
  node_ok cuts250 [⟨state250_39,exclude250_39⟩,⟨state250_41,exclude250_41⟩,⟨state250_28,exclude250_28⟩,⟨state250_43,exclude250_43⟩] 0xe060240c0a06028180626038180880a1898032301898062600c8c0cac232300c8c23230862600e06200031898062601c180323018980e2c238300e0c2383084a4232b08cac2381808a8232b08cac222b08cac21c182000232b08cac238b08486032b083818381820001381803818140c20000140c068604000470600a06070600a82870603418090301c18050301c180706012828d2c238180e2c238b0862c228a08e2c238b08a2c2 (by decide +kernel)

def state250_47 : List Sig := [0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000,input 3,input 5,input 1,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_47 : Impossible true (goalAt 250) 7 state250_47.toFinset :=
  node_ok cuts250 [⟨state250_30,exclude250_30⟩,⟨state250_38,exclude250_38⟩,⟨state250_40,exclude250_40⟩,⟨state250_42,exclude250_42⟩,⟨state250_44,exclude250_44⟩,⟨state250_45,exclude250_45⟩,⟨state250_46,exclude250_46⟩] 0xe0601c0c0e0602c0c1000b2c0c0e0604002ca0602c0c0703028180b0301c180706038180d2c234b08b03034b08d2c23818070601c180703024a08928212828d2c234b08703034b08d2c212828928224b09000734b08d2c238b08706038b0a00061c180706038b08d2c234b088a0a18980626038181000b381808a0a4002c880a381806260189804a0a0c8c032301c0c06260189804a0a1898062601c0c032300c8c0d2c218980d2c234300323034300d2c20c8c0d0c234300626034308e2c206860e2c238300626038300e2c218980e0c2383001a1838308cac218980cac2323001a1832300cac206860c8c232300626032309000a18980626040001000a4000100084002a000440000626018980e06018908e06026060e2c238b08e06038b08e2c226060624218b08703028a08a28216060e2c238b08703038b08e2c216060a28228b089818129084a4238180cac232b08981832b08cac2381804a4238180581822a088a821c0c0cac232b08581832b08cac21c0c08a8222b081a0a32b08cac234b09000a34b081a0a80000120a34b08cac232b09000a32b08cac238b09000a38b09000a4001c486040029000540014e06040028e06040029000b8000ce06040014e06040029000440010703040028703040029001080008703040010703040029000140004d2c240028d2c24002a000580004d2c240004d2c24002900070e061000a400286860 (by decide +kernel)

def state250_48 : List Sig := [0xffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00,input 6,input 3,input 5,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_48 : Impossible true (goalAt 250) 6 state250_48.toFinset :=
  node_ok cuts250 [] 0x706034b08d2c21c180d2c238b08706034b08928234b08d2c224a08928234b08d2c224a08626038180880a18980d2c234300d0c234308e2c238300e0c238308cac232300c8c23230832301898062600c8c0121018980626004840e06038b08e2c218b08703038b08e2c228b08a2821a180cac232b08686032b08d2c20e0c0cac232b08e2c21a180cac20e0c0cac232b088ac222a08e0602c0c0a060281805010381809010381809010 (by decide +kernel)

def state250_49 : List Sig := [0xffffffffff00ff000000000000000000ffffffffff00ff00,input 6,input 3,input 5,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_49 : Impossible true (goalAt 250) 6 state250_49.toFinset :=
  node_ok cuts250 [] 0x706034b08d2c21c180d2c238b08706034b08928234b08d2c224b08626038180880a18980d2c234300d0c234308e2c238300e0c238308cac232300c8c23230832301898062600c8c0e06038b08e2c218b08e28238b08e2c20e060686032b08cac21a180cac234b08383032b08cac238b08686032b08ca8232b08cac20e0c0e0602c0c0e0602c0c0b03038180b030381801a0a34b081a0a34b08323018980323018980a28238b08381838b088a8232b08383032b087030 (by decide +kernel)

def state250_50 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 3,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_50 : Impossible true (goalAt 250) 6 state250_50.toFinset :=
  node_ok cuts250 [] 0x1c180d2c234b08706034b08e2c21c180d2c224a08d2c234b08928224a08d2c234b08928218980e06022028626034b08d0c034308d0c218980686006860626038b08e0c038308e0c20c8c06260189803230068606260189801a181a180c8602606068601a180d2c20e0c0d2c232b0838301a18068600e0c038181a180686008828e06038b08e2c218b08703038b08e2c228b08a28238b08e2c240010e0602c0c0a060281805818381809818381803818 (by decide +kernel)

def state250_51 : List Sig := [0xffffffff000000000000000000000000ffffffff00000000,input 6,0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 3,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_51 : Impossible true (goalAt 250) 6 state250_51.toFinset :=
  node_ok cuts250 [] 0x706034b08d2c21c180d2c238b08706034b08928234b08d2c224b08626038180880a18980d2c234300d0c23430862601a1801a1818980e2c238300e0c23830832301898062600c8c068603218098181a180686034b08383034b08cac20e0c068601a180383038180e2c238b0862c238a08e2c238b08501038180b03038180b0302c0c0e0602c0c0e0600a828d2c20a060d2c20c8c062600c8c062600e0c068600e0c0686028a087030 (by decide +kernel)

def state250_52 : List Sig := [0x3333333333003300333333333300330033333333330033003333333333003300,input 1,input 3,input 5,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_52 : Impossible true (goalAt 250) 6 state250_52.toFinset :=
  node_ok cuts250 [] 0xe0602c0c0a06028180706034b08d2c21c180928234b08d2c224b08d2c238b08706034b08e06038b08e2c218b08a28238b08e2c228b08686032b08cac21a1808a8232b08cac222b08cac234b08383032b08cac238b08686032b081210381808a0a3818012101c0c04a0a1c0c0d2c234300d0c234308e2c238b00e2c20e060cac232b00cac21a180e06024040e06024040703014040703014040706034b08706034b08e0c038b08381838b08c8c032b08686032b086260 (by decide +kernel)

def state250_53 : List Sig := [0xffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff00,input 4,input 3,input 5,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_53 : Impossible true (goalAt 250) 6 state250_53.toFinset :=
  node_ok cuts250 [] 0xe0602c0c0a06028180626038180880a1898032301898062600c8c01a181898062600686062601a1801a1818980d2c234300d0c234308e06026060e060240c07030160605030140c068603818090181a18038301a18068600e0c038181a180686012180dac234b08383034b08524234b08d2c238180928234b08d2c224b08d2c23cb08381834b08e0602c0c0e0602c0c04a0a1c0c04a0a1c0c062600c8c062600c8c0e2c238b082a0a0e060cac232b0868600e0c07060 (by decide +kernel)

def state250_54 : List Sig := [0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 3,input 5,input 1,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_54 : Impossible true (goalAt 250) 7 state250_54.toFinset :=
  node_ok cuts250 [⟨state250_0,exclude250_0⟩,⟨state250_2,exclude250_2⟩,⟨state250_6,exclude250_6⟩,⟨state250_20,exclude250_20⟩,⟨state250_48,exclude250_48⟩,⟨state250_49,exclude250_49⟩,⟨state250_50,exclude250_50⟩,⟨state250_51,exclude250_51⟩,⟨state250_52,exclude250_52⟩,⟨state250_53,exclude250_53⟩] 0xe0601c0c0e0602c0c100112c0c0e06040044a0602c0c0703028180b0301c180706038180d2c234b08b03034b08d2c23818070601c180703024a08928212828d2c234b08703034b08d2c212828928224b08381834b08d2c20a82870601c18038181c18070600a828d2c234b0a000934b08d2c24000470601c18200031c180706040004d2c234b088a0a189806260381810011381808a0a40044880a381806260189804a0a0c8c032301c0c06260189804a0a1898062601c0c032300c8c0d2c218980d2c234300323034300d2c20c8c0d0c2343006260343082a0a068601a180e0606260189802a0a1898062600e0601a180686200021898062601a1801a181a1820001068601a181a180626018982000804840121040000626018982000018980626040000121004840e0600e060e06026061001126060e06040044e0602606038180e06070300e06070301606200071606070308001870301606038180e061000a40028e2c22606068601a180e06040044e06026061001126060e0601a18068601606038300e0c070301a18068601606068601a18070300e0c038300682868601a180d2c20e0c0d2c20682838300e0c0d2c21a180d2c20e06100070e061000a1a18068604002900071218100074001ccac23818100053818090104004490103818100113818090104001490101c0c100041c0c050108001450101c0c200041c0c05010400105010 (by decide +kernel)

def state250_55 : List Sig := [0xffff0000ffffff000000000000000000ffff0000ffffff00,input 4,input 3,input 5,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_55 : Impossible true (goalAt 250) 5 state250_55.toFinset :=
  node_ok cuts250 [] 0x18980a06022028626038b08e0c038308e0c232b08c8c032308c8c234b08d0c034308d0c228180e2c238b0862821a180cac232b08686032b08e2c21a180cac232b08d2c20e0c0cac21c180d2c234b08706034b08e2c21c180d2c21c0c0a0602c0c0a0600c8c062600c8c06260140c0e2c21c0c0e2c222b08cac20e0c0cac224b08d2c21c0c0d2c2 (by decide +kernel)

def state250_56 : List Sig := [0xffff0000ffffff00ffff0000ffffff00ffff0000ffffff00ffff0000ffffff00,input 4,input 3,input 5,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_56 : Impossible true (goalAt 250) 6 state250_56.toFinset :=
  node_ok cuts250 [⟨state250_55,exclude250_55⟩] 0xe0602c0c0a06028180626038180880a1898032301898062600c8c0e2c238300e0c23830862601a1801a181898062600c8c032301898062600c8c0323018980e06038b08e2c218b08a28238b08e2c228b0868603818090181a18038301a18068600e0c0eac238b08686038b0868600e0c038301a180cac232b0838301a180b03038180b03038180703012828703012060381838b08381838b08d2c22c0c0e0602c0c0e0601c0c200001c0c100040e060e2c20e060e2c2 (by decide +kernel)

def state250_57 : List Sig := [0xffffffffffffffff00000000ff00ff00ffffffffffffffff00000000ff00ff00,input 6,input 3,input 5,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_57 : Impossible true (goalAt 250) 6 state250_57.toFinset :=
  node_ok cuts250 [] 0x706034b08d2c21c180d2c238b08706034b08928234b08d2c224a08928234b08d2c224a08626038180880a18980d2c234300d0c234308e2c238300e0c238308cac232300c8c23230832301898062600c8c032301898062600c8c0e06038b08e2c218b08a28238b08e2c228a08a28238b08e2c228a08686032b08cac21a180cac234b08383032b08cac238b08686032b08383032b08cac222b088a8232b08cac20e0c0e0602c0c0e0602c0c0703038180b03038180b030 (by decide +kernel)

def state250_58 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,input 3,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_58 : Impossible true (goalAt 250) 6 state250_58.toFinset :=
  node_ok cuts250 [] 0x38180903028180a06018980e0602202862600c8c062601898032301898068600686062601898070600c8c0626038b08e0c038308e0c21a180e0602606068600e0c068601a18038301a18070600e0c068603ab08e2c21a180e2c20e060e06026060e0600e060503016060503006860626006860626032b0828181c18038181c181000138b08381838b0870603418090301c18050301c180706012828d2c238180e2c238b0862c228a08e2c238b08a2c2 (by decide +kernel)

def state250_59 : List Sig := [0xffff000000000000ffff000000000000ffff000000000000ffff00000000,input 4,0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,input 3,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_59 : Impossible true (goalAt 250) 6 state250_59.toFinset :=
  node_ok cuts250 [] 0xe060240c0a06028180626038180880a1898032301898062600c8c062601a1801a1818980d2c234300d0c23430868603818098181a18038301a18068600e0c0fac234b08383034b083818381809818381803818140c05818140c01a18189801a1818980cac206828d2c20e060d2c20a828524234b08d2c21cb08928234b08d2c22cb08e06038b08e2c218b08a28238b08e2c228b08e0c038b08e0c238308e2c23ab08686038b087060 (by decide +kernel)

def state250_60 : List Sig := [0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,input 3,input 5,input 1,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_60 : Impossible true (goalAt 250) 7 state250_60.toFinset :=
  node_ok cuts250 [⟨state250_56,exclude250_56⟩,⟨state250_57,exclude250_57⟩,⟨state250_58,exclude250_58⟩,⟨state250_59,exclude250_59⟩] 0xe0601c0c0e0602c0c1000b2c0c0e0604002ca0602c0c0703028180b0301c180706038180d2c234b08b03034b08d2c23818070601c180703024a08928212828d2c234b08703034b08d2c212828928224b0a000334b08d2c238b08706038b0a00021c180706038b08d2c234b088a0a18980626038181000b381808a0a4002c880a381806260189804a0a0c8c032301c0c06260189804a0a1898062601c0c032300c8c0d2c218980d2c234300323034300d2c20c8c0d0c234300626034308e2c206860e2c238300626038300e2c218980e0c2383001a1838309000a1898062601a1801a181a1810008068601a181a180626018980e06018908e06026060e2c238b08e06038b08e2c226060624218b08703028a08a28216060e2c238b08703038b08e2c216060a28228b0898181a180686038181000a3818098184002c98183818068601a18058180e0c038301c0c068601a18058181a18068601c0c038300e0c01a0a1a180686034b08383034b081a0a0e0c0383034b08686034b09000a4001ceac24002868601a180e2c240028e2c226061000526060e06040028e06026061000b26060e06040014e06016061000416060703040028703016062000116060703040010703006829000106828d2c240028d2c20682a000006828d2c240004d2c20686100000686062604002862600686100080686062604000062604002900110e061000a40028cac2 (by decide +kernel)

def state250_61 : List Sig := [0xccffccffccccccccccffccffccccccccccffccffccccccccccffccffcccccccc,input 1,input 3,input 5,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_61 : Impossible true (goalAt 250) 6 state250_61.toFinset :=
  node_ok cuts250 [] 0xe0602c0c0a06028180706034b08d2c21c180928234b08d2c224b08d2c238b08706034b08e06038b08e2c218b08a28238b08e2c228b084a4232b08cac2381808a8232b08cac222b08cac234b08120a32b08cac238b08381832b086260381808a0a1898032301898062600c8c0d2c234300d2c234300e2c218980e0c238308cac232300cac2323001a183818098183818098181c0c058181c0c0581834b08d0c034b08d0c038b08e0c038b08381832b08c8c032b08c8c0 (by decide +kernel)

def state250_62 : List Sig := [0x3333003333330000333300333333000033330033333300003333003333330000,input 4,input 3,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_62 : Impossible true (goalAt 250) 5 state250_62.toFinset :=
  node_ok cuts250 [] 0x38180b03028180a06038180e2c238b0862c028a08e2c238b08a2c012108c8c232308e06022208c8c2323088ac032308e2c20e0c0c8c232308d2c20e0c0c8c21c180d2c234b08706024a08d2c234b0892c034b08e2c21c180d2c218980880a3818062600c8c0626018980323038308e0c218980e2c218980c8c21a180c8c234308d0c21c180d2c2 (by decide +kernel)

def state250_63 : List Sig := [0xffff00ffffff0000ffff00ffffff0000ffff00ffffff0000ffff00ffffff0000,input 4,input 3,input 5,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_63 : Impossible true (goalAt 250) 6 state250_63.toFinset :=
  node_ok cuts250 [⟨state250_62,exclude250_62⟩] 0xe0602c0c0a06028180626038180880a1898032301898062600c8c01a1818980626006860cac232300c8c23230862601c180323018982000018980626040000e06026060e060240c07030160605030140c04a4232b08cac2381808a8232b08cac222b08cac23ab08383032b08cac21c180383032b08cac20e0c0686032b08706038180a0301c18070301c18070601282838181c180706014180d2c2381808a0a381808a0a1c0c04a0a1c0c04a0a38b08e2c20e0602a0a (by decide +kernel)

def state250_64 : List Sig := [0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000,input 3,input 5,input 1,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_64 : Impossible true (goalAt 250) 7 state250_64.toFinset :=
  node_ok cuts250 [⟨state250_31,exclude250_31⟩,⟨state250_36,exclude250_36⟩,⟨state250_61,exclude250_61⟩,⟨state250_63,exclude250_63⟩] 0xe0601c0c0e0602c0c1000d2c0c0e06040034a0602c0c0703028180b0301c180706038180d2c234b08b03034b08d2c23818070601c180703024a08928212828d2c234b08703034b08d2c212828928224b08381834b08d2c20a82870601c18038181c18070600a828d2c234b088a0a18980626038181000d381808a0a40034880a381806260189804a0a0c8c032301c0c06260189804a0a1898062601c0c032300c8c0d2c218980d2c234300323034300d2c20c8c0d0c2343006260343082a0a068601a180e0606260189802a0a1898062600e0601a1806860cac218980cac2323001a1832300cac206860c8c232300626032308e0600e060e06026061000726060e06040034e0602606038180e06070300e06070301606100071606070304004070301606038180e0609818129084a4238180cac232b08981832b08cac2381804a4238180581822a088a821c0c0cac232b08581832b08cac21c0c08a8222b081a0a32b08cac234b0a000134b081a0a80000120a34b08cac232b09000a4001ceac20e06100070e061000a32b08cac23818100053818098184001c981838181000d3818098184001498181c0c100041c0c058184001c58181c0c100101c0c058184001058181c18100011c180d2c24001cd2c21c18200031c180d2c240004d2c2189810000189801a184001c1a18189820002189801a18400001a1840029000a38b090007400446860 (by decide +kernel)

def state250_65 : List Sig := [0xffffffff00000000ff00ff0000000000ffffffff00000000ff00ff00,input 5,input 3,input 6,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_65 : Impossible true (goalAt 250) 6 state250_65.toFinset :=
  node_ok cuts250 [] 0x706034b08d2c21c180928234b08d2c224a08d2c228a08706034b08626038180880a18980d2c234300d0c23430832301898062600c8c0cac232300c8c232308a28228200a08228208e0602c0c0a06028180686032b08cac21a180cac234b08383032b08383032b08cac222b08cac228a08686032b08e06028a08a282240c0a28238a08703028a08981838180981838180d2c224a08d2c224a081a18189801a181898058181c0c058181c0c0cac222a08cac21a180e2c2 (by decide +kernel)

def state250_66 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00,input 3,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_66 : Impossible true (goalAt 250) 6 state250_66.toFinset :=
  node_ok cuts250 [] 0x1c180d2c234b08706024a08d2c234b08928234b08e2c21c180d2c224a08d2c234b08928218980e06022028626034b08d0c034308d0c232b08c8c032308c8c20c8c0626018980323038b08e0c038308e0c2068606260189801a181a180cac232b08686032b08d2c206828cac222a08cac238b08686032b08581832b08cac222b08e0602c0c0a0602818058181c0c0703040028e06038b08e2c218b08703038b08e2c228b08a282381809818381805818 (by decide +kernel)

def state250_67 : List Sig := [0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00,input 3,input 6,input 1,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_67 : Impossible true (goalAt 250) 7 state250_67.toFinset :=
  node_ok cuts250 [⟨state250_48,exclude250_48⟩,⟨state250_65,exclude250_65⟩,⟨state250_66,exclude250_66⟩] 0xe06018908e06026060e2c238b08e06038b08e2c226060624218b09000428a08a28216060e2c238b0a000238b08e2c216060a28228a0a000128a08a2824001ce2c238b0a000038b08e2c24001ca28228a08b0301c180706038180d2c234b08b03034b08d2c23818070601c180381834b08d2c238b08706038b0838181c180706038b08d2c234b08581824a08928212828d2c234b08581834b08d2c212828928224a09000624a08928240004d2c234b09000634b08d2c240004928224a088a0a189806260381810003381808a0a40048880a38180626018980e2c206860e2c238300626038300e2c218980e0c2383001a1838308d2c218980d2c234300323034300d2c20c8c0d0c2343006260343084a0a0c8c03230160606260189804a0a1898062601606032300c8c0cac218980cac2323001a1832300cac206860c8c23230062603230900030c8c032304000062601898100031898062604000032300c8c0e06016060e0602c0c100042c0c0e06040048e0602c0c058182c0c100044002870302606068601a180e06032b08cac226060cac232b08e0601a18068600e060cac232b08e2c21a180e2c20e06068601a180e2c232b08cac206828cac232b08d2c240018d2c206829000606828d2c232b08cac216061000416061000a32b08cac240011000422b090004400108a8238181000538180b03040048b03038181001238180b03040014b030 (by decide +kernel)

def state250_68 : List Sig := [0xffffffff00000000ffffffffff00ff00ffffffff00000000ffffffffff00ff00,input 5,input 3,input 6,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_68 : Impossible true (goalAt 250) 6 state250_68.toFinset :=
  node_ok cuts250 [] 0x706034b08d2c21c180928234b08d2c224b08d2c21c180706034b08d2c21c180706034b08626038180880a18980d2c234300d0c23430832301898062600c8c0cac232300c8c2323081a1818980626006860121018980626004840e0602c0c0a06028180686032b08cac21a180cac234b08383032b08ca8232b08cac20e0c0cac21a180686032b08cac222a08686032b08e06026060e0600e06070301e06070300e060e2c23818090103818090101c0c050101c0c05818 (by decide +kernel)

def state250_69 : List Sig := [0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,input 3,input 6,input 1,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_69 : Impossible true (goalAt 250) 7 state250_69.toFinset :=
  node_ok cuts250 [⟨state250_68,exclude250_68⟩] 0xe06018908e06026060e2c238b08e06038b08e2c226060624218b08703028a08a28214040e2c238b08703038b08e2c214040a28228b08b0301c180706038180d2c234b08b03034b08d2c23818070601c180381834b08d2c238b08706038b0838181c180706038b08d2c234b08703024a08928240018d2c234b08703034b08d2c240010928224b088a0a189806260381810003381808a0a4002c880a38180626018980e2c206860e2c238300626038300e2c218980e0c2383001a1838308d2c218980d2c234300323034300d2c20c8c0d0c23430062603430900040c8c032301c0c062601898100031898062601c0c032300c8c0cac218980cac2323001a1832300cac206860c8c232300626032308e0601c0c0e0602c0c100042c0c0e0604002ca0602c0c070302818098181a180686038180cac232b08981832b08cac23818068601a180381832b08cac238b08686038b0838181a180686038b08cac232b081a0a32b08cac234b09000a34b081a0a400181a0a34b08cac232b09000440010ca8240028cac232b08703040010703026061000526060e06040028e06026061000b26060e06040014e0600e06100070e060e2c240028e2c20e06200000e060e2c240028e2c206829000106828d2c240028d2c206829000606828d2c240004d2c2068610000068606260400286260068610003068606260400006260400290004160610004400108a82 (by decide +kernel)

def state250_70 : List Sig := [0xffffffffffffffffffffffffffffffff33333333333300003333333333330000,input 7,input 4,input 5,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_70 : Impossible true (goalAt 250) 5 state250_70.toFinset :=
  node_ok cuts250 [] 0xe0602c0c0a0602818062600c8c062600c8c0888232308c8c222b00c8c238308686032308c8c234308383032308686032308c8c21a180484232308c8c218980a08238308e0c228b00e06038308e0c218908626038308e0c218908908234308d0c224b00d0c238308706034308706034308d0c21c180504234308d0c218980880a (by decide +kernel)

def state250_71 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0x33333333333300003333333333330000,input 4,input 5,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_71 : Impossible true (goalAt 250) 4 state250_71.toFinset :=
  node_ok cuts250 [] 0x32308e0c21a180c8c232308d0c20e0c0c8c20e0c0c8c23230838301c0c0e0c238308503034308e0c21c180d0c21c0c0d0c234308124018980c8c21a180c8c206860e0c218980e0c218980d0c21c180d0c20c8c06260189803230 (by decide +kernel)

def state250_72 : List Sig := [0x33333333333300003333333333330000,input 7,input 4,input 5,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_72 : Impossible true (goalAt 250) 5 state250_72.toFinset :=
  node_ok cuts250 [⟨state250_71,exclude250_71⟩] 0x70302202a00001c0c0888232308c8c222b00c8c238308686032308c8c234308383032308686032308c8c21a180a08238308e0c228b00624238308e0c218b00908234308d0c224b00d0c238308706034308706034308d0c21c18032301898062600c8c06260323086860323081a1838308626038308626034308706034308e060 (by decide +kernel)

def state250_73 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0x3333333333330000333333333333000033333333333300003333333333330000,input 4,input 5,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_73 : Impossible true (goalAt 250) 5 state250_73.toFinset :=
  node_ok cuts250 [⟨state250_71,exclude250_71⟩] 0xc8c238b08686032308c8c234b08383032308686032308c8c21a180383032308c8c20e0c0a06038b08e2c218a00703038b08e2c2140c0d2c238b08706034b08706034b08d2c21c180703034b08d2c204900626032308686032308e0c238308626038b08d0c234308706034b08626080000a0601898032301898062600c8c0b030 (by decide +kernel)

def state250_74 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,input 4,input 5,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_74 : Impossible true (goalAt 250) 6 state250_74.toFinset :=
  node_ok cuts250 [⟨state250_70,exclude250_70⟩,⟨state250_72,exclude250_72⟩,⟨state250_73,exclude250_73⟩] 0x38180703038180b0304003cb03038182000228180b0301c0c0a0602606068601a180e06032308c8c226060c8c232308e0601a180686016060888222208703032308c8c216060c8c2323087030222088ac00e060c8c232308e2c21a180e2c20e06068601a180e2c232308c8c206828c8c232308d2c20e0c0d2c20682838300e0c0d2c232308c8c238180624238180981838b08e2c238180e2c238b0898181890862c01c0c0a28228a08581838b08e2c21c0c0e2c238b08581828a08a2c02c0c070601c180e06034b08d2c22c0c0d2c234b08e0601c18070601c0c0928224a08480a34b08d2c21c0c0d2c234b08480a24a0892c00e060d2c234b08e2c21c180e2c20e06070601c180e2c234b08d2c238180626018980880a80004880a38182000038180880a1898062601c0c032300c8c0480a1898062601c0c0626018980480a0c8c032301a180626018980c8c206860c8c21a1801a181a180c8c218980c8c20e0601a1838308e2c218980e0c20e060626018980e2c206860e2c21c180626034308d2c20c8c0d0c21c18032301c180d2c218980d2c2 (by decide +kernel)

def state250_75 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_75 : Impossible true (goalAt 250) 6 state250_75.toFinset :=
  node_ok cuts250 [] 0x38180b03028180a0601a180c8c232308686022208c8c2323088ac03230868601a180c8c23230870600e0c0c8c23230868601a180c8c23818098183818090301c0c05818140c0503038b08706038180a0301c18070301c18070601202838181c180506034b08e06022028e06022028703012028703012028626022028e0601898032301898062600c8c06260323086860323081a181898062600686062600c8c07060189810000 (by decide +kernel)

def state250_76 : List Sig := [0xff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000,input 3,input 4,input 5,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_76 : Impossible true (goalAt 250) 6 state250_76.toFinset :=
  node_ok cuts250 [] 0xe0602c0c0a06028180626038180880a1898032301898062600c8c01a181898062600686062601c180323018980cac232300c8c232308e06026060e060240c07030160605030140c0706038180a0301c18070301c18070601206038181c1807060141804a4232b08cac2381808a8232b08cac222b08cac23ab08381832b08cac236b081a0a32b08e06026060e06026060703016060703016060626006860626006860e2c238b0900010e060d2c234b087060068286860 (by decide +kernel)

def state250_77 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 1,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_77 : Impossible true (goalAt 250) 7 state250_77.toFinset :=
  node_ok cuts250 [⟨state250_20,exclude250_20⟩,⟨state250_32,exclude250_32⟩,⟨state250_46,exclude250_46⟩,⟨state250_58,exclude250_58⟩,⟨state250_74,exclude250_74⟩,⟨state250_75,exclude250_75⟩,⟨state250_76,exclude250_76⟩] 0xe0601c0c0e0602c0c100062c0c0e0604004ca0602c0c070302818098181a180686038180cac232b08981832b08cac23818068601a180581822a088a821c0c0cac232b08581832b08cac21c0c08a8222b08381832b08cac28000c68601a18038181a180686080008cac232b09000132b08cac21c18038301c18200010e0c038301c180cac232b0a000632b08cac24002868601a18200001a180686040028cac232b088a0a189806260381810002381808a0a4004c880a381806260189804a0a0c8c032301c0c06260189804a0a1898062601c0c032300c8c0cac218980cac2323001a1832300cac206860c8c2323006260323090002068601a180e06062601898100021898062600e0601a180686100011898062601c18032301c18100020c8c032301c180626018981000280016000440000626018981000218980626040001000240000e0600e060e06026061001326060e0604004ce060260603818240c070300e0607030160610006160607030400185030160603818140c1000140004e2c22c0c070601c180e06040004e0602c0c10013280c0e0601c18070601c0c100061c0c04a0a1c18070601c0c070601c1804a0a400044a0a0e06100070e06100011c18070604000500011418100014001cd2c2381810005381808a0a4004c8a0a381810013381808a0a400148a0a1c0c100041c0c04a0a400184a0a1c0c100061c0c04a0a400104a0a (by decide +kernel)

def state250_78 : List Sig := [0xffffffffffffffff0000ffff00000000ffffffffffffffff0000ffff00000000,input 4,input 5,input 1,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_78 : Impossible true (goalAt 250) 6 state250_78.toFinset :=
  node_ok cuts250 [] 0x2606068601a180a06032b08cac226060cac232b08a0601a18068600e060cac232b08e2c21a180e2c20e06068601a180e2c232b08cac206828cac232b08d2c20e0c0d2c20682838300e0c0d2c232b08cac2160608a8222a08703032b08cac216060cac232b08703022a088ac222828626018980a06040034a06022829000d22028a06018980626032b08626032b08c8c006860c8c032b081a1832308c8c018980c8c238b081a1838b08e0c018980e0c038b08626038308e0c006860e0c234b08626034b08d0c00c8c0d0c034b08323034308d0c018980d0c21282832300c8c070301898062601282862601898070300c8c0323028180624228180981838b08e2c228180e2c238b0898181890862c21c0c0381828a08581838b08e2c21c0c0e2c238b0858180e06050302c0c070601c180a06034b08d2c22c0c0d2c234b08a0601c18070600e060d2c234b08e2c21c180e2c20e06070601c180e2c234b08d2c21c0c0928224a084a0a34b08d2c21c0c0d2c234b084a0a24a0892c228180703028180b03040034b03028181000d28180b0301c0c07030 (by decide +kernel)

def state250_79 : List Sig := [0xff00ffffff00ff00ff00ffffff00ff00ff00ffffff00ff00ff00ffffff00ff00,input 3,input 4,input 5,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_79 : Impossible true (goalAt 250) 6 state250_79.toFinset :=
  node_ok cuts250 [] 0xe0602c0c0a06028180626038180880a1898032301898062600c8c01a1818980626006860d2c234300d0c23430862601a1801a181898032301898062600c8c0e06026060e060240c07030160605030140c0524234b08d2c238180928234b08d2c224b08d2c23cb08281834b0868603818098181a18028201a18068601c0c038181a180686012180686034b081a0a34b08cac238180b03038180b03016060703016060703038b08e2c20e061000106828d2c21c180d2c2 (by decide +kernel)

def state250_80 : List Sig := [0xffff000000000000ffff000000000000ffff000000000000ffff00000000,input 4,input 5,input 1,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_80 : Impossible true (goalAt 250) 7 state250_80.toFinset :=
  node_ok cuts250 [⟨state250_59,exclude250_59⟩,⟨state250_78,exclude250_78⟩,⟨state250_79,exclude250_79⟩] 0xe0601c0c0e0602c0c100062c0c0e06040034a0602c0c070302818098181a180686038180cac232b08981832b08cac23818068601a180581822a088a821c0c0cac232b08581832b08cac21c0c08a8222b08381832b08cac28000068601a18038181a18068604001ccac232b081a0a32b08cac234b08383034b081a0a0e0c0383034b08cac232b088a0a189806260381810002381808a0a40034880a381806260189804a0a0c8c032301c0c06260189804a0a1898062601c0c032300c8c0cac218980cac2323001a1832300cac206860c8c2323006260323090002068601a180e06062601898100021898062600e0601a1806860d2c218980d2c234300323034300d2c20c8c0d0c234300626034308e0600e060e06026061000726060e06040034e060260603818240c070300e0607030160610007160607030400185030160603818140c0b03014908524238180d2c234b08b03034b08d2c238180524238180703024a08928212828d2c234b08703034b08d2c212828928224b09000140004f2c20e06100070e061000134b08d2c238181000538180b0304001cb03038181000d38180b03040014b0304001d00044001070304001c70304001d00068000470304001070301a181000a1a180cac24001ccac21a18200021a180cac240028cac218981000018980323040008323018981000218980323040000323040005000138b090007400047060 (by decide +kernel)

def state250_81 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 1,input 3,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_81 : Impossible true (goalAt 250) 7 state250_81.toFinset :=
  node_ok cuts250 [⟨state250_48,exclude250_48⟩,⟨state250_50,exclude250_50⟩,⟨state250_66,exclude250_66⟩] 0xb0301c180706038180d2c234b08b03034b08d2c23818070601c180703024a08928240018d2c234b08703034b08d2c240010928224a09000634b08d2c238b08706038b0900061c180706038b08d2c234b09000624a08928240004d2c234b09000634b08d2c240004928224a0898181a180686038180cac232b08981832b08cac23818068601a1801a0a32b08cac234b08383034b081a0a0e0c0383034b08cac232b09000422a088a821c0c0cac232b0a000232b08cac21c0c08a8222a09001032b08cac238b08686038b0a00011a180686038b08cac232b09001022a088a8240028cac232b0a000032b08cac2400288a8222a088a0a189806260381810003381808a0a40050880a38180626018980d2c218980d2c234300323034300d2c20c8c0d0c234300626034308cac218980cac2323001a1832300cac206860c8c23230062603230900040c8c032301c0c062601898100031898062601c0c032300c8c0e2c206860e2c238300626038300e2c218980e0c2383001a18383090003068601a18400006260189810003189806260400001a1806860e0601c0c0e0602c0c100042c0c0e06040050a0602c0c070302818100044001c581838180624238180981838b08e2c238180e2c238b0898181890862c21c0c100041c0c1000738b08e2c240011000428b09000440010a282381810005381809818400409818381810014381809818400149818 (by decide +kernel)

def state250_82 : List Sig := [0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000,input 5,input 6,input 1,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_82 : Impossible true (goalAt 250) 6 state250_82.toFinset :=
  node_ok cuts250 [] 0x2606068601a180e06032b08cac226060cac232b08e0601a1806860160608a8222a08703032b08cac216060cac232b08703022a088ac20a060cac232b08e2c21a180e2c20a06068601a180e2c232b08cac206828cac232b08d2c20e0c0d2c20682838300e0c0d2c232b08cac222828626018980e06040034e06022829000d22028e06018980626032b08626032b08c8c006860c8c032b081a1832308c8c018980c8c21282832300c8c070301898062601282862601898070300c8c0323038b081a1838b08e0c018980e0c038b08626038308e0c006860e0c234b08626034b08d0c00c8c0d0c034b08323034308d0c018980d0c238180703038180a03040018a03038181000d38180a0301c0c0703038180624238180981838b08e2c238180e2c238b0898181890862c21c0c0281838a08581838b08e2c21c0c0e2c238b0858180a0605030280c070601c180e06034b08d2c2280c0d2c234b08e0601c18070601c0c0928224a084a0a34b08d2c21c0c0d2c234b084a0a24a0892c20a060d2c234b08e2c21c180e2c20a06070601c180e2c234b08d2c2 (by decide +kernel)

def state250_83 : List Sig := [0xff00ff00ff00ff00ffffffffff00ff00ff00ff00ff00ff00ffffffffff00ff00,input 3,input 5,input 6,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_83 : Impossible true (goalAt 250) 6 state250_83.toFinset :=
  node_ok cuts250 [] 0x706034b08d2c21c180928234b08d2c224b08d2c238b08706034b08626038180880a18980d2c234300d0c23430832301898062600c8c0e2c238300e0c23830862600e0c01a181898062600c8c0323018980e0602c0c0e0602c0c0e06038b08e2c218b08e28238b08e2c20e060383038180981838180282034b08383034b0838301e0c058180e0c0381838b08383038b08cac22c0c0e0602c0c0e06006828d2c206828d2c21606050101c0c0703028a08e2c20e060e2c2 (by decide +kernel)

def state250_84 : List Sig := [0xffffffff000000000000000000000000ffffffff00000000,input 5,input 6,input 1,input 3,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_84 : Impossible true (goalAt 250) 7 state250_84.toFinset :=
  node_ok cuts250 [⟨state250_51,exclude250_51⟩,⟨state250_82,exclude250_82⟩,⟨state250_83,exclude250_83⟩] 0xb0301c180706038180d2c234b08b03034b08d2c23818070601c180581824a08928212828d2c234b08581834b08d2c212828928224b09000734b08d2c238b08706038b0900061c180706038b08d2c234b0898181a180686038180cac232b08981832b08cac23818068601a1801a0a32b08cac234b08383034b081a0a0e0c0383034b08cac232b08581822a088a8214040cac232b08581832b08cac2140408a8222b09000732b08cac238b08686038b0a00001a180686038b08cac232b088a0a189806260381810003381808a0a40034880a38180626018980d2c218980d2c234300323034300d2c20c8c0d0c234300626034308cac218980cac2323001a1832300cac206860c8c2323006260323084a0a0c8c03230160606260189804a0a1898062601606032300c8c0e2c206860e2c238300626038300e2c218980e0c2383001a1838308e06016060e0602c0c100042c0c0e06040034e0602c0c058182c0c0e06018908e06026060e2c238b08e06038b08e2c226060624218b09000440010e2824001ce2c238b0858184001058182c0c100052c0c0e0604001ce0602c0c1000d2c0c0e06040014e0604001d000140004d2c24001cd2c24001d000680004d2c240004d2c20e0c1000a0e0c0cac24001ccac20e0c200020e0c0cac240028cac20c8c100000c8c062604001c62600c8c100030c8c062604000062604001d00041c0c1000440010a282 (by decide +kernel)

def state250_85 : List Sig := roots 250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_85 : Impossible true (goalAt 250) 8 state250_85.toFinset :=
  node_ok cuts250 [⟨state250_3,exclude250_3⟩,⟨state250_7,exclude250_7⟩,⟨state250_9,exclude250_9⟩,⟨state250_11,exclude250_11⟩,⟨state250_33,exclude250_33⟩,⟨state250_37,exclude250_37⟩,⟨state250_47,exclude250_47⟩,⟨state250_54,exclude250_54⟩,⟨state250_60,exclude250_60⟩,⟨state250_64,exclude250_64⟩,⟨state250_67,exclude250_67⟩,⟨state250_69,exclude250_69⟩,⟨state250_77,exclude250_77⟩,⟨state250_80,exclude250_80⟩,⟨state250_81,exclude250_81⟩,⟨state250_84,exclude250_84⟩] 0x40014e0601c0c0e06040014b03040014b03040014e06040014a06040014b0301c0c0a06040014e06018908e06040014981838b08e2c240014e06038b08e2c24001498181890862c240010703028a08a2828003c581838b08e2c280038703038b08e2c240010581828a08a2c240014b0301c180706040014e06034b08d2c240014b03034b08d2c240014e0601c180706040010703024a089282400044a0a34b08d2c240018703034b08d2c2400044a0a24a0892c280034381834b08d2c240004e2c21c180e2c28003038181c180706040004e2c234b08d2c24001498181a180686040014e06032b08cac240014981832b08cac240014e0601a180686040010581822a088a828002c703032b08cac280028581832b08cac240010703022a088ac280024381832b08cac280020e2c21a180e2c28001c38181a180686080018e2c232b08cac2400041a0a32b08cac280014d2c20e0c0d2c2800101a0a0e0c0383040004d2c232b08cac2400148a0a18980626040014e06040014e060400148a0a40014880a40014e060189806260400104a0a0c8c032304000070301898062604000c4a0a1898062604000070300c8c032308000ce2c206860e2c240000e0c018980e0c080008e2c218980e0c240000e0c006860e0c240004d2c218980d2c240000d0c00c8c0d0c040008d2c20c8c0d0c240004d0c018980d0c280004cac218980cac240000c8c006860c8c080000cac206860c8c240000c8c018980c8c2 (by decide +kernel)

theorem lower250 : Claim 250 9 :=
  fromSearch 856772672 (by decide +kernel) exclude250_85

theorem lower177 : Claim 177 5 :=
  fromLift 5 16 4 lower161 (by decide +kernel)

def cuts145 : Cuts (goalAt 145) := []

def state145_0 : List Sig := roots 145
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude145_0 : Impossible true (goalAt 145) 3 state145_0.toFinset :=
  node_ok cuts145 [] 0x240401101240408101242009080240409080242008101044041101204041110044409010206008180204048180206009010044401110044048180206009080044409080044041110044409080206008180 (by decide +kernel)

theorem lower145 : Claim 145 4 :=
  fromSearch 4 (by decide +kernel) exclude145_0

theorem lower153 : Claim 153 5 :=
  fromLift 5 8 3 lower145 (by decide +kernel)

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

def cuts99 : Cuts (goalAt 99) := []

def state99_0 : List Sig := roots 99
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude99_0 : Impossible true (goalAt 99) 3 state99_0.toFinset :=
  node_ok cuts99 [] 0x8c0c624218908224208880626018980226018908626018980210308480616018580216010d08616018580434218580626010d086160 (by decide +kernel)

theorem lower99 : Claim 99 4 :=
  fromSearch 85 (by decide +kernel) exclude99_0

theorem lower43 : Claim 43 5 :=
  fromLift 5 2 83 lower41 (by decide +kernel)

def rule107_0 : {c : Cut // CutGood (goalAt 107) c} :=
  ruleFor 107 lower105 none (by decide +kernel)

def rule107_1 : {c : Cut // CutGood (goalAt 107) c} :=
  ruleFor 107 lower106 none (by decide +kernel)

def rule107_2 : {c : Cut // CutGood (goalAt 107) c} :=
  ruleFor 107 lower99 none (by decide +kernel)

def rule107_3 : {c : Cut // CutGood (goalAt 107) c} :=
  ruleFor 107 lower73 none (by decide +kernel)

def rule107_4 : {c : Cut // CutGood (goalAt 107) c} :=
  ruleFor 107 lower43 none (by decide +kernel)

def cuts107 : Cuts (goalAt 107) := [rule107_0,rule107_1,rule107_2,rule107_3,rule107_4]

def state107_0 : List Sig := [0xffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffee,input 3,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_0 : Impossible true (goalAt 107) 4 state107_0.toFinset :=
  node_ok cuts107 [] 0xa028624218908224202c28434210d080b0a10d0861420840c434210d08484202c28434218580480a1210848420240c484218908220a121086860088806260189802260189086260189810003 (by decide +kernel)

def state107_1 : List Sig := [0xee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee,input 3,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_1 : Impossible true (goalAt 107) 4 state107_1.toFinset :=
  node_ok cuts107 [] 0x280a189086242089080b0a10d08434202c28434218508210310d0869601a1800b0a1a18028201a18068600a98048401a18068601298022201898062600898062421898062600a0286160185804342189804842 (by decide +kernel)

def state107_2 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_2 : Impossible true (goalAt 107) 5 state107_2.toFinset :=
  node_ok cuts107 [⟨state107_0,exclude107_0⟩,⟨state107_1,exclude107_1⟩] 0x100030a8282a0a128286242189090003189086242128282a0a089084a0a0a08028201040c68601a1804a0a1a18068601040c28200a1802a0a129084a421890868601a1802a0a1a1806860189084a4212180410302c280b0a12828434210d08410310d084342128280b0a02c28210310d0843421890900011850821034000c210318908434210d08090310d0843421a1800b0a1a180090302c280b0a1a18043421a18100004000061601282822200888048081898062601282862601898048080888022601890900031890828081898062601890862601898028084000c280a1290862601898068608000468601290a0000121086860189806260 (by decide +kernel)

def state107_3 : List Sig := [0x5544554455445544554455445544554455445544554455445544554455445544,input 0,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_3 : Impossible true (goalAt 107) 4 state107_3.toFinset :=
  node_ok cuts107 [] 0x280a18908624208908480a1210848420240c484218908220a12108212018580616008d80414018580616010d8061601a58009031858022201898062600898062421898062600840c62601a1804842189804342 (by decide +kernel)

def state107_4 : List Sig := [0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 3,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_4 : Impossible true (goalAt 107) 5 state107_4.toFinset :=
  node_ok cuts107 [⟨state107_0,exclude107_0⟩,⟨state107_3,exclude107_3⟩] 0x100030a028280a12028624218909000318908624212028280a08908430308480212012028616018580430318580616012028212008580230310d08434218908616018580230318580616018908434210d080903185806160121080b0a12108090302c280b0a12108616018582000118580616018980434218982000010d08434218980616018580480a0240c480a10c0c484212108480a12108484210c0c09030240c280a12108484218909000218908280a4000c220a1890848421210900004000068601202822200888041011898062601202862601898041010888022601890900031890821011898062601890862601898021014000c2103 (by decide +kernel)

def state107_5 : List Sig := [0xffaaffaaffaaffaa0000000000000000ffaaffaaffaaffaa,input 0,input 3,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_5 : Impossible true (goalAt 107) 4 state107_5.toFinset :=
  node_ok cuts107 [] 0x18908626018980280a1898068601210862601290868601a180486010d08616018580434218580626010d08616018580686002c2861600a82862420a82862421202862601282862600a180686012828686008580616002c286160 (by decide +kernel)

def state107_6 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 3,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_6 : Impossible true (goalAt 107) 5 state107_6.toFinset :=
  node_ok cuts107 [⟨state107_0,exclude107_0⟩,⟨state107_5,exclude107_5⟩] 0x2a0a1890862420890822201898062600898062421898062600a0286260024040903189806260400020000189804a0a10c0c4a0a02c0c2a0a189082a0a18908686002c284a0a10c0c0b0a02c28624208c0c624202420626002c28626002c0c0b0a4000461601282a00011282900040a82862420a8286242 (by decide +kernel)

def state107_7 : List Sig := roots 107
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_7 : Impossible true (goalAt 107) 6 state107_7.toFinset :=
  node_ok cuts107 [⟨state107_2,exclude107_2⟩,⟨state107_4,exclude107_4⟩,⟨state107_6,exclude107_6⟩] 0x4001100040a8282a0a400104a0a189086242400110003189086242400104a0a0a8282242400104a0a0a08028204001043031a1806860400104a0a1a18068604001043030a08028604000c2a0a129084a424000862421a18068604000c2a0a1a1806860400086242129084860400004a0a088802220400004808189806260400004a0a1898062604000048080888022604000062424000c624240000280818980626040000624218980626040000280840000280a400004a42189806260400006860400006860400004a42800044842400006860189806260400104303084802120400104a0a185806160400104303185806160400104a0a0848021604000c230310d0843424000462421858061604000c230318580616040004624210d084342400080b0318580616040004686002c286860800080b0302c280b0a40004686018580616040001000018580616040000626010d08626040002000010d084342400006260185806160 (by decide +kernel)

theorem lower107 : Claim 107 7 :=
  fromSearch 83 (by decide +kernel) exclude107_7

theorem lower83 : Claim 83 5 :=
  fromLift 5 2 68 lower81 (by decide +kernel)

def cuts27 : Cuts (goalAt 27) := []

def state27_0 : List Sig := roots 27
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude27_0 : Impossible true (goalAt 27) 3 state27_0.toFinset :=
  node_ok cuts27 [] 0x6828130304828120a068281a18068601103048401a1806860121802c281918064600b0a044401918064601118064601a1802c281918 (by decide +kernel)

theorem lower27 : Claim 27 4 :=
  fromSearch 67 (by decide +kernel) exclude27_0

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

theorem lower115 : Claim 115 6 :=
  fromLift 6 2 68 lower113 (by decide +kernel)

theorem lower59 : Claim 59 6 :=
  fromLift 6 2 67 lower57 (by decide +kernel)

def rule123_0 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower121 none (by decide +kernel)

def rule123_1 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower122 none (by decide +kernel)

def rule123_2 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower107 none (by decide +kernel)

def rule123_3 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower91 none (by decide +kernel)

def rule123_4 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower115 none (by decide +kernel)

def rule123_5 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower59 none (by decide +kernel)

def rule123_6 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower43 none (by decide +kernel)

def rule123_7 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower122 (some (1,input 3,input 6)) (by decide +kernel)

def rule123_8 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower57 none (by decide +kernel)

def rule123_9 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower83 none (by decide +kernel)

def cuts123 : Cuts (goalAt 123) := [rule123_0,rule123_1,rule123_2,rule123_3,rule123_4,rule123_5,rule123_6,rule123_7,rule123_8,rule123_9]

def state123_0 : List Sig := [0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00,input 3,input 6,input 0,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_0 : Impossible true (goalAt 123) 7 state123_0.toFinset :=
  node_ok cuts123 [] 0x100050e06038181606062421890900091890862421606038180e061000908c0c23034000c62421890900091890862424000c230308c0c38181490852421890870601c18038181c18070601890852421418058180682858181282870601c18058181c1807060128281a0a12061000604c0c13034000870601c18100061c180706040008130304c0c62420686062420e06062601898062421898062600e0601a180686052421898062601c18032301c18052420c8c050421c1806260189804a0a0c8c03230160606260189804a0a1898062601606032300c8c04a421898062601a1801a181a1804a420686048421a18062601898100080c8c032304000062601898100081898062604000032300c8c0230310d08434218908616018580230318580616018908434210d0813031858061601c18031301c18013030c4c031301c180616018581000818580616018980434218981000710d0843421898061601858100050c4c031301606061601858100071858061601606031300c4c100041858061601a18019181a18100070646019181a18061601858100070c4c031304000461601858100071858061604000431300c4c100044001070300e0604a421290862421a18068600e06068601a18062421290848600682868601a18070604001070600682900060682870601a18068601606100051606100041a18068604001100040a1810004400143830 (by decide +kernel)

def state123_1 : List Sig := roots 123
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_1 : Impossible true (goalAt 123) 8 state123_1.toFinset :=
  node_ok cuts123 [⟨state123_0,exclude123_0⟩] 0x4000c70300e06070304000c58181890862424000c70301890862424000c58180e0605030400087030068287030400084a0a1c18070604000870301c1807060400084a0a0682848184000c38181490852424000c62421c18070604000c38181c18070604000c62421490850604001458180e0c038304001070301a18068608000058181a18068604001070300e0c038304000c3818129084a424000c62421a18068604000c38181a18068604000c6242129084860400081a0a1a18068604000870600e0c07060400081a0a0e0c038304000870601a1806860400004a0a0c8c03230400007030189806260400004a0a1898062604000070300c8c03230400006242068606242400003818189806260400006242189806260400003818068601a184000052421898062604000070600c8c070604000052420c8c05042400007060189806260400004a42189806260400006860068606860400004a420686048424000068601898062604000443030c4c031304000470301858061604000443031858061604000470300c4c0313040004230310d08434240004624218580616040004230318580616040004624210d0843424000413031858061604000470600c4c070604000413030c4c03130400047060185806160400040b03185806160400046860064606860400040b0306460191840004686018580616040001000018580616040000626010d08626040001000110d084342400006260185806160 (by decide +kernel)

theorem lower123 : Claim 123 9 :=
  fromSearch 67 (by decide +kernel) exclude123_1

theorem lower235 : Claim 235 9 :=
  fromLift 9 2 83 lower233 (by decide +kernel)

theorem lower209 : Claim 209 5 :=
  fromLift 5 64 4 lower145 (by decide +kernel)

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

theorem lower147 : Claim 147 5 :=
  fromLift 5 2 68 lower145 (by decide +kernel)

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

theorem lower211 : Claim 211 6 :=
  fromLift 6 2 68 lower209 (by decide +kernel)

theorem lower227 : Claim 227 6 :=
  fromLift 6 2 85 lower225 (by decide +kernel)

def rule251_0 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower249 none (by decide +kernel)

def rule251_1 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower250 none (by decide +kernel)

def rule251_2 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower187 none (by decide +kernel)

def rule251_3 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower123 none (by decide +kernel)

def rule251_4 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower235 none (by decide +kernel)

def rule251_5 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower243 none (by decide +kernel)

def rule251_6 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower219 none (by decide +kernel)

def rule251_7 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower155 none (by decide +kernel)

def rule251_8 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower91 none (by decide +kernel)

def rule251_9 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower211 none (by decide +kernel)

def rule251_10 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower250 (some (1,input 3,input 5)) (by decide +kernel)

def rule251_11 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower241 none (by decide +kernel)

def rule251_12 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower227 none (by decide +kernel)

def rule251_13 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower235 (some (1,input 3,input 5)) (by decide +kernel)

def cuts251 : Cuts (goalAt 251) := [rule251_0,rule251_1,rule251_2,rule251_3,rule251_4,rule251_5,rule251_6,rule251_7,rule251_8,rule251_9,rule251_10,rule251_11,rule251_12,rule251_13]

def state251_0 : List Sig := [0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 3,input 5,input 0,input 1,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_0 : Impossible true (goalAt 251) 9 state251_0.toFinset :=
  node_ok cuts251 [] 0x4001ce0601c0c0e0604001cb0304001cb0304001ce06040020a0604001cb0301c0c0a06040020b0301c180706040020e06034b08d2c240020b03034b08d2c240020e0601c18070604001c703024a0892824001c4a0a34b08d2c24001c703034b08d2c24001c4a0a24a0892c240018381834b08d2c2400182a0a1c18070604001838181c1807060400182a0a34b08d2c240025000934b08d2c24003100041c180706040025000d1c180706040031000434b08d2c24002c8a0a1898062604002ce0604002ce0604002c8a0a40020880a4002ce0601898062604002c4a0a0c8c032304002c70301898062604002c4a0a1898062604002c70300c8c032304002cd2c218980d2c24002cd0c00c8c0d0c04002cd2c20c8c0d0c24002cd0c018980d0c2400182a0a068601a18400183818189806260400182a0a189806260400183818068601a1840015000518980626040014686006860686040015000b068601a184001468601898062604002d000b0484012104002d00001898062604002d000b1898062604002d000004840121040020830318580616040020e06030f08c3c240020830330f08c3c240020e0601858061604001c430320e0883824001c703030f08c3c24001c430330f08c3c24001c703020e0883c240030130330f08c3c240028d2c20c4c0d2c24002813030c4c0313040030d2c230f08c3c24002d000b30700c1c04002c626030f08c3c24002d000a30f08c3c24002c626030700c1c240019000630f08c3c240018381818580616040019000a18580616040018381830f08c3c240015000530f08c3c240014686006460686040015000a06460191840014686030f08c3c240025000930f08c3c240025000118580616040025000a18580616040025000130f08c3c240018e0600e060e06040018981840018981840018e06040020e0604001898180e06038184001870300e06070304001858184001858184001870304001c70304001858180e060381840015000540014e2c24001498181a180686040014e06040014e06040014981840020981840014e0601a18068604001458180e0c038304001470301a18068604001458181a18068604001470300e0c03830400141a0a1a180686040014d2c20e0c0d2c2400141a0a0e0c0383040014d2c21a180d2c24001438184001838184001500051a180686040015000540014486040015000540018cac240020e0604000ce06040020901040020901040020e06040020e0604002090104000c90104001c70304000870304001c50104001c50104001c70304001c70304001c5010400085010 (by decide +kernel)

def state251_1 : List Sig := roots 251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_1 : Impossible true (goalAt 251) 10 state251_1.toFinset :=
  node_ok cuts251 [⟨state251_0,exclude251_0⟩] 0x40008e0601c0c0e06040008b03040008b03040008e0604000ca06040008b0301c0c0a0604000ce06018908e0604000c981838b08e2c24000ce06038b08e2c24000c98181890862c240008703028a08a28240008581838b08e2c240008703038b08e2c240008581828a08a2c24000cb0301c18070604000ce06034b08d2c24000cb03034b08d2c24000ce0601c180706040008703024a089282400084a0a34b08d2c240008703034b08d2c2400084a0a24a0892c240010381834b08d2c240010e2c21c180e2c24001038181c180706040010e2c234b08d2c24000c98181a18068604000ce06032b08cac24000c981832b08cac24000ce0601a180686040008581822a088a8240008703032b08cac240008581832b08cac240008703022a088ac240018381832b08cac240014e2c21a180e2c28000038181a180686040014e2c232b08cac2400101a0a32b08cac240010d2c20e0c0d2c2400101a0a0e0c0383040010d2c232b08cac2400008a0a18980626040000e06040000e060400008a0a4000c880a40000e060189806260400004a0a0c8c03230400007030189806260400004a0a1898062604000070300c8c0323040000e2c206860e2c240000e0c018980e0c040000e2c218980e0c240000e0c006860e0c240000d2c218980d2c240000d0c00c8c0d0c040000d2c20c8c0d0c240000d0c018980d0c240000cac218980cac240000c8c006860c8c040000cac206860c8c240000c8c018980c8c240004830318580616040004e06030f08c3c240004830330f08c3c240004e06018580616040008430320e08838240008703030f08c3c240008430330f08c3c240008703020e0883c240004230330f08c3c240004e2c218580e2c240004230318580616040004e2c230f08c3c240004130330f08c3c240004d2c20c4c0d2c24000413030c4c0313040004d2c230f08c3c2400040b0330f08c3c240004cac206460cac2400040b0306460191840004cac230f08c3c240001000030700c1c040000626030f08c3c240001000130f08c3c240000626030700c1c2 (by decide +kernel)

theorem lower251 : Claim 251 11 :=
  fromSearch 67 (by decide +kernel) exclude251_1


open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

def smallCircuit : Circuit := ⟨[⟨.or, [4, 5]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [8, 10]⟩, ⟨.and, [13, 14]⟩, ⟨.and, [3, 15]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [19, 18]⟩], 20⟩

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


def lowRow (i : Fin 8) : Row := Fin.ofNat 256 (1 <<< ([3, 4, 6, 0, 0, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 256 ((1 <<< i.val) ||| (1 <<< ([3, 4, 6, 0, 0, 0, 0, 0] : List Nat).getD i.val 0))

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

end PEqualNP.Outside.L_meta_31215_aux

open PEqualNP.Outside.L_meta_31215_aux in
theorem PEqualNP.Outside.L_meta_31215 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true))  := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct

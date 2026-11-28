import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31081_aux


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
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 4 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)


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

def cuts176 : Cuts (goalAt 176) := []

def state176_0 : List Sig := roots 176
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude176_0 : Impossible true (goalAt 176) 3 state176_0.toFinset :=
  node_ok cuts176 [] 0x28080301028080901028200a08028080a0802820090100c04030102404030200c080a02024200908024040908024200a0200c08030200c040908024200a0800c080a0800c04030200c080a080242009080 (by decide +kernel)

theorem lower176 : Claim 176 4 :=
  fromSearch 1078263808 (by decide +kernel) exclude176_0

theorem lower240 : Claim 240 5 :=
  fromLift 5 64 1195704320 lower176 (by decide +kernel)

theorem lower209 : Claim 209 5 :=
  fromLift 5 16 4 lower193 (by decide +kernel)

def cuts161 : Cuts (goalAt 161) := []

def state161_0 : List Sig := roots 161
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude161_0 : Impossible true (goalAt 161) 3 state161_0.toFinset :=
  node_ok cuts161 [] 0x28080210128080810128200a08028080a08028200810108404210120404212008480a02020600818020404818020600a02008480212008404818020600a08008480a08008404212008480a080206008180 (by decide +kernel)

theorem lower161 : Claim 161 4 :=
  fromSearch 5 (by decide +kernel) exclude161_0

def cuts145 : Cuts (goalAt 145) := []

def state145_0 : List Sig := roots 145
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude145_0 : Impossible true (goalAt 145) 3 state145_0.toFinset :=
  node_ok cuts145 [] 0x240401101240408101242009080240409080242008101044041101204041110044409010206008180204048180206009010044401110044048180206009080044409080044041110044409080206008180 (by decide +kernel)

theorem lower145 : Claim 145 4 :=
  fromSearch 4 (by decide +kernel) exclude145_0

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

def cuts49 : Cuts (goalAt 49) := []

def state49_0 : List Sig := roots 49
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude49_0 : Impossible true (goalAt 49) 3 state49_0.toFinset :=
  node_ok cuts49 [] 0xc04011010c04021010c08030200c04030200c0802101044041101084041110044403010084802120084042120084803010044401110044042120084803020044403020044041110044403020084802120 (by decide +kernel)

theorem lower49 : Claim 49 4 :=
  fromSearch 4 (by decide +kernel) exclude49_0

theorem lower113 : Claim 113 5 :=
  fromLift 5 64 4 lower49 (by decide +kernel)

def rule241_0 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower225 none (by decide +kernel)

def rule241_1 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower240 none (by decide +kernel)

def rule241_2 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower209 none (by decide +kernel)

def rule241_3 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower177 none (by decide +kernel)

def rule241_4 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower113 none (by decide +kernel)

def rule241_5 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower193 none (by decide +kernel)

def rule241_6 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower49 none (by decide +kernel)

def rule241_7 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower161 none (by decide +kernel)

def rule241_8 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower145 none (by decide +kernel)

def rule241_9 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower176 none (by decide +kernel)

def cuts241 : Cuts (goalAt 241) := [rule241_0,rule241_1,rule241_2,rule241_3,rule241_4,rule241_5,rule241_6,rule241_7,rule241_8,rule241_9]

def state241_0 : List Sig := [0xffffffffffffffffffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaa,input 0,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_0 : Impossible true (goalAt 241) 4 state241_0.toFinset :=
  node_ok cuts241 [] 0x2820090801c14090801c140a0802820070501c180a0802820100082414090802420011011c18090802420100032c1808180282002101206008180242005150206005150206008180145406160 (by decide +kernel)

def state241_1 : List Sig := [0x5555555555555555555555555555555555550000555500005555000055550000,input 0,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_1 : Impossible true (goalAt 241) 4 state241_1.toFinset :=
  node_ok cuts241 [] 0xa08024200705024200705028200a0801c14090502420090800440441402820061602820021202420061602420061602c580810118580a0801c180a0800840490801c18090800440470602c18090501c1808180 (by decide +kernel)

def state241_2 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_2 : Impossible true (goalAt 241) 4 state241_2.toFinset :=
  node_ok cuts241 [] 0xa08024200705024200706028200a08008404705028200a0801c14070602420090801040490502420090804001c81802820021012060081802420041012060081012060081801c18061602c1807060241407060 (by decide +kernel)

def state241_3 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_3 : Impossible true (goalAt 241) 5 state241_3.toFinset :=
  node_ok cuts241 [⟨state241_0,exclude241_0⟩,⟨state241_1,exclude241_1⟩,⟨state241_2,exclude241_2⟩] 0x1000728200a0802420070502420100051c140705024200a0802420100061c140705024140a08028201000528200a0802414070501c140706008404706040020a08028200706028200a0804002021010840421012060081802820061602820021011858061602820081802060041012060081802420061602420041011858061602420081802060100061858061602414081802060200022060081802414061601858200011858061601c18081802060200002060081801c18061601858090501040490504001c90802420090502420090804001841011040470601040470604000c90802420070602420090804000c410110405000040000b060 (by decide +kernel)

def state241_4 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaa,input 7,input 0,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_4 : Impossible true (goalAt 241) 4 state241_4.toFinset :=
  node_ok cuts241 [] 0xa08024200705024200b06028200a08024180b06024200908028180818028200210120600818024200515020600b1602060081802c1807050282007060282003020242007060242006160206005150206009050 (by decide +kernel)

def state241_5 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_5 : Impossible true (goalAt 241) 4 state241_5.toFinset :=
  node_ok cuts241 [] 0xa08030200705028200705028200a0801c140615028200a08014540110130200c08004404515030200c0804001c81802820070602060081802420070602060070602060081801c18061602060081801c180e060 (by decide +kernel)

def state241_6 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 0,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_6 : Impossible true (goalAt 241) 5 state241_6.toFinset :=
  node_ok cuts241 [⟨state241_0,exclude241_0⟩,⟨state241_4,exclude241_4⟩,⟨state241_5,exclude241_5⟩] 0xe0601c140e06024140a08028200e06028200a08024140705030181000728200a0803020070503020100051c140705030200a08028200e06004404e06028080c08030200e06030200c0802808011012818081011454051503818100093818081018000881013818051503818021011454051502820100092820021014001421012820051502820011014001c11013020051503020011011454051503020100073020100004000081802414070601c180e06080004b06024142000024140e0601c18070601c14100081c140a0801c180a0801c14070601c180a08040020a08004405000324200c0801c18090800440470601c180c0804000cc080 (by decide +kernel)

def state241_7 : List Sig := [0xffff0000ffff00000000000000000000aaaa0000aaaa,input 0,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_7 : Impossible true (goalAt 241) 4 state241_7.toFinset :=
  node_ok cuts241 [] 0xe06028200a0803018070502820070602820070602c18090501c18081802820061602060081801c180515020600616020600818018580a0801c140a08030200908028180c08030200e06020600616020600c080 (by decide +kernel)

def state241_8 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_8 : Impossible true (goalAt 241) 5 state241_8.toFinset :=
  node_ok cuts241 [⟨state241_5,exclude241_5⟩,⟨state241_0,exclude241_0⟩,⟨state241_2,exclude241_2⟩,⟨state241_7,exclude241_7⟩] 0x28200c0801c140a0801c140a0802820070501c140a0802820070501c140a0801c180a0802420070602040600021c18070604000200011c180410130200c08010406000330200c0804001ce06020600a08008404818020600706080000818020600c080104048180204048180400186160 (by decide +kernel)

def state241_9 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 0,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_9 : Impossible true (goalAt 241) 6 state241_9.toFinset :=
  node_ok cuts241 [⟨state241_3,exclude241_3⟩,⟨state241_6,exclude241_6⟩,⟨state241_8,exclude241_8⟩] 0x40018e0601c140e06040020905028200a08040014e06028200a0804002090501c140c0604001d000728200a08040020c0801c140c0804001d00051c140705040020c08028200a08040018810118580616040024e06020600818080008810120600818040018e06018580616040020210120600818040024a08018580a08040014210118580616040020a0802060081804000100002060081804000070601454070604000200011454051504000070602060081804001c41012060081804001cc08018580c0804001c41011858061604001cc0802060081804000090501c180706040000e06040000b06040000905080000905040000e0601c180706040000705040020705040000a0801c180a0804000070501c180706040000a08040000a0804000d00034000c908040018e06010404e0604001ca02030200c0804001ce06030200c08040018a02010404a060 (by decide +kernel)

def state241_10 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_10 : Impossible true (goalAt 241) 4 state241_10.toFinset :=
  node_ok cuts241 [] 0x24200a0801c18090801c18090802420070601c140908024201000728180a0802820021011c140a0802820100032c1408180242001101206008180282006160206006160206008180185805150 (by decide +kernel)

def state241_11 : List Sig := [0x5555555555555555555555555555555555555555000000005555555500000000,input 0,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_11 : Impossible true (goalAt 241) 4 state241_11.toFinset :=
  node_ok cuts241 [] 0x90802820070602420070602420090801c180a06028200a0800840441402420051502420011102820051502820051502818081012818090801c140908004404a0801c140a08008404a0602c140a0601c1408180 (by decide +kernel)

def state241_12 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_12 : Impossible true (goalAt 241) 4 state241_12.toFinset :=
  node_ok cuts241 [] 0x90802820070602420070502420090800440470602420090801c180705028200a08010404a06028200a0804002081802420011012060081802820041012060081012060081801c14061602c140a060281807050 (by decide +kernel)

def state241_13 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_13 : Impossible true (goalAt 241) 5 state241_13.toFinset :=
  node_ok cuts241 [⟨state241_10,exclude241_10⟩,⟨state241_11,exclude241_11⟩,⟨state241_12,exclude241_12⟩] 0x100082420090802820070602820100051c18070602820090802420100061c18070602818090802420100052420090802818070601c18070500440470504001c90802420070502420090804001c11010440411012060081802420051502420011011454051502420081802060041012060081802820061602820041011858061602820081802060100061858061602818081802060200022060081802818061601858200011454051501c14081802060200002060081801c140515014540a06010404a06040020a08028200a06028200a0804002041011040470501040470504000ca08028200705028200a0804000c410110405000240008b050 (by decide +kernel)

def state241_14 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaa,input 7,input 0,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_14 : Impossible true (goalAt 241) 4 state241_14.toFinset :=
  node_ok cuts241 [] 0x90802820070602420070602420090801c180b05028200a08024140818024200110120600818028200616020600616020600818018580706024200706024200301028200705028200616020600616020600a060 (by decide +kernel)

def state241_15 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_15 : Impossible true (goalAt 241) 4 state241_15.toFinset :=
  node_ok cuts241 [] 0x90803020070602420090802060070602060070602420090801c180706024200908018580210130200c08008404616030200c0804002081802820070502060070502060081801c14061602060081801c140a060 (by decide +kernel)

def state241_16 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_16 : Impossible true (goalAt 241) 5 state241_16.toFinset :=
  node_ok cuts241 [⟨state241_10,exclude241_10⟩,⟨state241_14,exclude241_14⟩,⟨state241_15,exclude241_15⟩] 0xd0501c180706028180908024200d0502420090802818070601c18100082420090803020070603020100051c18070603020090802420070502420090804001c70601c18070501c18070604001c908024200a06008404a06024040c08030200a06030200c08024040210124140810118580616028181000928180810180008810128180616018580110118580616024201000924200110140014110124200616024200210140020210130200616030200210118580616030201000830201000240008818028180705028180d05080004b05028182000028180d0501c140c06008405000328200c0801c140a0800840470501c140c0804000cc080 (by decide +kernel)

def state241_17 : List Sig := [0xffffffff000000000000000000000000aaaaaaaa,input 0,input 7,input 5,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_17 : Impossible true (goalAt 241) 4 state241_17.toFinset :=
  node_ok cuts241 [] 0x90801c18070602420070602420090801c180a0602c140a0603018081802420051502060081801858061602060061602060081801858090801c180908030200a08024140c08030200a06020600616020600c080 (by decide +kernel)

def state241_18 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_18 : Impossible true (goalAt 241) 5 state241_18.toFinset :=
  node_ok cuts241 [⟨state241_15,exclude241_15⟩,⟨state241_10,exclude241_10⟩,⟨state241_12,exclude241_12⟩,⟨state241_17,exclude241_17⟩] 0x2420070601c180908024200c0801c18090801c18090802420070601c18090802420070602820070502040600021c14070504000a00011c140410130200c08010406000330200c08040020a06020600908004404818020600705080000818020600c080104048180204048180400186160 (by decide +kernel)

def state241_19 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 0,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_19 : Impossible true (goalAt 241) 6 state241_19.toFinset :=
  node_ok cuts241 [⟨state241_13,exclude241_13⟩,⟨state241_16,exclude241_16⟩,⟨state241_18,exclude241_18⟩] 0x40018d0501c18070604001ca06024200908040014d05024200908040018a0601c18070604000870502420090804000900071c18070604000870501c180706040009000224200908040021000824200908040020c0801c180c0804002100051c180706040020c08024200908040018810118580616040024a06020600818080008810120600818040018a0601858061604001c11012060081804002490801454090804001411011454051504001c90802060081804000900022060081804000870501858061604000a000118580616040008705020600818040020410120600818040020c08018580c08040020410118580616040020c08020600818040008a0601c140a06040008d05040008b05040008a06080000a06040008d0501c140c0604000d00034000ca08040020a06010404a06040020901030200c08040020a06030200c080400209010104049050 (by decide +kernel)

def state241_20 : List Sig := [0xffffffff00000000ffffffff00000000ffffaaaa00000000ffffaaaa,input 7,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_20 : Impossible true (goalAt 241) 4 state241_20.toFinset :=
  node_ok cuts241 [] 0x38180c08030200a06024200c0801c18090801c180908024200706020600c08018580818020600908014540818018580818020600616028200705030200a08024200706024200a08020600616020600a08030180a08028200e060 (by decide +kernel)

def state241_21 : List Sig := [0xffffffffffffffff0000000000000000ffffaaaaffffaaaa,input 7,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_21 : Impossible true (goalAt 241) 4 state241_21.toFinset :=
  node_ok cuts241 [] 0x38180a08028200c06024200a0801c18090801c180908024200706020600a08018580818020600908014540818018580818020600616028200705028200c08024200706024200c08020600616020600c08028180c08030200e060 (by decide +kernel)

def state241_22 : List Sig := [0xffffffffffffffffffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaa,input 7,input 0,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_22 : Impossible true (goalAt 241) 5 state241_22.toFinset :=
  node_ok cuts241 [⟨state241_0,exclude241_0⟩,⟨state241_20,exclude241_20⟩,⟨state241_21,exclude241_21⟩] 0xd05030200c08024142000230200c0804000ca08030200705028200705028200a0801c142000128200a08040008908030202000024200908028200705024200d05024200908030140706020600c08014540818020600a08008404818020600908014540818014540818020600515018580e060 (by decide +kernel)

def state241_23 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaa,input 7,input 0,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_23 : Impossible true (goalAt 241) 5 state241_23.toFinset :=
  node_ok cuts241 [⟨state241_4,exclude241_4⟩] 0xe06030200c08028180a08030200705028200e06028200a08030180908030202000024200908028200705024200f06024200908038180818030200515020600818028200210120600818024200515020600e16020600818038180410130200410130200705028200705028200706024200110124200616020600515020600d050 (by decide +kernel)

def state241_24 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_24 : Impossible true (goalAt 241) 4 state241_24.toFinset :=
  node_ok cuts241 [] 0x14540c08030200815010404c08030200110128200c0801c140a0801c140a08028200515008404a08028200110120600c08010404818020600a0801c140818018580818020600c0501c180818020601000438180e060145404150 (by decide +kernel)

def state241_25 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_25 : Impossible true (goalAt 241) 5 state241_25.toFinset :=
  node_ok cuts241 [⟨state241_5,exclude241_5⟩,⟨state241_24,exclude241_24⟩] 0x10404c08030200410114540c08030200115028200c0801c140a0801c140a0802820070501c140a08028200515004404c08080000c0801c140a0801c140a08024200110120406000104404515004404515010540818030200410120600818028200705020600810120600818040010616020600818040000e060 (by decide +kernel)

def state241_26 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_26 : Impossible true (goalAt 241) 5 state241_26.toFinset :=
  node_ok cuts241 [⟨state241_24,exclude241_24⟩] 0x34140c08030200905010404c08030200110128200c0801c140a0801c140a08028200705008404a08028200110104440c08014540c08014540a08008404a08020600515030542000014540110114540515010540908030200410124200908028200705024200d05024200908030140706024200908040010e060 (by decide +kernel)

def state241_27 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 0,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_27 : Impossible true (goalAt 241) 6 state241_27.toFinset :=
  node_ok cuts241 [⟨state241_6,exclude241_6⟩,⟨state241_22,exclude241_22⟩,⟨state241_23,exclude241_23⟩,⟨state241_25,exclude241_25⟩,⟨state241_26,exclude241_26⟩] 0xe06010404e06028080c08030200e06030200c08028080410128180e0601c140e06034140a08028200e06028200a08034140705030181000728200a0803020070503020100051c140705030200a08028200d05004404d05038181000038180d05080010d0503818011013818100000440411013020100003020100004001e000030200110130200705004404705028201000028200705040014705028200110128201000040004908020404515014540e06040004e06020406000320404e06014540e06010404111004440c08014540c08010404515014540c08004440c08008404515014540a08040004a08008405000508404a08014540a08004405000004405000114540515040001000010541000040000818034141000434140e06080008e06034142000134140e06040010e06010405000310404c0804001cc08010405000710404c0804000cc0801c14100021c140a08040014a0801c14100051c140a08040008a080 (by decide +kernel)

def state241_28 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000ffff0000aaaa,input 7,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_28 : Impossible true (goalAt 241) 4 state241_28.toFinset :=
  node_ok cuts241 [] 0x38180c08030200a06028200c0801c140a08038180a08028200c06020600c08018580818020600a0801858081801858081802060061602420070603020090802420070602820090802060051502060090801c1809080242007060 (by decide +kernel)

def state241_29 : List Sig := [0xffffffffffffffff0000000000000000ffffffffaaaaaaaa,input 7,input 0,input 5,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_29 : Impossible true (goalAt 241) 4 state241_29.toFinset :=
  node_ok cuts241 [] 0x24200a0801c18090801c180908024200706038180a08028200c06020600908014540818020600a08018580818018580818020600616024200706024200c08028200705028200c08020600616020600c08028180c08030200e060 (by decide +kernel)

def state241_30 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa,input 7,input 0,input 5,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_30 : Impossible true (goalAt 241) 5 state241_30.toFinset :=
  node_ok cuts241 [⟨state241_10,exclude241_10⟩,⟨state241_28,exclude241_28⟩,⟨state241_29,exclude241_29⟩] 0xe06030200c08028182000230200c0804000c90803020070602420090802820070602420070602420090801c182000124200908040000a08030202000028200e06028200a08030180705020600c08018580818020600908004404818020600a08018580818018580818020600616014540d050 (by decide +kernel)

def state241_31 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaa,input 7,input 0,input 5,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_31 : Impossible true (goalAt 241) 5 state241_31.toFinset :=
  node_ok cuts241 [⟨state241_14,exclude241_14⟩] 0xd05030200c0802414090803020070602420090802820070602420070602420090801c180a08030202000028200f05028200a08034140818030200616020600818024200110120600818028200616020600616020600818018580410130200410130200706024200706024200705028200210128200616020600616020600e060 (by decide +kernel)

def state241_32 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_32 : Impossible true (goalAt 241) 4 state241_32.toFinset :=
  node_ok cuts241 [] 0x18580c08030200816010404c08030200210124200c0801c18090802420081801c18081801c180908024200616004404908024200110120600c08010404818018580818020600c0601c1408180206010004341406160185804160 (by decide +kernel)

def state241_33 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 5,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_33 : Impossible true (goalAt 241) 5 state241_33.toFinset :=
  node_ok cuts241 [⟨state241_15,exclude241_15⟩,⟨state241_32,exclude241_32⟩] 0x10404c08030200410118580c08030200216024200c0801c18090802420070601c18090802420081801c18081801c18090802420070601c180908024200616008404c08080000c08028200210120406000108404616008404616010580818030200410120600810120600818040010616020600818040008e060 (by decide +kernel)

def state241_34 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_34 : Impossible true (goalAt 241) 5 state241_34.toFinset :=
  node_ok cuts241 [⟨state241_32,exclude241_32⟩] 0x38180c08030200a06010404c08030200210124200c0801c180908024200a0801c18090801c180908024200706004404908024200110108480c08018580c08018580908004404908020600616030582000018580210118580616010580a08030200410128200e06028200a08030180705028200a08040010d050 (by decide +kernel)

def state241_35 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 5,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_35 : Impossible true (goalAt 241) 6 state241_35.toFinset :=
  node_ok cuts241 [⟨state241_16,exclude241_16⟩,⟨state241_30,exclude241_30⟩,⟨state241_31,exclude241_31⟩,⟨state241_33,exclude241_33⟩,⟨state241_34,exclude241_34⟩] 0xe06010404e06028080c08030200e06030200c08028080410128180d0501c180706038180908024200d0502420090803818070601c18100082420090803020070603020100051c18070603020090802420100022420090800840470601c18100051c18070600840490802420100052420090804000070601c18100051c180706040000908024200e06008404e06034141000234140e06080010e06034140210134141000208404210130201000230201000240022000030200210130201000240004a08020404616018580e06040004e06020406000320404e06018580616010404212008480c08018580c08010404616018580c08008480c08004404616018580908040004908004405000504404908018580908008405000208405000118580616040009000210581000240008818038181000438180d05080008d05038182000138180d05040010d05010405000310404c08040020c08010405000810404c0804000cc080 (by decide +kernel)

def state241_36 : List Sig := [0xffff000000000000ffffffff00000000ffff000000000000ffffaaaa,input 4,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_36 : Impossible true (goalAt 241) 3 state241_36.toFinset :=
  node_ok cuts241 [] 0x1858081802060061602060090801454081801c18090802420070601c140a08028200a06020600616020600a08024200706024200a080 (by decide +kernel)

def state241_37 : List Sig := [0xffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffaaaaffffaaaa,input 4,input 0,input 7,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_37 : Impossible true (goalAt 241) 4 state241_37.toFinset :=
  node_ok cuts241 [⟨state241_36,exclude241_36⟩] 0xe06028200a08030180818028200616020600616020600818018580818024200515020600616020600818030200908028200705024200905024200908038180706028202000028200c08028180c08030200e060 (by decide +kernel)

def state241_38 : List Sig := [0xffff000000000000ffff0000ffff0000ffff000000000000ffff0000aaaa,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_38 : Impossible true (goalAt 241) 3 state241_38.toFinset :=
  node_ok cuts241 [] 0x18580818020600616020600a08018580818028180a0802820070501c1809080242007060206005150206009080242007060282009080 (by decide +kernel)

def state241_39 : List Sig := [0xffffffff00000000ffffffffffffffffffffffff00000000ffffffffaaaaaaaa,input 5,input 0,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_39 : Impossible true (goalAt 241) 4 state241_39.toFinset :=
  node_ok cuts241 [⟨state241_38,exclude241_38⟩] 0x70602420090801c180908028200706024202000024200908030200818024200515020600616020600818018580818028200616020600515020600818030200a06028200a08034140705028180c08030200d050 (by decide +kernel)

def state241_40 : List Sig := [0xffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa,input 0,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_40 : Impossible true (goalAt 241) 5 state241_40.toFinset :=
  node_ok cuts241 [⟨state241_7,exclude241_7⟩,⟨state241_17,exclude241_17⟩,⟨state241_37,exclude241_37⟩,⟨state241_39,exclude241_39⟩] 0x38180705038180d05028200a08038180a08028200d0501c140c0601c140908024200a0801c180a0801c14070601c180a0802420090803414070601c180e06024200908034140908024200e0601c180706008404818020600a08018580a08008404616018580a08020600818004404818020600908014540908004404515014540908020600818020404616018580e06020600818020404818020600e06018580616028200c08028200705080004705028202000328200705030200c08024200c08024200706080000706024202000224200706030200c08020404410128180e06030200c08020404c08030200e06010404e06020600c08020600616010404616020600410120600616030200c080 (by decide +kernel)

def state241_41 : List Sig := [0xffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa,input 4,input 0,input 7,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_41 : Impossible true (goalAt 241) 5 state241_41.toFinset :=
  node_ok cuts241 [⟨state241_7,exclude241_7⟩] 0xd05030200c08024140a08030200705028200705028200a0801c14081803020051502060081802820021012060051502060081801454081801c18051502060030203020070603020070502820070602820070603c180d0501c180c08080000c0804000ca0801c140a0801c140e060381808101341408180185808180145409080 (by decide +kernel)

def state241_42 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_42 : Impossible true (goalAt 241) 5 state241_42.toFinset :=
  node_ok cuts241 [⟨state241_2,exclude241_2⟩,⟨state241_24,exclude241_24⟩] 0x34140c08030200905010404c08030200410128200c0801c140a0801c140a08028200705008404a08028200210120600c08010404818020600a08008404818018580818024202000120600810120600818040004e06038180d05040000908030202000024200908028200705024200d050242009080301407060 (by decide +kernel)

def state241_43 : List Sig := [0xffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa,input 5,input 0,input 7,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_43 : Impossible true (goalAt 241) 5 state241_43.toFinset :=
  node_ok cuts241 [⟨state241_17,exclude241_17⟩] 0xe06030200c0802818090803020070602420070602420090801c18090801c180706024200818030200616020600818024200110120600616020600818018580818018580616020600301030200705030200e0603c140e0601c140c08080000c0804000c90801c18090801c180d05038180810138180818018580818018580a080 (by decide +kernel)

def state241_44 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_44 : Impossible true (goalAt 241) 5 state241_44.toFinset :=
  node_ok cuts241 [⟨state241_12,exclude241_12⟩,⟨state241_32,exclude241_32⟩] 0x38180c08030200a06010404c08030200410124200c0801c18090801c180908024200706024200a0801c180908004404908024200110120600c08010404818020600908004404818018580818028202000120600810120600818040004d05038180e06040008a08030202000028200e06028200a080301807050 (by decide +kernel)

def state241_45 : List Sig := [0xffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_45 : Impossible true (goalAt 241) 5 state241_45.toFinset :=
  node_ok cuts241 [] 0x1c140a0802820070501c140a08028200705024200a0801c18090801c18090802420070601c180908024200706038180818028200210120600818024200110120600810120601000618580a0801c140a0803020090801c180908030200410130200c080104048180104048180302010003 (by decide +kernel)

def state241_46 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_46 : Impossible true (goalAt 241) 6 state241_46.toFinset :=
  node_ok cuts241 [⟨state241_25,exclude241_25⟩,⟨state241_33,exclude241_33⟩,⟨state241_22,exclude241_22⟩,⟨state241_8,exclude241_8⟩,⟨state241_30,exclude241_30⟩,⟨state241_18,exclude241_18⟩,⟨state241_40,exclude241_40⟩,⟨state241_41,exclude241_41⟩,⟨state241_42,exclude241_42⟩,⟨state241_43,exclude241_43⟩,⟨state241_44,exclude241_44⟩,⟨state241_45,exclude241_45⟩] 0x1000410404410120404c08030201000630200c0802040441011040500068002e00064000cc08030201000630200c0804000d00064000d000628200a0803020070503020200051c140705030200a0802820100041c140705020404a08028202000a28200a0802040470501c14200091c140705040008a08028202000428200a0804000870501c14100062420090803020070603020200031c18070603020090802420070502420090802820070602820070501c18070602820090802420100041c18070602040490802420200082420090802040470601c18200071c18070604000090802420200022420090804000070601c181000440004e06010404818020600c08040004c08010405000610404c08020600818008404818020600a08040004a08008406000108404a080206008180044048180206009080400049080044060000044049080206008180204050004204050001206008180400110004400110004400106160 (by decide +kernel)

def state241_47 : List Sig := [0x5555555555555555555555555555555555550000555500005555000055550000,input 0,input 4,input 7,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_47 : Impossible true (goalAt 241) 5 state241_47.toFinset :=
  node_ok cuts241 [⟨state241_1,exclude241_1⟩] 0xd05030200c08024140a08030200705028200705028200a0801c140908030202000024200908028200705024200d05024200908030140212030200616030200414028200616028200616038580810118580616024200110124200c08010404c08010404a08008404a08008404e06038180d0502040490801c1809080044048180 (by decide +kernel)

def state241_48 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_48 : Impossible true (goalAt 241) 6 state241_48.toFinset :=
  node_ok cuts241 [⟨state241_3,exclude241_3⟩,⟨state241_22,exclude241_22⟩,⟨state241_26,exclude241_26⟩,⟨state241_42,exclude241_42⟩,⟨state241_47,exclude241_47⟩] 0xd05010404d05024040c08030200d05030200c0802404041012414100061040441014000cc08030201000630200c0804000c410110405000628200a0803020070503020100051c140705030200a0802820100041c140705034140a08028201000528200a0803414070501c141000508404210140008a08028201000528200a08040008210108404410120600818030200616030200410118580616030200818020600210120600818028200616028200210118580616028200818020601000418580616034140818020602000320600818034140616018581000020600818024200515024202000214540515024200818020602000418580616040004818020602000120600818040004616018581000040000e06040000908024200c08040000c08040001000680000c0802420090801c140908024200a08040000a0801c14100051c140a080242009080341410004341410000242009080400010000301410000400107060 (by decide +kernel)

def state241_49 : List Sig := [0x5555555555555555555555555555555555555555000000005555555500000000,input 0,input 5,input 7,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_49 : Impossible true (goalAt 241) 5 state241_49.toFinset :=
  node_ok cuts241 [⟨state241_11,exclude241_11⟩] 0xe06030200c0802818090803020070602420070602420090801c180908028200706024200a08030202000028200e06028200a08030180111030200515030200414024200515024200515038180810138180515028200210128200c08010404c08010404908004404908004404e06034140e06020404a0801c140a080084048180 (by decide +kernel)

def state241_50 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_50 : Impossible true (goalAt 241) 6 state241_50.toFinset :=
  node_ok cuts241 [⟨state241_13,exclude241_13⟩,⟨state241_30,exclude241_30⟩,⟨state241_34,exclude241_34⟩,⟨state241_44,exclude241_44⟩,⟨state241_49,exclude241_49⟩] 0xe06010404e06028080c08030200e06030200c0802808041012818100081040441014000cc08030201000830200c0804000c41011040500082420090803020070603020100051c18070603020090802420100041c18070603818090802420100052420090803818070601c18100022420090802820070602820100051c180706028200908024201000504404110140000908024201000524200908040000110104404410120600818030200616030200410118580616030200818020600110120600818024200515024200110114540515024200818020601000418580616038180818020602000320600818038180616018581000220600818028200616028202000218580616028200818020602000414540515040004818020602000120600818040004515014541000240008d05040008a08028200c08040008c08040009000880000c08028200a08038181000438181000228200a080400090002301810002400107050 (by decide +kernel)

def state241_51 : List Sig := roots 241
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_51 : Impossible true (goalAt 241) 7 state241_51.toFinset :=
  node_ok cuts241 [⟨state241_9,exclude241_9⟩,⟨state241_19,exclude241_19⟩,⟨state241_27,exclude241_27⟩,⟨state241_35,exclude241_35⟩,⟨state241_46,exclude241_46⟩,⟨state241_48,exclude241_48⟩,⟨state241_50,exclude241_50⟩] 0x4000ce06010404e0604000ca02030200c0804000ce06030200c0804000ca02010404a06040010e0601c140e06040008d05028200a08080018e06028200a08040008d0501c140c0604000d000328200a0804000cc0801c140c0804000e00011c14070504000cc08028200a08040010d0501c180706040000e06024200908080014d05024200908040000e0601c18070604000d00032420090804000cc0801c180c0804000e00001c18070604000cc08024200908040008705024200908040000a0801c180a0804001470501c180706040000a08024200908040010810118580616040004e06020600818080010810120600818040010e0601858061604000c41012060081804000cc08018580c0804000c41011858061604000cc08020600818040008210120600818040004a08018580a0808000c210118580616040008a080206008180400001101206008180400049080145409080800081101145405150400009080206008180 (by decide +kernel)

theorem lower241 : Claim 241 8 :=
  fromSearch 4 (by decide +kernel) exclude241_51

theorem lower245 : Claim 245 9 :=
  fromLift 9 4 1540 lower241 (by decide +kernel)

def cuts196 : Cuts (goalAt 196) := []

def state196_0 : List Sig := roots 196
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude196_0 : Impossible true (goalAt 196) 3 state196_0.toFinset :=
  node_ok cuts196 [] 0x30100440430100840430200c08030100c08030200840411010440421010444011100c04021200848021010848021200c04011100444011010848021200c08011100c08011010444011100c080212008480 (by decide +kernel)

theorem lower196 : Claim 196 4 :=
  fromSearch 570426880 (by decide +kernel) exclude196_0

theorem lower228 : Claim 228 5 :=
  fromLift 5 32 577766912 lower196 (by decide +kernel)

theorem lower212 : Claim 212 5 :=
  fromLift 5 16 570885632 lower196 (by decide +kernel)

theorem lower180 : Claim 180 5 :=
  fromLift 5 4 541394688 lower176 (by decide +kernel)

def rule244_0 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower228 none (by decide +kernel)

def rule244_1 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower240 none (by decide +kernel)

def rule244_2 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower212 none (by decide +kernel)

def rule244_3 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower180 none (by decide +kernel)

def cuts244 : Cuts (goalAt 244) := [rule244_0,rule244_1,rule244_2,rule244_3]

def state244_0 : List Sig := roots 244
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_0 : Impossible true (goalAt 244) 6 state244_0.toFinset :=
  node_ok cuts244 [] 0x4000ce06019090e0604000ca42430200c0804000ce06030200c0804000ca42419090a06040008e0601c140e06040008d05028200a08040008e06028200a08040008d0501c140c06040008642428200a08040008c0801c140c0804000864241c140705040008c08028200a08040000d0501c180706040000e06024200908040000d05024200908040000e0601c180706040000541424200908040000c0801c180c0804000054141c180706040000c08024200908040000705024200908040000a0801c180a0804000070501c180706040000a08024200908040004a42419180646040004e06021200848040004a42421200848040004e06019180646040004642421200848040004c08019180c08040004642419180646040004c08021200848040004341421200848040004a08019180a08040004341419180646040004a080212008480400003424212008480400009080151409080400003424151405450400009080212008480 (by decide +kernel)

theorem lower244 : Claim 244 7 :=
  fromSearch 574948864 (by decide +kernel) exclude244_0

def cuts50 : Cuts (goalAt 50) := []

def state50_0 : List Sig := roots 50
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude50_0 : Impossible true (goalAt 50) 3 state50_0.toFinset :=
  node_ok cuts50 [] 0xc04012020c04022020c08030200c04030200c0802202048081202088081210048403010088802220088082220088803010048401210048082220088803020048403020048081210048403020088802220 (by decide +kernel)

theorem lower50 : Claim 50 4 :=
  fromSearch 1114176 (by decide +kernel) exclude50_0

theorem lower114 : Claim 114 5 :=
  fromLift 5 64 17891392 lower50 (by decide +kernel)

def cuts102 : Cuts (goalAt 102) := []

def state102_0 : List Sig := roots 102
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude102_0 : Impossible true (goalAt 102) 3 state102_0.toFinset :=
  node_ok cuts102 [] 0x190904606110904424190906460191804206111006460191804460098906260189802624109006260189804260189806460098906260 (by decide +kernel)

theorem lower102 : Claim 102 4 :=
  fromSearch 17827408 (by decide +kernel) exclude102_0

def cuts86 : Cuts (goalAt 86) := []

def state86_0 : List Sig := roots 86
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude86_0 : Impossible true (goalAt 86) 3 state86_0.toFinset :=
  node_ok cuts86 [] 0x150504606110504414150505450151404206111005450151404450058505250149401614109005250149404250149405450058505250 (by decide +kernel)

theorem lower86 : Claim 86 4 :=
  fromSearch 16844352 (by decide +kernel) exclude86_0

def rule118_0 : {c : Cut // CutGood (goalAt 118) c} :=
  ruleFor 118 lower114 none (by decide +kernel)

def rule118_1 : {c : Cut // CutGood (goalAt 118) c} :=
  ruleFor 118 lower102 none (by decide +kernel)

def rule118_2 : {c : Cut // CutGood (goalAt 118) c} :=
  ruleFor 118 lower86 none (by decide +kernel)

def rule118_3 : {c : Cut // CutGood (goalAt 118) c} :=
  ruleFor 118 lower50 none (by decide +kernel)

def cuts118 : Cuts (goalAt 118) := [rule118_0,rule118_1,rule118_2,rule118_3]

def state118_0 : List Sig := [0xfcfcfcfcfcfcfcfc0000000000000000fcfcfcfcfcfcfcfc,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_0 : Impossible true (goalAt 118) 4 state118_0.toFinset :=
  node_ok cuts118 [] 0x1c14070601c18012060585070500989070500989070600585070601898054501918064601514064601c18054501918044241c14064241c14034241c18034241c1802624108182624188910003 (by decide +kernel)

def state118_1 : List Sig := [0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 1,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_1 : Impossible true (goalAt 118) 5 state118_1.toFinset :=
  node_ok cuts118 [⟨state118_0,exclude118_0⟩] 0x64240d05064241505070501c14064241c14070501505034140c14054140d09034241909070601c18054141c18070601909034240c18070500481870500881870601c18070501c18070600881812060481842060989026241909100031889042064000c42061909026240989022060585016141c14026241c14022060989026241c14016141c14012060989026241c18016141c18012060585016141c18026241c18100004000062601909100031909200001918064601909064601918100034000d00030d05054501514070501918064600d05064601918070501514054500d09064601918070601514070600d0905450151407060191806460 (by decide +kernel)

def state118_2 : List Sig := [0xffffcccc00000000ffffcccc00000000ffffcccc00000000ffffcccc,input 1,input 4,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_2 : Impossible true (goalAt 118) 4 state118_2.toFinset :=
  node_ok cuts118 [] 0x1109064601918042061918070601514064600d09070601c18030400989062601898026241898064600989062601898070601494062600c14070501c14044241514064601514064600581870601c1407060149406260149406260 (by decide +kernel)

def state118_3 : List Sig := [0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 1,input 4,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_3 : Impossible true (goalAt 118) 5 state118_3.toFinset :=
  node_ok cuts118 [⟨state118_2,exclude118_2⟩] 0x64241c14070500c14064241918064601081854501918064601514064601514054501918064601514054501918054141909054141909070500981870500581870600585052501494064241494070500981852501494064600585064600581852501094062601505064241505064241c14200001c1410002 (by decide +kernel)

def state118_4 : List Sig := [0xf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfc,input 1,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_4 : Impossible true (goalAt 118) 4 state118_4.toFinset :=
  node_ok cuts118 [] 0x1909070501c14030500d09070601c18030601c14070601c18016060989052501494026241494070500989052501c9807060149407060189806260098906460190906460191810003151406460191805450191807060151406460 (by decide +kernel)

def state118_5 : List Sig := [0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,input 1,input 4,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_5 : Impossible true (goalAt 118) 5 state118_5.toFinset :=
  node_ok cuts118 [⟨state118_4,exclude118_4⟩] 0x64241c14070500c14064241918064601081854501918064601514064601c18054501918034241c18070600c18070501c18070600981816141494052501909052501c1402606149405250191801614191807260149407060118186424118186424098187050098187050400006460800006460058186260 (by decide +kernel)

def state118_6 : List Sig := [0xffff0000cccc0000ffff0000cccc0000ffff0000cccc0000ffff0000cccc,input 1,input 5,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_6 : Impossible true (goalAt 118) 4 state118_6.toFinset :=
  node_ok cuts118 [] 0x1909064601918042061514064601918054501909070501c14030400989062601898026241898064600989062601494062601898052500c18070601c18034241918054501918070600581870601c1807050189805250189807060 (by decide +kernel)

def state118_7 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 1,input 5,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_7 : Impossible true (goalAt 118) 5 state118_7.toFinset :=
  node_ok cuts118 [⟨state118_6,exclude118_6⟩] 0x34241c18070600c18016061c18070600581a00001c18070604000464241918064601081864601c1805450191805450191806460151405450191806460151406424150506424150507050098906260189802624189807060058186260189806460098906260098186260109805250190905414190905414 (by decide +kernel)

def state118_8 : List Sig := [0xf0f0f0f0fcfcfcfcf0f0f0f0fcfcfcfcf0f0f0f0fcfcfcfcf0f0f0f0fcfcfcfc,input 1,input 5,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_8 : Impossible true (goalAt 118) 4 state118_8.toFinset :=
  node_ok cuts118 [] 0xd09070601c18030601c14070601c18012061909070501c14030500989062601898026241898070600585062601c9406260189807050189806460098906260190906460191810003191807060151406460151406460191805450 (by decide +kernel)

def state118_9 : List Sig := [0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,input 1,input 5,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_9 : Impossible true (goalAt 118) 5 state118_9.toFinset :=
  node_ok cuts118 [⟨state118_8,exclude118_8⟩] 0x34241c18070600c18070501c18070600581864241918064601081864601c18054501918054501918064601514064241c14070500c14026241898062600989062601c1801606189806260191802624189807250189807050118186424118186424058187060058187060400006460800006460098185250 (by decide +kernel)

def state118_10 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_10 : Impossible true (goalAt 118) 5 state118_10.toFinset :=
  node_ok cuts118 [] 0x64241918064601081854501918064601514064601c18054501918044401918064601110026241898062600989062601918026241898052501898062601494062601c18052501898042401898062601090064241c14070500c14026060d09070601c18030601c1407060400041606190904606190904606 (by decide +kernel)

def state118_11 : List Sig := roots 118
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_11 : Impossible true (goalAt 118) 6 state118_11.toFinset :=
  node_ok cuts118 [⟨state118_1,exclude118_1⟩,⟨state118_3,exclude118_3⟩,⟨state118_5,exclude118_5⟩,⟨state118_7,exclude118_7⟩,⟨state118_9,exclude118_9⟩,⟨state118_10,exclude118_10⟩] 0x4000c64240d05064244000854141c14070504000c64241c14070504000854140d05030504000c54140d09034244000464241c18070604000c54141c18070604000464240d09030604000870500581870504000426061c18070608001470501c18070604000426060581816064000064244000c64244000042021918064604000064241918064604000042024000042064000034141514054504000070501918064604000034141918064604000070501514054504000034241918064604000070601514070604000034241514054504000070601918064604000c46060989026244000c64241898062604000c46061898062604000c64240989026244000826061494052508001070501898062608000c2606189806260400087050149405250400041606189806260800087060149407060800041606149405250400047060189806260400010000189806260400006460098906460400020000098902624400006460189806260 (by decide +kernel)

theorem lower118 : Claim 118 7 :=
  fromSearch 17892928 (by decide +kernel) exclude118_11

theorem lower242 : Claim 242 6 :=
  fromLift 6 2 1091633216 lower240 (by decide +kernel)

theorem lower230 : Claim 230 6 :=
  fromLift 6 2 554698320 lower228 (by decide +kernel)

theorem lower214 : Claim 214 6 :=
  fromLift 6 2 553715264 lower212 (by decide +kernel)

theorem lower178 : Claim 178 5 :=
  fromLift 5 2 1074856000 lower176 (by decide +kernel)

def cuts166 : Cuts (goalAt 166) := []

def state166_0 : List Sig := roots 166
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude166_0 : Impossible true (goalAt 166) 3 state166_0.toFinset :=
  node_ok cuts166 [] 0x29090a28228a08842429090868221a08a02421a08a28208818868209890a42421018262428a08a08028208a08221a088480212088482 (by decide +kernel)

theorem lower166 : Claim 166 4 :=
  fromSearch 537921360 (by decide +kernel) exclude166_0

def cuts150 : Cuts (goalAt 150) := []

def state150_0 : List Sig := roots 150
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude150_0 : Impossible true (goalAt 150) 3 state150_0.toFinset :=
  node_ok cuts150 [] 0x25050928224a08841425050868221a08901421a08928204818868205850941421018161424a08908024208908221a088480212088482 (by decide +kernel)

theorem lower150 : Claim 150 4 :=
  fromSearch 536938304 (by decide +kernel) exclude150_0

def rule182_0 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower180 none (by decide +kernel)

def rule182_1 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower50 none (by decide +kernel)

def rule182_2 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower178 none (by decide +kernel)

def rule182_3 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower166 none (by decide +kernel)

def rule182_4 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower150 none (by decide +kernel)

def rule182_5 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower176 none (by decide +kernel)

def cuts182 : Cuts (goalAt 182) := [rule182_0,rule182_1,rule182_2,rule182_3,rule182_4,rule182_5]

def state182_0 : List Sig := [0xfffffffffffff0f0fffffffffffff0f0fffffffffffff0f0fffffffffffff0f0,input 5,input 4,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_0 : Impossible true (goalAt 182) 4 state182_0.toFinset :=
  node_ok cuts182 [] 0x9890a02421018262409890302405850262405850262409890161421a0884802120884820c090a0242105030240c05030240c090120624a08a02424050842421090a28228090868221a090001 (by decide +kernel)

def state182_1 : List Sig := [0xfffff0f000000000fffff0f000000000fffff0f000000000fffff0f0,input 5,input 4,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_1 : Impossible true (goalAt 182) 4 state182_1.toFinset :=
  node_ok cuts182 [] 0x26242809084060989026240c090161409890a28228200a0822820830242809084140c090b28228a08302428a08a02428a08a28209a08901421a08868228090848021a08848221208868224a08120621a083014 (by decide +kernel)

def state182_2 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 4,input 1,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_2 : Impossible true (goalAt 182) 5 state182_2.toFinset :=
  node_ok cuts182 [⟨state182_0,exclude182_0⟩,⟨state182_1,exclude182_1⟩] 0xa4240c050a42424050a28228a08a42428a08a28224050301421090860609890262429091000529090860640004840629090262409890a28205850a28228200262428200a28209890a0822820016142820812060989026240c09016140c09012060585016140c09026240989086820888086822120026242120086820989084822120022202120890140c09030242909100032909090144000484142909030240c090301404818301428a08302428a0830140c090302428a08120628a09000240008928229091000129090a02021a08868229090868221a08a02040004a0240c050868221a08a28280004a2820c05200000c050a28221a088682 (by decide +kernel)

def state182_3 : List Sig := [0xffff0000f0f00000ffff0000f0f00000ffff0000f0f00000ffff0000f0f0,input 4,input 5,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_3 : Impossible true (goalAt 182) 4 state182_3.toFinset :=
  node_ok cuts182 [] 0x262428090840609890161409890262405850928224200908224208a02424050842421090901424a0892822809092822ca08301424a08a02421a08868224050848021a08848221208868228a08220621a083024 (by decide +kernel)

def state182_4 : List Sig := [0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 5,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_4 : Impossible true (goalAt 182) 5 state182_4.toFinset :=
  node_ok cuts182 [⟨state182_0,exclude182_0⟩,⟨state182_3,exclude182_3⟩] 0x94140c090302428090928224a08941424a0892822809030240c090301424a0892820881830240c09030140c090302408818928224a0a000124a08928221a08302421a0a00000c090302421a08928221a0886060989026242809100052809086064000484062809026240989092820989092822420016142420092820585090822420026242420822060585016140c05026240989022060989026240c050161405850868204840868221200262421200868209890848221200121021208a0240c050a02425051000425050a02440004842425050301421091000240008a28228091000128090901021a08868228090868221a089010400049014 (by decide +kernel)

def state182_5 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,input 4,input 5,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_5 : Impossible true (goalAt 182) 4 state182_5.toFinset :=
  node_ok cuts182 [] 0x29090848221208a02421208a2820c05084822120892820c090848229090a28228a0822800d090928224a08342424a08a2820d090928209890840629090262408890848209890848228208a08209890a2822420890820d0909282 (by decide +kernel)

def state182_6 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_6 : Impossible true (goalAt 182) 5 state182_6.toFinset :=
  node_ok cuts182 [⟨state182_0,exclude182_0⟩,⟨state182_5,exclude182_5⟩] 0xa42421a0886822809086820c040301421a0886820c080302421a0886824000a000021a0826242909084060989086822120084822120816140989026240585026240d090161409892000109890262440000a42425050a4240d050a2820d090a4242505034240d05034244000c9282290908606290908606 (by decide +kernel)

def state182_7 : List Sig := roots 182
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_7 : Impossible true (goalAt 182) 6 state182_7.toFinset :=
  node_ok cuts182 [⟨state182_2,exclude182_2⟩,⟨state182_4,exclude182_4⟩,⟨state182_6,exclude182_6⟩] 0x40004a4240d050a42440010941428a08a28240004a42428a08a2824001094140d05084244000494140d09034244000ca42424a08928240004941424a0892824000ca4240d090342440010341424a0892824000ca2820d090a2828000834140d09034244000ca28224a08928240008a42440004a42440008a02021a08868240008a42421a08868240008a02040008a02440008341421a08868240008a28240008a28240008341480004301440008a28221a08868240008342421a08868240008928240008928240008342480000302440008928221a08868240000860609890262440000a42440000a42440000860640004840640000a42409890262440000a28205850a28240000a08009890a08040000a28209890a08240000a08005850a082400009282098909282400009080058509080400009282058509082400009080098909082400008682088808682400008480098908480400008682098908482400008480088808482 (by decide +kernel)

theorem lower182 : Claim 182 7 :=
  fromSearch 537986880 (by decide +kernel) exclude182_7

theorem lower198 : Claim 198 5 :=
  fromLift 5 2 553649760 lower196 (by decide +kernel)

def rule246_0 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower244 none (by decide +kernel)

def rule246_1 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower118 none (by decide +kernel)

def rule246_2 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower242 none (by decide +kernel)

def rule246_3 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower230 none (by decide +kernel)

def rule246_4 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower214 none (by decide +kernel)

def rule246_5 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower182 none (by decide +kernel)

def rule246_6 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower198 none (by decide +kernel)

def rule246_7 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower178 none (by decide +kernel)

def rule246_8 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower114 none (by decide +kernel)

def rule246_9 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower228 none (by decide +kernel)

def rule246_10 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower212 none (by decide +kernel)

def cuts246 : Cuts (goalAt 246) := [rule246_0,rule246_1,rule246_2,rule246_3,rule246_4,rule246_5,rule246_6,rule246_7,rule246_8,rule246_9,rule246_10]

def state246_0 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 2,input 4,input 1,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_0 : Impossible true (goalAt 246) 7 state246_0.toFinset :=
  node_ok cuts246 [] 0xe06019090e06029090c28230a08e06030a08c28229090642428180e0601c140e06034140a28228a08e06028a08a28234140705030180642428a08a28230a08705030a0864241c140705030a08a28228a08860618980626038181000838180860640020840638180626018980c28209890c28230200626030200c28218980c08230200262430208a28214940a28228200626028200a28218980a0822820052502820816061898062600d09052501494016061494052500d090626018981000218980626015140262415141000909890262415140626018981000918980626040000525014941000914940525040000626018980d0500d090d05038181000338180d05040020d0503818034243818054140d090342430a09000330a0854144001c441430a08342430a08705005818705028a08342428a0870500d090705028a08160628a09000240008928229090545015140e06040008e06029091000829090e06015140e06019091000719090c28215140c28219090545015140c28240008c2820d050545015140a28240008a2820d05100060c050a28215140a2820d09100030d09100021514054504000900021114100024000c868234141000134140e06040020e06034141000834140e06040004e06019091000519090c2824001cc28219091000719090c28240014c2821c14100041c140a28240018a2821c14100061c140a28240010a282 (by decide +kernel)

def state246_1 : List Sig := [0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 2,input 5,input 1,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_1 : Impossible true (goalAt 246) 7 state246_1.toFinset :=
  node_ok cuts246 [] 0xe06019090e06029090c28230a08e06030a08c28229090642428180d0501c180706038180928224a08d05024a0892823818070601c180541424a08928230a08706030a0854141c180706030a08928224a08341424a0892820981870601c18034141c180706009818928224a09000624a0892824000c70601c18100061c18070604000c928224a08860618980626038181000838180860640020840638180626018980c28209890c28230200626030200c28218980c0823020026243020892821898092822420052502420092821494090822420062602420826061494052500d05062601898026061898062600d050525014941000218980626019180262419181000a09890262419180626018981000a14940525040000626018981000a18980626040000525014940e0600d050e06034141000434140e06040020e0603414034143414064240d050642430a09000430a0864244001c442430a08341430a09000240008a28229090646019180e06040008e06029091000828090e06019180646019091000719090c28219180c28219090646019180c28240008c2820d09064601918092824000892820d09100060c09092821918092820d05100040d051000219180646040009000211181000240010868238181000138180d05040020d05038181000838180d05040004d05019091000519090c2824001cc28219091000719090c28240014c282 (by decide +kernel)

def state246_2 : List Sig := roots 246
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_2 : Impossible true (goalAt 246) 8 state246_2.toFinset :=
  node_ok cuts246 [⟨state246_0,exclude246_0⟩,⟨state246_1,exclude246_1⟩] 0x40004e06019090e06040004a42430a08c28240004e06030a08c28240004a42419090a06040004e0601c140e06040004d05028a08a28240004e06028a08a28240004d0501c140c06040014642428a08a28240014c2821c140c2824001464241c140705040014c28228a08a28240004d0501c180706040004e06024a08928240004d05024a08928240004e0601c180706040014541424a08928240014c2821c180c2824001454141c180706040014c28224a08928240010705024a0892824000ca2821c180a2824001870501c180706040010a28224a08928240004a42419180646040004e06021a08868240004a42421a08868240004e06019180646040014642421a08868240014c28219180c28240014642419180646040014c28221a08868240010341421a08868240008a28219180a28280004341419180646040008a28221a0886824000c342421a08868240008928215140928280000342415140545040008928221a08868240004860618980626040004e06040004e06040004860640004840640004e06018980626040000c28209890c28240000c08018980c08040000c28218980c08240000c08009890c08240000a28214940a28240000a08018980a08040000a28218980a08240000a08014940a082400009282189809282400009080149409080400009282149409082400009080189809082400008682189808682400008480098908480400008682098908482400008480189808482 (by decide +kernel)

theorem lower246 : Claim 246 9 :=
  fromSearch 554763840 (by decide +kernel) exclude246_2

theorem lower243 : Claim 243 9 :=
  fromLift 9 2 68 lower241 (by decide +kernel)

theorem lower163 : Claim 163 5 :=
  fromLift 5 2 85 lower161 (by decide +kernel)

theorem lower147 : Claim 147 5 :=
  fromLift 5 2 68 lower145 (by decide +kernel)

theorem lower51 : Claim 51 5 :=
  fromLift 5 1 68 lower50 (by decide +kernel)

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

theorem lower183 : Claim 183 9 :=
  fromLift 9 4 1860 lower179 (by decide +kernel)

theorem lower197 : Claim 197 5 :=
  fromLift 5 1 1542 lower196 (by decide +kernel)

theorem lower149 : Claim 149 5 :=
  fromLift 5 4 1796 lower145 (by decide +kernel)

def rule213_0 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower209 none (by decide +kernel)

def rule213_1 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower212 none (by decide +kernel)

def rule213_2 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower197 none (by decide +kernel)

def rule213_3 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower149 none (by decide +kernel)

def cuts213 : Cuts (goalAt 213) := [rule213_0,rule213_1,rule213_2,rule213_3]

def state213_0 : List Sig := roots 213
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_0 : Impossible true (goalAt 213) 6 state213_0.toFinset :=
  node_ok cuts213 [] 0x4000cd05015050d0504000c941430200c0804000cd05030200c0804000c941415050905040008d05005414d05040008c04024200908040008d05024200908040008c04005414c05040008541424200908040008c08040008c0804000854144000c441440008c08024200908040000941415140545040000d05021200848040000941421200848040000d05015140545040000541421200848040000c08015140c08040000541415140545040000c08021200848040000150521200848040000908015140908040000150515140545040000908021200848040004850514540515040004d05020600818040004850520600818040004d05014540515040004450520600818040004c08014540c08040004450514540515040004c080206008180400081505206008180400089080145409080400081505145405150400089080206008180400010000206008180400008480054508480400010001054501514400008480206008180 (by decide +kernel)

theorem lower213 : Claim 213 7 :=
  fromSearch 1540 (by decide +kernel) exclude213_0

theorem lower215 : Claim 215 8 :=
  fromLift 8 2 1604 lower213 (by decide +kernel)

theorem lower165 : Claim 165 5 :=
  fromLift 5 4 1797 lower161 (by decide +kernel)

def rule229_0 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower225 none (by decide +kernel)

def rule229_1 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower228 none (by decide +kernel)

def rule229_2 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower197 none (by decide +kernel)

def rule229_3 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower165 none (by decide +kernel)

def cuts229 : Cuts (goalAt 229) := [rule229_0,rule229_1,rule229_2,rule229_3]

def state229_0 : List Sig := roots 229
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_0 : Impossible true (goalAt 229) 6 state229_0.toFinset :=
  node_ok cuts229 [] 0x4000ce06019090e0604000ca42430200c0804000ce06030200c0804000ca42419090a06040008e06009414e06040008c04028200a08040008e06028200a08040008c04009414c06040008642428200a08040008c08040008c0804000864244000c442440008c08028200a08040000a42419180646040000e06021200848040000a42421200848040000e06019180646040000642421200848040000c08019180c08040000642419180646040000c08021200848040000250521200848040000a08019180a08040000250519180646040000a08021200848040004850518580616040004e06020600818040004850520600818040004e06018580616040004450520600818040004c08018580c08040004450518580616040004c08020600818040008250520600818040008a08018580a08040008250518580616040008a080206008180400010000206008180400008480094908480400010001094902524400008480206008180 (by decide +kernel)

theorem lower229 : Claim 229 7 :=
  fromSearch 1541 (by decide +kernel) exclude229_0

theorem lower231 : Claim 231 8 :=
  fromLift 8 2 1621 lower229 (by decide +kernel)

theorem lower119 : Claim 119 8 :=
  fromLift 8 1 1604 lower118 (by decide +kernel)

def cuts101 : Cuts (goalAt 101) := []

def state101_0 : List Sig := roots 101
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude101_0 : Impossible true (goalAt 101) 3 state101_0.toFinset :=
  node_ok cuts101 [] 0x190904505110904424190906460191804105111006460191804460094906160185802524105006160185804160185806460094906160 (by decide +kernel)

theorem lower101 : Claim 101 4 :=
  fromSearch 1541 (by decide +kernel) exclude101_0

def cuts85 : Cuts (goalAt 85) := []

def state85_0 : List Sig := roots 85
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude85_0 : Impossible true (goalAt 85) 3 state85_0.toFinset :=
  node_ok cuts85 [] 0x150504505110504414150505450151404105111005450151404450054505150145401514105005150145404150145405450054505150 (by decide +kernel)

theorem lower85 : Claim 85 4 :=
  fromSearch 1540 (by decide +kernel) exclude85_0

def rule117_0 : {c : Cut // CutGood (goalAt 117) c} :=
  ruleFor 117 lower113 none (by decide +kernel)

def rule117_1 : {c : Cut // CutGood (goalAt 117) c} :=
  ruleFor 117 lower101 none (by decide +kernel)

def rule117_2 : {c : Cut // CutGood (goalAt 117) c} :=
  ruleFor 117 lower85 none (by decide +kernel)

def rule117_3 : {c : Cut // CutGood (goalAt 117) c} :=
  ruleFor 117 lower49 none (by decide +kernel)

def cuts117 : Cuts (goalAt 117) := [rule117_0,rule117_1,rule117_2,rule117_3]

def state117_0 : List Sig := [0xfafafafafafafafa0000000000000000fafafafafafafafa,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_0 : Impossible true (goalAt 117) 4 state117_0.toFinset :=
  node_ok cuts117 [] 0x1c14070601c18011050545070500949070500949070600545070601858054501918064601514064601c18054501918044241c14064241c14034241c18034241c1802524104142524184910003 (by decide +kernel)

def state117_1 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_1 : Impossible true (goalAt 117) 5 state117_1.toFinset :=
  node_ok cuts117 [⟨state117_0,exclude117_0⟩] 0x64240d05064241505070501c14064241c14070501505034140c14054140d09034241909070601c18054141c18070601909034240c18070500441470500841470601c18070501c18070600841411050441441050949025241909100031849041054000c41051909025240949021050545015141c14025241c14021050949025241c14015141c14011050949025241c18015141c18011050545015141c18025241c18100004000061601909100031909200001918064601909064601918100034000d00030d05054501514070501918064600d05064601918070501514054500d09064601918070601514070600d0905450151407060191806460 (by decide +kernel)

def state117_2 : List Sig := [0xffffaaaa00000000ffffaaaa00000000ffffaaaa00000000ffffaaaa,input 0,input 4,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_2 : Impossible true (goalAt 117) 4 state117_2.toFinset :=
  node_ok cuts117 [] 0x1109064601918041051918070601514064600d09070601c18030400949061601858025241858064600949061601858070601454061600c14070501c14044241514064601514064600541470601c1407060145406160145406160 (by decide +kernel)

def state117_3 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 0,input 4,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_3 : Impossible true (goalAt 117) 5 state117_3.toFinset :=
  node_ok cuts117 [⟨state117_2,exclude117_2⟩] 0x64241c14070500c14064241918064601041454501918064601514064601514054501918064601514054501918054141909054141909070500941470500541470600545051501454064241454070500941451501454064600545064600541451501054061601505064241505064241c14200001c1410002 (by decide +kernel)

def state117_4 : List Sig := [0xf0f0fafaf0f0fafaf0f0fafaf0f0fafaf0f0fafaf0f0fafaf0f0fafaf0f0fafa,input 0,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_4 : Impossible true (goalAt 117) 4 state117_4.toFinset :=
  node_ok cuts117 [] 0x1909070501c14030500d09070601c18030601c14070601c18015050949051501454025241454070500949051501c5807060145407060185806160094906460190906460191810003151406460191805450191807060151406460 (by decide +kernel)

def state117_5 : List Sig := [0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,input 0,input 4,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_5 : Impossible true (goalAt 117) 5 state117_5.toFinset :=
  node_ok cuts117 [⟨state117_4,exclude117_4⟩] 0x64241c14070500c14064241918064601041454501918064601514064601c18054501918034241c18070600c18070501c18070600941415141454051501909051501c1402505145405150191801514191807160145407060114146424114146424094147050094147050400006460800006460054146160 (by decide +kernel)

def state117_6 : List Sig := [0xffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa,input 0,input 5,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_6 : Impossible true (goalAt 117) 4 state117_6.toFinset :=
  node_ok cuts117 [] 0x1909064601918041051514064601918054501909070501c14030400949061601858025241858064600949061601454061601858051500c18070601c18034241918054501918070600541470601c1807050185805150185807060 (by decide +kernel)

def state117_7 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 5,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_7 : Impossible true (goalAt 117) 5 state117_7.toFinset :=
  node_ok cuts117 [⟨state117_6,exclude117_6⟩] 0x34241c18070600c18015051c18070600541600001c18070604000464241918064601041464601c1805450191805450191806460151405450191806460151406424150506424150507050094906160185802524185807060054146160185806460094906160094146160105805150190905414190905414 (by decide +kernel)

def state117_8 : List Sig := [0xf0f0f0f0fafafafaf0f0f0f0fafafafaf0f0f0f0fafafafaf0f0f0f0fafafafa,input 0,input 5,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_8 : Impossible true (goalAt 117) 4 state117_8.toFinset :=
  node_ok cuts117 [] 0xd09070601c18030601c14070601c18011051909070501c14030500949061601858025241858070600545061601c5406160185807050185806460094906160190906460191810003191807060151406460151406460191805450 (by decide +kernel)

def state117_9 : List Sig := [0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,input 0,input 5,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_9 : Impossible true (goalAt 117) 5 state117_9.toFinset :=
  node_ok cuts117 [⟨state117_8,exclude117_8⟩] 0x34241c18070600c18070501c18070600541464241918064601041464601c18054501918054501918064601514064241c14070500c14025241858061600949061601c1801505185806160191802524185807150185807050114146424114146424054147060054147060400006460800006460094145150 (by decide +kernel)

def state117_10 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_10 : Impossible true (goalAt 117) 5 state117_10.toFinset :=
  node_ok cuts117 [] 0x64241918064601041454501918064601514064601c18054501918044401918064601110025241858061600949061601918025241858051501858061601454061601c18051501858041401858061601050064241c14070500c14025050d09070601c18030601c1407060400041505190904505190904505 (by decide +kernel)

def state117_11 : List Sig := roots 117
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_11 : Impossible true (goalAt 117) 6 state117_11.toFinset :=
  node_ok cuts117 [⟨state117_1,exclude117_1⟩,⟨state117_3,exclude117_3⟩,⟨state117_5,exclude117_5⟩,⟨state117_7,exclude117_7⟩,⟨state117_9,exclude117_9⟩,⟨state117_10,exclude117_10⟩] 0x4000c64240d05064244000854141c14070504000c64241c14070504000854140d05030504000c54140d09034244000464241c18070604000c54141c18070604000464240d09030604000870500541470504000425051c18070608001470501c18070604000425050541415054000064244000c64244000041011918064604000064241918064604000041014000041054000034141514054504000070501918064604000034141918064604000070501514054504000034241918064604000070601514070604000034241514054504000070601918064604000c45050949025244000c64241858061604000c45051858061604000c64240949025244000825051454051508001070501858061608000c2505185806160400087050145405150400041505185806160800087060145407060800041505145405150400047060185806160400010000185806160400006460094906460400020000094902524400006460185806160 (by decide +kernel)

theorem lower117 : Claim 117 7 :=
  fromSearch 1540 (by decide +kernel) exclude117_11

theorem lower181 : Claim 181 7 :=
  fromLift 7 4 1796 lower177 (by decide +kernel)

theorem lower115 : Claim 115 6 :=
  fromLift 6 1 68 lower114 (by decide +kernel)

theorem lower103 : Claim 103 5 :=
  fromLift 5 1 1621 lower102 (by decide +kernel)

theorem lower87 : Claim 87 5 :=
  fromLift 5 1 1604 lower86 (by decide +kernel)

theorem lower151 : Claim 151 6 :=
  fromLift 6 2 1860 lower149 (by decide +kernel)

theorem lower199 : Claim 199 6 :=
  fromLift 6 1 1638 lower198 (by decide +kernel)

theorem lower195 : Claim 195 5 :=
  fromLift 5 2 102 lower193 (by decide +kernel)

theorem lower227 : Claim 227 6 :=
  fromLift 6 2 85 lower225 (by decide +kernel)

theorem lower167 : Claim 167 6 :=
  fromLift 6 2 1877 lower165 (by decide +kernel)

def rule247_0 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower245 none (by decide +kernel)

def rule247_1 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower246 none (by decide +kernel)

def rule247_2 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower243 none (by decide +kernel)

def rule247_3 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower183 none (by decide +kernel)

def rule247_4 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower215 none (by decide +kernel)

def rule247_5 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower231 none (by decide +kernel)

def rule247_6 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower119 none (by decide +kernel)

def rule247_7 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower118 none (by decide +kernel)

def rule247_8 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower241 none (by decide +kernel)

def rule247_9 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower229 none (by decide +kernel)

def rule247_10 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower117 none (by decide +kernel)

def rule247_11 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower213 none (by decide +kernel)

def rule247_12 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower183 (some (1,input 1,input 7)) (by decide +kernel)

def rule247_13 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower181 none (by decide +kernel)

def rule247_14 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower115 none (by decide +kernel)

def rule247_15 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower241 (some (1,input 4,input 7)) (by decide +kernel)

def rule247_16 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower103 none (by decide +kernel)

def rule247_17 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower193 none (by decide +kernel)

def rule247_18 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower197 none (by decide +kernel)

def rule247_19 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower51 none (by decide +kernel)

def rule247_20 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower165 none (by decide +kernel)

def rule247_21 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower117 (some (1,input 4,input 5)) (by decide +kernel)

def rule247_22 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower196 none (by decide +kernel)

def rule247_23 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower49 none (by decide +kernel)

def rule247_24 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower50 none (by decide +kernel)

def rule247_25 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower225 none (by decide +kernel)

def rule247_26 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower87 none (by decide +kernel)

def rule247_27 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower102 none (by decide +kernel)

def rule247_28 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower101 none (by decide +kernel)

def rule247_29 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower241 (some (1,input 5,input 7)) (by decide +kernel)

def rule247_30 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower149 none (by decide +kernel)

def rule247_31 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower209 none (by decide +kernel)

def rule247_32 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower86 none (by decide +kernel)

def rule247_33 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower119 (some (1,input 4,input 5)) (by decide +kernel)

def rule247_34 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower151 none (by decide +kernel)

def rule247_35 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower183 (some (1,input 4,input 5)) (by decide +kernel)

def rule247_36 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower199 none (by decide +kernel)

def rule247_37 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower198 none (by decide +kernel)

def rule247_38 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower230 none (by decide +kernel)

def rule247_39 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower195 none (by decide +kernel)

def rule247_40 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower227 none (by decide +kernel)

def rule247_41 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower147 none (by decide +kernel)

def rule247_42 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower167 none (by decide +kernel)

def rule247_43 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower183 (some (1,input 4,input 7)) (by decide +kernel)

def rule247_44 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower243 (some (1,input 4,input 7)) (by decide +kernel)

def rule247_45 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower163 none (by decide +kernel)

def rule247_46 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower183 (some (1,input 5,input 7)) (by decide +kernel)

def rule247_47 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower243 (some (1,input 5,input 7)) (by decide +kernel)

def cuts247 : Cuts (goalAt 247) := [rule247_0,rule247_1,rule247_2,rule247_3,rule247_4,rule247_5,rule247_6,rule247_7,rule247_8,rule247_9,rule247_10,rule247_11,rule247_12,rule247_13,rule247_14,rule247_15,rule247_16,rule247_17,rule247_18,rule247_19,rule247_20,rule247_21,rule247_22,rule247_23,rule247_24,rule247_25,rule247_26,rule247_27,rule247_28,rule247_29,rule247_30,rule247_31,rule247_32,rule247_33,rule247_34,rule247_35,rule247_36,rule247_37,rule247_38,rule247_39,rule247_40,rule247_41,rule247_42,rule247_43,rule247_44,rule247_45,rule247_46,rule247_47]

def state247_0 : List Sig := [0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000,input 6,input 5,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_0 : Impossible true (goalAt 247) 6 state247_0.toFinset :=
  node_ok cuts247 [] 0x19180848221208626019180848221208646021208646019180848221208646019180848221208908219180848220e08848209490838218580838220e08616018580838220e08616020e08616018580838220e08616018580838220e0890821858083821898070601494062601898052501898052501c18070501c18085071909070501c14030502820862600989062602414070600d09070600c180c0821898090822420884141c1809082242088507 (by decide +kernel)

def state247_1 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_1 : Impossible true (goalAt 247) 7 state247_1.toFinset :=
  node_ok cuts247 [⟨state247_0,exclude247_0⟩] 0x626019090626009890c08230208626030208c0820989064242414070601909070600d090c08230208706030208c0820d090642410a0064242120884823020864603020864241918064603020884822120826241918064601898084822120826242120884821898064601898034241918064601c18084822120834242120884821c18064601918034142120884821c14064601918034141918064601c140848221209001221208848224208646024209001119180646024208848221208470720e08838230208616030208470718580616030208838220e09001120e08838221208252421209001609490252421208838220e09001618580616018980838220e09001620e0883821898061601858085071858061601c180838220e08850720e0883821c180616018581001220e0883821c14061601858100161858061601c140838220e09001220e08838224208616024209001618580616024208838220e0885071898062601c18052501c18085071494052501c18062601898064240d05064243020870503020864241c14070503020834143020862601c14062601494100121494062604005462601494070501494070604004070602141c70501c14070601c14070602141d00102141d000940024a08219090908224208c08240048c08219092000019090c08224208908218981000a18980424024208908218980908224208424040028c0501c18100061c18085072420890821c1809082242088507400188507 (by decide +kernel)

def state247_2 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_2 : Impossible true (goalAt 247) 6 state247_2.toFinset :=
  node_ok cuts247 [] 0x646021208848218980646021208848219180848224208646021208848219180646021208848219180646021208838221208252420e08616020e08838218580616020e08838218580838224208616020e08838218580616020e08838218580616020e0862601c18052501898062602420890820989070602420890821909090823020864242420862601494062601494070601c14070602141c642424208705024208a0821898016141898090501c18054141c1804414 (by decide +kernel)

def state247_3 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_3 : Impossible true (goalAt 247) 7 state247_3.toFinset :=
  node_ok cuts247 [⟨state247_0,exclude247_0⟩,⟨state247_2,exclude247_2⟩] 0x62601c140626014940a08228208626028208a08214940705014940706009c1c70602141ca08228208706028208a0822141c270708a01001428208a0821505070501c14200011c140705015050a08228209001428208a0822420870502420a00001c140705024208a0822420834142120884822820864602820834141918064602820884822120826241918064601898084822120826242120884821898064601898085071918064601c18084822120885072120884821c180646019180541421208848240064646019180541419180646040050848221209001421208848224208646024209001319180646024208848221208270720e08838228208616028208270718580616028208838220e09001320e08838221208252421209001809490252421208838220e09001718580616018980838220e09001820e0883821898061601858085071858061601c180838220e08850720e0883821c180616018581001420e08838215050616018581001818580616015050838220e09001420e08838224208616024209001818580616024208838220e0885071898062601c18052501c18085071494052501c18062601898062601505062600989100140989062604005c62600989054142414070604004070602141c54141505070601505070602141d00140c181000940024c08218981000a1898026242420890821898090822420826244002826241c18100061c18085072420890821c1809082242088507400188507 (by decide +kernel)

def state247_4 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000,input 6,input 5,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_4 : Impossible true (goalAt 247) 6 state247_4.toFinset :=
  node_ok cuts247 [] 0x64602120884821898084822420854502120884822820864602120884823020864602120885072120884822041c838221208252420e08616020e08838218580838224208515020e08838228208616020e08838230208616020e08850720e0883822101c850718980626040000706024208908218980908228208706024208908230208706024208170718980a08228208c06028208c0821c140a08209c1c626030208c082281804707 (by decide +kernel)

def state247_5 : List Sig := [0xffffffffffffffff0000000000000000ffffffffffff0000,input 6,input 5,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_5 : Impossible true (goalAt 247) 6 state247_5.toFinset :=
  node_ok cuts247 [] 0x646021208848218980848224208545021208848228208646021208848219180646021208838221208252420e08616020e08838218580838224208515020e08838228208616020e08838218580616020e0870602420890821898090822820870602420890821c180706024208626028208a08230180a0821c14070502820862600989062600989084821918084821918083821858083821858026241898026241898090821c18090821c180a0821c140a0821c140c082 (by decide +kernel)

def state247_6 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 5,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_6 : Impossible true (goalAt 247) 7 state247_6.toFinset :=
  node_ok cuts247 [⟨state247_4,exclude247_4⟩,⟨state247_5,exclude247_5⟩] 0x18980642418980262430208c08218980c08230208262419090a06080004470711c1c850730208c08280000c08230208850711c1c428019090848221208c08219180c08219090646019180c0822120884820989064601918062602120884820989084822120862601918062600d09084822120890821514090820d09054501514090822120884820d050848221208a08219180a0820d050646019180a0822120884822141c44401110081032120884822141c848221208810311100444011c1c838220e08c08218580c08211c1c616018580c08220e08838240044838220e08848209490848240058252409490848220e08838240058616018580626020e08838240058838220e08626018580616040048838220e08908214540908240058515014540908220e08838240048838220e08a08218580a08240058616018580a08220e0883822141c414010500840620e0883822141c838220e0884061050041402141c42401090100001898062602141c626018981000010900424015050908224208c0821c180c0821505070601c180c0822420890821494070601c18062602420890821494090822420862601c18062601c140908224208a0821c180a0821c14070601c180a08224208908240069001a05c1c642428208a0823020870503020864241c140705030208a0822820862601c140626014940a08228208626028208a082149407050301810010400402707 (by decide +kernel)

def state247_7 : List Sig := [0xffffffffffffffff00000000ffffffffffffffffffffffff00000000ffff0000,input 6,input 5,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_7 : Impossible true (goalAt 247) 6 state247_7.toFinset :=
  node_ok cuts247 [] 0x64602120884821898084822420854502120884821918064602120884823020864602120885072120884822041c838221208252420e08616020e08838218580838224208515020e08838218580616020e08838230208616020e08252420e0883820949070602420890821898090821c18070602420890823020870602420834242420890820d090626014940626030180e0823020870503020827071c140a08228208626030208c082241406424189802624189802624 (by decide +kernel)

def state247_8 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_8 : Impossible true (goalAt 247) 6 state247_8.toFinset :=
  node_ok cuts247 [] 0x646021208848218980848224208545021208848219180646021208848219180646021208838221208252420e08616020e08838218580838224208515020e08838218580616020e08838218580616020e0870602420890821898090821c18070602420890821c180706024208848219180848219180838218580838218580c0601898052501898090821c18090821c18030501c14070501109085071c140a08228208626009890626028180c082189801614189801614 (by decide +kernel)

def state247_9 : List Sig := [0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,input 5,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_9 : Impossible true (goalAt 247) 7 state247_9.toFinset :=
  node_ok cuts247 [⟨state247_7,exclude247_7⟩,⟨state247_8,exclude247_8⟩] 0x626019090626009890c08230208626030208c08209890642428180642421208848230208646030208642419180646030208848221208262419180646018980848221208262421208848218980646018980342421208848224208545024208342415140545024208848221208270721208848208c0c646019180270719180646008c0c848221208470720e08838230208616030208470718580616030208838220e09001b20e08838221208252421209001b09490252421208838220e09001c18580616018980838220e09001b20e08838218980616018581001020e08838224208515024209001b14540515024208838220e08270720e08838209818616018580270718580616009818838220e0854142420890823020870603020854141c18070603020890822420852501c180706018980908224208525024208908218980706018981001024208908209c1c70601c18100101c180706009c1c908224208642409c1c642430209001230208642480004442430208270730208626009414626014940270714940626009c1c626014940250514940c0822141cc08219091001019090c08280000c08219090850710a0084822040c84821918085071918084822141c84821918081031918083822101883821858085071858083822141c83821858084061858052504002852501898085071898052502141c525018981000a1898090822141c90821c18100061c18090824001890821c18085071c181001040048a082 (by decide +kernel)

def state247_10 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,input 6,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_10 : Impossible true (goalAt 247) 6 state247_10.toFinset :=
  node_ok cuts247 [] 0x626028208a08230180a08230208705028208230728208a08208c1c838228208616020e08616020e08838218580838224208515020e08838230208616020e08252420e08838209490262418980626009890908228208706024208706024208908218980908230208706024208342418980c08230208a06019090848219180a08221208838209490838221208626021208848219180848215140908221208848219180c082212088107 (by decide +kernel)

def state247_11 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff00000000ffff0000,input 5,input 6,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_11 : Impossible true (goalAt 247) 6 state247_11.toFinset :=
  node_ok cuts247 [] 0x646021208848218980848224208545021208848230208646021208848219180646021208838221208252420e08616020e08838218580838224208515020e08838230208616020e08838218580616020e0870602420890821898090823020870602420890821c180706024208626030208c0822818062601494062601494064243020864243020884821918084821918083821858083821858052501898052501898090821c18090821c180c08219090c08219090a082 (by decide +kernel)

def state247_12 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_12 : Impossible true (goalAt 247) 6 state247_12.toFinset :=
  node_ok cuts247 [] 0x19180848221208626021208908215140848219090848221208810721208646019180848221208c08219180848220e08848209490838218580838220e08616020e08908214540838209490838220e08252420e08616018580838220e08c0821858083820989062601898026241c18090822420862600d09090821c18070602420890823020870602420862601494062603018064241c140705011090a08218980c08230208905019090c082302088507 (by decide +kernel)

def state247_13 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,input 6,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_13 : Impossible true (goalAt 247) 7 state247_13.toFinset :=
  node_ok cuts247 [⟨state247_4,exclude247_4⟩,⟨state247_10,exclude247_10⟩,⟨state247_11,exclude247_11⟩,⟨state247_12,exclude247_12⟩] 0x18980705018980525028208a08218980a0822820852501c140c06040050a08228208c0821c140c0828000c70501c140c08228208a08280008270709c1c850728208a08280000a08228208850709c1c22800d050848221208a08219180a0820d050646019180a0822120884820989064601918062602120884820989084822120862601918062604005084822120890821514090824004c545015140908221208848215050848221208c08219180c08215050646019180c0822120884822141e00012141c81032120884822141c84822120881034004c810709c1c838220e08a08218580a08209c1c616018580a08220e0883824004c838220e08848209490848240060252409490848220e0883824005c616018580626020e08838240060838220e08626018580616040050838220e08908214540908240060515014540908220e08838240050838220e08c08218580c08240060616018580c08220e0883822141c252409490840620e0883822141c838220e0884060949025242141c26240989100001898062602141c62601898100000989026241c140908224208a0821c180a0821c14070601c180a0822420890821494070601c18062602420890821494090822420862601c180626015050908224208c0821c180c0821505070601c180c0822420890824005100130d090626015050626009890c08230208626030208c082098905414281810014400406424 (by decide +kernel)

def state247_14 : List Sig := [0xffffffff00000000ffffffffffffffffffffffff00000000ffffffffffff0000,input 5,input 6,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_14 : Impossible true (goalAt 247) 6 state247_14.toFinset :=
  node_ok cuts247 [] 0x646021208848218980848224208545021208848219180646021208848228208646021208545021208848215140838221208252420e08616020e08838218580838224208515020e08838218580616020e08838228208616020e08515020e0883821454070602420890821898090821c18070602420890822820870602420817072420890822141c626009890626028180626028208a08214940a08238208642428208705018980525018980525019090470730208c082 (by decide +kernel)

def state247_15 : List Sig := [0xffffffffffffffff0000000000000000ffff0000ffff0000,input 6,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_15 : Impossible true (goalAt 247) 7 state247_15.toFinset :=
  node_ok cuts247 [⟨state247_14,exclude247_14⟩] 0x62601c140626014940a08228208626028208a08214940705030180642428208a08211c1c70501c14064241c140705011c1ca08228208341421208848228208646028208341419180646028208848221208262419180646018980848221208262421208848218980646018981001421208848224208545024209001315140545024208848221208642421208848210c0c646019180642419180646010c0c848221208270720e08838228208616028208270718580616028208838220e09001320e08838221208252421209001b09490252421208838220e09001c18580616018980838220e09001b20e08838218980616018581001420e08838224208515024209001b14540515024208838220e08470720e08838219090616018580470718580616019090838220e0870502420890822820870602820870501c18070602820890822420852501c18070601898090822420852502420890821898070601898100142420890821909070601c18100141c180706019090908224208626019090626009890470709890626011c1c626009890642409890a0822141ca0821c14100101c140a08280000a0821c14085071c14084822040c84821918085071918084822141c84821918081031918083822101883821858085071858083822141c838218580840618580161440028a4241898085071898016142141c161418981000a1898090822141c90821c18100061c18090824001890821c18085071c181001040050c082 (by decide +kernel)

def state247_16 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 5,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_16 : Impossible true (goalAt 247) 7 state247_16.toFinset :=
  node_ok cuts247 [] 0x626030208c08224140642430208c08219090470730208c08211c1c848230208646021208646021208848218980848224208545021208646021208848219180848228208646021208444021208848211100838230208616020e08838221208252420e08616020e08838218580838224208515020e08616020e08838218580838228208616020e08414020e08838210500626038180525018980424018980626010900908230208541424208525024208908218980706024208a0821c140908240068850728208c0821c140a08218980a08228208525040040a08208a002707 (by decide +kernel)

def state247_17 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_17 : Impossible true (goalAt 247) 7 state247_17.toFinset :=
  node_ok cuts247 [⟨state247_4,exclude247_4⟩,⟨state247_8,exclude247_8⟩,⟨state247_12,exclude247_12⟩,⟨state247_0,exclude247_0⟩,⟨state247_2,exclude247_2⟩] 0x19180848221208626021208908215140848219180848221208646021208646019180848221208646019180848221208646019180848220e08848209490838218580838220e08616020e08908214540838218580838220e08616020e08616018580838220e08616018580838220e08616018580838218980e0601494062601494090822420862601c18090821909200042420890824005070502420890824002600032420862600989062600989064242141e000219090c0821898052501898052508000470501c14085071909070500c140a082189801614189801614400408507800008507 (by decide +kernel)

def state247_18 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000,input 6,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_18 : Impossible true (goalAt 247) 6 state247_18.toFinset :=
  node_ok cuts247 [] 0x626028208a08214940230728208a08208c1ca08230208705028208838228208616020e08616020e08838218580838224208515020e08616020e08838218580838230208616020e08626038180525018980908228208705024208525024208908218980706024208c08215050908218980c08230208905019090c08230208428021208646028208848220e08252420e088482189808482212086460212085450242088482191808482212086460212086460302088482 (by decide +kernel)

def state247_19 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,input 6,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_19 : Impossible true (goalAt 247) 7 state247_19.toFinset :=
  node_ok cuts247 [⟨state247_18,exclude247_18⟩] 0x626028208a08214940270728208a08209c1ca08230208705028208270728208a08209c1c84822820864602120864602120884821898084822420854502120864602120884821918084823020864602120a000021208848240038838228208616020e08838221208252420e08616020e08838218580838224208515020e08616020e08838218580838230208616020e08252420e08838209490626038180525018980262418980626009890908228208705024208525024208908218980706024208c0821505090824004c850718980c08230208905040040c08210a006424 (by decide +kernel)

def state247_20 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_20 : Impossible true (goalAt 247) 8 state247_20.toFinset :=
  node_ok cuts247 [⟨state247_1,exclude247_1⟩,⟨state247_3,exclude247_3⟩,⟨state247_6,exclude247_6⟩,⟨state247_9,exclude247_9⟩,⟨state247_13,exclude247_13⟩,⟨state247_15,exclude247_15⟩,⟨state247_16,exclude247_16⟩,⟨state247_17,exclude247_17⟩,⟨state247_19,exclude247_19⟩] 0x40028626019090626040028262430208c08240028626030208c08240028262419090905040042000519090642440050850730208c08280022000430208c08240050850719090428040050642428208a08240048c0821c140c0828001c64241c140705040050c08228208a0824002862601c140626040028525028208a08240028626028208a0824002852501c140525040042000309c1c270740048850728208a0828001a000228208a08240040850709c1c228040050642421208848240038c08219180c0824004c642419180646040038c08221208848240048341421208848240038a08219180a08240044341419180646040038a08221208848240028262419180646040028626021208848240028262421208848240028626019180626040025000921208848240024908215140908240025000f1514054504002490822120884824004085071918064604003881032120884824003c85072120884824003881031918064604001c470720e0883824001cc08218580c0824001c47071858061604001cc08220e0883824001c270720e0883824001ca08218580a0824001c27071858061604001ca08220e0883824001d000720e0883824001c84820949084824001d00070949025244001c848220e0883824001d00071858061604001c626020e0883824001d000720e0883824001c62601858061604001d000720e0883824001c90821454090824001d00071454051504001c908220e0883824001c85071858061604001c840620e0883824001c850720e0883824001c840618580616040024850718980626040025000014940e06040024850714940525040025000018980626040024541424208908240024c08240024c08240024541480004541440024c08224208908240024705024208908240024a08240024a08240024705080000705040024a082242089082400245250400285250400246260242089082400245250242089082400246260400246260400190006400187060 (by decide +kernel)

def state247_21 : List Sig := [0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000,input 4,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_21 : Impossible true (goalAt 247) 6 state247_21.toFinset :=
  node_ok cuts247 [] 0x19180848221208626015140848221208545021208646019180848221208706015140848221208a08219180848220e08848209490838218580838220e08616014540838220e08515020e08616018580838220e08706014540838220e08a08218580838214940626018980525018980262418980a0601c14064241c14030503020870601898052501898070501c18070602141c34241c18070600c180908218980a0822820884241c140a082282088507 (by decide +kernel)

def state247_22 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_22 : Impossible true (goalAt 247) 6 state247_22.toFinset :=
  node_ok cuts247 [] 0x64602120884821898054502120884821514084822820864602120884821c180545021208848219180646021208838221208252420e08616020e08838218580515020e08838214540838228208616020e0883821c180515020e08838218580616020e08525018980626014940626028208a08221090705028208a0821505070601898052501898070501c18070602141c541428208706028208908218980262418980a0601c14064241c140442430208a08219090a082 (by decide +kernel)

def state247_23 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_23 : Impossible true (goalAt 247) 7 state247_23.toFinset :=
  node_ok cuts247 [⟨state247_21,exclude247_21⟩,⟨state247_22,exclude247_22⟩] 0x52501c180706018980908224208525024208908218980706018980705005c1c70502141c90822420870502420890822141c170704a01001e2420890821909070601c18200011c180706019090908224209001e2420890822820870602820a00001c18070602820890822420834242120884822420854502420834241514054502420884822120826241918064601898084822120826242120884821898064601898085071514054501c14084822120885072120884821c14054501514064242120884824007c646019180642419180646040078848221209001e21208848228208646028209001319180646028208848221208170720e08838224208515024208170714540515024208838220e09001320e08838221208252421209001809490252421208838220e09001718580616018980838220e09001820e0883821898061601858085071454051501c140838220e08850720e0883821c140515014541001e20e08838219090616018581001818580616019090838220e09001e20e08838228208616028209001818580616028208838220e0885071494052501c14062601898085071898062601c140525014940626019090626009891001e0989062604005c62600989064242818070504006870502141c64241909070501909070502141d001e0c141000b4002cc08218981000a18980161428208a08218980a0822820816144002884241c14100061c140850728208a0821c140a082282088507400188507 (by decide +kernel)

def state247_24 : List Sig := [0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff00000000,input 6,input 4,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_24 : Impossible true (goalAt 247) 6 state247_24.toFinset :=
  node_ok cuts247 [] 0x64602120884821898084822820864602120884821c18054502120884823020864602120885072120884822041c838221208252420e08616020e08838218580838228208616020e0883821c180515020e08838230208616020e08151420e08838205450626028208a08230180a08230208705028208341428208a0820d050706018980525018980705028208706028208d0823020870603020817071c180908224208626030208c082281805414189801614189801614 (by decide +kernel)

def state247_25 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_25 : Impossible true (goalAt 247) 6 state247_25.toFinset :=
  node_ok cuts247 [] 0x646021208848218980848228208646021208848219180646021208848219180646021208838221208252420e08616020e08838218580838228208616020e08838218580616020e08838218580616020e08626028208a08230180a0821c140705028208a0821c14070502820884821514084821c18083821454083821c18062601494062601c180a0821c180a0821c14030601c18070601105085071c180908224208626009890626024140c082189802624189802624 (by decide +kernel)

def state247_26 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000,input 4,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_26 : Impossible true (goalAt 247) 7 state247_26.toFinset :=
  node_ok cuts247 [⟨state247_24,exclude247_24⟩,⟨state247_25,exclude247_25⟩] 0x626019090626009890c08230208626030208c08209890642428180642421208848230208646030208642419180646030208848221208262419180646018980848221208262421208848218980646018980341421208848228208646028208341419180646028208848221208170721208848204c0c545015140170715140545004c0c848221208470720e08838230208616030208470718580616030208838220e09002020e08838221208252421209002009490252421208838220e09002018580616018980838220e09002020e08838218980616018581001a20e08838228208616028209002018580616028208838220e08170720e08838205818515014540170714540515005818838220e08642428208a0823020870503020864241c140705030208a0822820862601c140626014940a08228208626028208a08214940705030180541405c1c541430209001230208541480004441430208170730208525005414525018980170718980525005c1c525018980150518980705005c1c705028209001a28208705040068705028208170728208c0822141cc08215051001a15050c08280000c08215050850710a0084822040c84821514085071514084822141c84821514081031514083822101883821454085071454083822141c83821454084061454062604002462601494085071494062602141c626014941000914940a0822141ca0821c14100061c140a08240018a0821c14085071c141001a400489082 (by decide +kernel)

def state247_27 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_27 : Impossible true (goalAt 247) 7 state247_27.toFinset :=
  node_ok cuts247 [⟨state247_21,exclude247_21⟩] 0x626019090626009890c08230208626030208c0820989064242818070501505070500d050c08230208705030208c0820d050541410a0064242120884823020864603020864241918064603020884822120826241918064601898084822120826242120884821898064601898034141514054501c14084822120834142120884821c14054501514034242120884821c18054501c18034241514054501c180848221209001221208848228208646028209001119180646028208848221208470720e08838230208616030208470718580616030208838220e09001120e08838221208252421209001609490252421208838220e09001618580616018980838220e09001620e0883821898061601858085071454051501c140838220e08850720e0883821c140515014541001220e0883821c18051501c18100161454051501c180838220e09001220e08838228208616028209001618580616028208838220e0885071494052501c14062601898085071898062601c14052501494054140d09034243020870603020854141c18070603020834243020852501c18070601898100121898052504005452501898070601898070504006870502141c70601c18070501c18070602141d001a2141d000b4002c908219090a08228208c08240048c08219092000019090c08228208a08218981000a18980424028208a08218980a08228208424040028c0601c14100061c140850728208a0821c140a082282088507400188507 (by decide +kernel)

def state247_28 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 6,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_28 : Impossible true (goalAt 247) 6 state247_28.toFinset :=
  node_ok cuts247 [] 0x706024208908218980908228208706024208908230208706024208130724208908204c1c838224208515020e08616020e08838218580838228208616020e08838230208616020e08151420e08838205450161418980626005850626028208a08230180a08230208705028208341418980c08230208a06015050848215140908221208838209490838221208626021208848219180848219180a08221208848219180c082212088107 (by decide +kernel)

def state247_29 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000,input 4,input 6,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_29 : Impossible true (goalAt 247) 6 state247_29.toFinset :=
  node_ok cuts247 [] 0x646021208848218980848228208646021208848230208646021208848215140545021208838221208252420e08616020e08838218580838228208616020e08838230208616020e08838214540515020e08626028208a08230180a08230208705028208626030208c08228180525018980525018980705028208705028208541430208541430208848215140848215140838214540838214540626014940626014940a0821c140a0821c140c08215050c082150509082 (by decide +kernel)

def state247_30 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_30 : Impossible true (goalAt 247) 6 state247_30.toFinset :=
  node_ok cuts247 [] 0x19180848221208626021208a08219180848215050848221208810721208706015140848221208c08219180848220e08848209490838218580838220e08616020e08a08218580838205450838220e08151420e08706014540838220e08c08218580838205850626018980161418980a08228208c0600d050a0823020870502820870601898052501898070502820870602820854141c180706011050908218980c08230208a06015050c082302088507 (by decide +kernel)

def state247_31 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 6,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_31 : Impossible true (goalAt 247) 7 state247_31.toFinset :=
  node_ok cuts247 [⟨state247_4,exclude247_4⟩,⟨state247_28,exclude247_28⟩,⟨state247_29,exclude247_29⟩,⟨state247_30,exclude247_30⟩] 0x1494070601c18062602420890821494090822420862601c18062601c140908224208a0821c180a0821c14070601c180a08224208908240078908224208c0821c180c0828000c70601c180c08224208908280008170705c1c850724208908280000908224208850705c1c12800d09084822120890821514090820d090545015140908221208848209890646019180626021208848209890848221208626019180626040078848221208a08219180a0824004c646019180a08221208848219090848221208c08219180c08219090646019180c0822120884822141e00012141c81032120884822141c84822120881034004c810705c1c838220e08908214540908205c1c515014540908220e0883824004c838220e08848209490848240060252409490848220e0883824005c616018580626020e08838240060838220e08626018580616040078838220e08a08218580a08240060616018580a08220e08838240078838220e08c08218580c08240060616018580c08220e0883822141c151405450840620e0883822141c838220e0884060545015142141c16140585100001898062602141c626018981000005850161418980705018980525028208a08218980a0822820852501c140c06019090a08228208c0821c140c0821909070501c140c08228208a0824007900130d050626019090626009890c08230208626030208c08209890642428181001e400685414 (by decide +kernel)

def state247_32 : List Sig := [0xffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffff0000,input 4,input 6,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_32 : Impossible true (goalAt 247) 6 state247_32.toFinset :=
  node_ok cuts247 [] 0x646021208848218980848228208646021208848219180646021208848224208545021208646021208848219180838221208252420e08616020e08838218580838228208616020e08838218580616020e08838224208515020e08616020e08838218580626028208a08230180a0821c140705028208626009890626024140525024208908218980908228208705024208908234208541424208706014940626014940626028208270728208850715050470730208c082 (by decide +kernel)

def state247_33 : List Sig := [0xffffffffffffffff0000000000000000ffffffff00000000,input 6,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_33 : Impossible true (goalAt 247) 7 state247_33.toFinset :=
  node_ok cuts247 [⟨state247_32,exclude247_32⟩] 0x52501c18070601898090822420852502420890821898070601898070502420890822820870602820870501c180706028208908224208541424208908211c1c70601c18054141c180706011c1c908224208342421208848224208545024208342415140545024208848221208262419180646018980848221208262421208848218980646018981001e21208848228208646028209001319180646028208848221208541421208848210c0c646019180541419180646010c0c848221208170720e08838224208515024208170714540515024208838220e09001320e08838221208252421209002009490252421208838220e09002018580616018980838220e09002020e08838218980616018581001e20e08838228208616028209002018580616028208838220e08470720e08838215050616018580470718580616015050838220e0862601c140626014940a08228208626028208a08214940705030181001e28208a0821505070501c141001e1c140705015050a08228208626015050626009890470709890626011c1c62600989054140989090822141c90821c181001a1c18090828000090821c18085071c18084822040c84821918085071918084822141c84821918081031918083822101883821858085071858083822141c83821858084061858026244002826241898085071898026242141c262418981000a18980a0822141ca0821c14100061c140a08240018a0821c14085071c141001a40078c082 (by decide +kernel)

def state247_34 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 4,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_34 : Impossible true (goalAt 247) 7 state247_34.toFinset :=
  node_ok cuts247 [] 0x626030208c08228180541430208c08215050470730208c08211c1c848230208646021208646021208848218980848228208646021208545021208848215140848224208545021208444021208848211100838230208616020e08838221208252420e08616020e08838218580838228208616020e08515020e08838214540838224208515020e08414020e08838210500525018980626014940424018980626010900a08230208642428208626028208a08230180705040040850724208c0821c18090821c180908224208626024208a0821c180908240068908204a001707 (by decide +kernel)

def state247_35 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_35 : Impossible true (goalAt 247) 7 state247_35.toFinset :=
  node_ok cuts247 [⟨state247_4,exclude247_4⟩,⟨state247_25,exclude247_25⟩,⟨state247_30,exclude247_30⟩,⟨state247_21,exclude247_21⟩,⟨state247_22,exclude247_22⟩] 0x19180848221208626021208a08219180848215140848221208545021208646019180848221208706015140848221208646019180848220e08848209490838218580838220e08616020e08a08218580838214540838220e08515020e08616018580838220e08706014540838220e08616018580838214940626018980525018980a08228208c0601c140a08215052000428208a0824002e00032820862600989062600989054142141e000215050c0821c180626014940626040078a0821c180a0828000470601c18085071505070600c1809082189802624189802624400688507800008507 (by decide +kernel)

def state247_36 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_36 : Impossible true (goalAt 247) 6 state247_36.toFinset :=
  node_ok cuts247 [] 0x706024208908218980908228208706024208130724208908204c1c908230208706024208838224208515020e08616020e08838218580838228208616020e08515020e08838214540838230208616020e08525018980626014940626028208a08230180705028208c08219090a08218980c08230208a06015050c08230208428021208545024208848220e08252420e088482189808482212086460212086460282088482151408482212085450212086460302088482 (by decide +kernel)

def state247_37 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_37 : Impossible true (goalAt 247) 7 state247_37.toFinset :=
  node_ok cuts247 [⟨state247_36,exclude247_36⟩] 0x706024208908218980908228208706024208170724208908205c1c908230208706024208170724208908205c1c84822420854502120864602120884821898084822820864602120854502120884821514084823020864602120a000021208848240038838224208515020e08838221208252420e08616020e08838218580838228208616020e08515020e08838214540838230208616020e08151420e08838205450525018980626014940161418980626005850626028208a08230180705028208c08219090a0824004c850718980c08230208a06040068c08210a005414 (by decide +kernel)

def state247_38 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_38 : Impossible true (goalAt 247) 8 state247_38.toFinset :=
  node_ok cuts247 [⟨state247_6,exclude247_6⟩,⟨state247_23,exclude247_23⟩,⟨state247_26,exclude247_26⟩,⟨state247_27,exclude247_27⟩,⟨state247_31,exclude247_31⟩,⟨state247_33,exclude247_33⟩,⟨state247_34,exclude247_34⟩,⟨state247_35,exclude247_35⟩,⟨state247_37,exclude247_37⟩] 0x40028626019090626040028262430208c08240028626030208c08240028262419090a0604006a000515050541440078850730208c08280022000430208c08240078850715050428040078541424208908240048c0821c180c0828001c54141c180706040078c0822420890824002852501c18070604002862602420890824002852502420890824002862601c18062604002d000b2420890824002ca0821c180a0824002e00031c18070604002ca0822420890824006a000205c1c17074004885072420890828001a000024208908240068850705c1c128040078642421208848240038c08219180c0824004c642419180646040038c0822120884824004834242120884824003890821514090824004434241514054504003890822120884824002826241918064604002862602120884824002826242120884824002862601918062604002d000b2120884824002ca08219180a0824002d001d1918064604002ca0822120884824006885071514054504003881032120884824007485072120884824003881031514054504001c470720e0883824001cc08218580c0824001c47071858061604001cc08220e0883824001c170720e0883824001c90821454090824001c17071454051504001c908220e0883824001d000720e0883824001c84820949084824001d00070949025244001c848220e0883824001d00071858061604001c626020e0883824001d000720e0883824001c62601858061604001d000720e0883824001ca08218580a0824001d00071858061604001ca08220e0883824001c85071454051504001c840620e0883824001c850720e0883824001c84061454051504002885071494052504002900001898062604002885071898062604002900001494052504002c642428208a0824002cc0824002cc0824002c64248000464244002cc08228208a08240028626040028626040028525028208a08240028626028208a08240028525040028c060400190006400187050 (by decide +kernel)

def state247_39 : List Sig := [0x33333333333333333333333333330000,input 6,input 4,input 5,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_39 : Impossible true (goalAt 247) 6 state247_39.toFinset :=
  node_ok cuts247 [] 0x646021208848219180848228208646021208848224208545021208848230208646021208838221208252420e08616020e08838218580838228208616020e08838224208515020e08838230208616020e08705028208a0821c140a0823020870502820870602420890821c180908228208706024208908230208706024208642430208c08210a00626021208646021208616020e08616020e08e06014940a08218980a0821898090821c180908209890c08218980c082 (by decide +kernel)

def state247_40 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000,input 4,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_40 : Impossible true (goalAt 247) 6 state247_40.toFinset :=
  node_ok cuts247 [] 0x19180848221208626021208646019180848221208706015140848221208c08219180848219090848221208810720e08848209490838218580838220e08616020e08616018580838220e08706014540838220e08c08218580838209490838220e08252409890626018980262418980525018980c0602820864241c14070500c14070601898052501898070501c18070604007890820d09070601c180306018980c08230209000a19090c082302088507 (by decide +kernel)

def state247_41 : List Sig := [0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000,input 6,input 4,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_41 : Impossible true (goalAt 247) 7 state247_41.toFinset :=
  node_ok cuts247 [⟨state247_4,exclude247_4⟩,⟨state247_0,exclude247_0⟩,⟨state247_21,exclude247_21⟩,⟨state247_39,exclude247_39⟩,⟨state247_40,exclude247_40⟩] 0x19180848221208646019180848221208626021208646019180848221208706015140848221208646019180848221208646019180848220e08848209490838218580838220e08616018580838220e08616020e08616018580838220e08706014540838220e08616018580838220e0861601858083823818070502141e00021c14062601494062601494064241c14070500c140a0821c18085078000470601c18062601494062601c14070601c181001e0d09070601c18030602420864242141e000419090626009890626009890c08240018850780000850718982000318981000a (by decide +kernel)

def state247_42 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_42 : Impossible true (goalAt 247) 7 state247_42.toFinset :=
  node_ok cuts247 [⟨state247_4,exclude247_4⟩,⟨state247_40,exclude247_40⟩] 0x19180848221208626021208646019180848221208706015140848221208646019180848221208c0821918084822141c848221208810720e08848209490838218580838220e08616020e08616018580838220e08706014540838220e08616018580838220e08c08218580838209490838220e0825240989062601898026241898052501898052502820834143020870503020834141c14070500d05070601898052501898070501c181001e2420834243020870603020834241c18070600d090626010900626010901000d3020a00013020900132141e00002141c626030208c082281806424 (by decide +kernel)

def state247_43 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_43 : Impossible true (goalAt 247) 8 state247_43.toFinset :=
  node_ok cuts247 [⟨state247_6,exclude247_6⟩,⟨state247_1,exclude247_1⟩,⟨state247_27,exclude247_27⟩,⟨state247_41,exclude247_41⟩,⟨state247_42,exclude247_42⟩] 0x40084642419090850730208c08280010c08230208850719090428018980642418980262430208c08218980c08230208262419090262419090848221208c08219180c08219090646019180c0822120884822141c64601918081032120884822141c84822120881031918064600989064601918062602120884820989084822120862601918062600d05084822120870501918064600d05064601918070502120884820d09084822120870601514070600d090545015140706021208848240048848221209000819180646040044646019181000821208848211c1c838220e08c08218580c08211c1c616018580c08220e08838240044838220e08848209490848240058252409490848220e0883822141c616018580840620e0883822141c838220e08840618580616040058616018580626020e08838240058838220e0862601858061604002c838220e08705018580616040058616018580705020e08838240024838220e08706014540706040058515014540706020e08838240048838220e09000718580616040058616018581000720e0883824002500093818064240d05064243020870503020864241c140705030208341430209000b1c14070502141d000b2141d000b4008600022141c70501c14062601c140626014941000b14940626040054626014940705014941000940024a0821505034240d090c0821c180c0821505070601c180c0820d090c0824002470601c18085074002485074002500218000485071c18070601494070601c18062604002462601494100151494062601c18062601c141000b1c14100091c18070604002500094002500094002c908219091000d19090c08240048c08219092000319090c08240034c08240049000640018850740048850740049002180000850740018850718981000a189804240400484240189810015189804240400284240 (by decide +kernel)

def state247_44 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 0,input 2,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_44 : Impossible true (goalAt 247) 9 state247_44.toFinset :=
  node_ok cuts247 [⟨state247_20,exclude247_20⟩,⟨state247_38,exclude247_38⟩,⟨state247_43,exclude247_43⟩] 0x40019000619090642440018850730208c08240019000c30208c08240018850719090428040028626019090626040028262430208c08240028626030208c08240028262419090262440034642428208a0824002cc0821c140c0824003064241c140705040034c08228208a0824001900061c140705040018850728208a0824001a000128208a0824001885071c14070504002862601c140626040028525028208a08240028626028208a0824002852501c140525040034541424208908240024c0821c180c0824003054141c180706040024c0822420890824002c705024208908240024a0821c180a0828000870501c180706040024a0822420890824001900061c18070604001885072420890824001a00002420890824001885071c18070604002852501c18070604002462602420890824002852502420890824002462601c180626040020642421208848240020c08219180c08240020642419180646040020c08221208848240020341421208848240020a08219180a08240020341419180646040020a0822120884824002034242120884824002090821514090824002034241514054504002090822120884824001885071918064604001881032120884824001885072120884824001881031918064604002026241918064604002062602120884824002026242120884824002062601918062604001c470720e0883824001cc08218580c0824001c47071858061604001cc08220e0883824001c270720e0883824001ca08218580a0824001c27071858061604001ca08220e0883824001c170720e0883824001c90821454090824001c17071454051504001c908220e08838240021000820e08838240020848209490848240021000709490252440020848220e08838240018850718580616040018840620e08838240018850720e0883824001884061858061604001d00071858061604001c626020e0883824001d000720e0883824001c626018580616040001000040000e060 (by decide +kernel)

def state247_45 : List Sig := [0x5555555555555555555555555555555555555555555555555555555555550000,input 6,input 7,input 4,input 5,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_45 : Impossible true (goalAt 247) 6 state247_45.toFinset :=
  node_ok cuts247 [] 0x21a08a28219180868221a08928215140868219180868221a08646021a08c28219180868221a08848021208848228a08a08028208a08224a08908024208908218980e0602141c626030a08c08030208c08238180a28228a08c06028a08c2821c140a28224a08a2821c18092821c180928224a08706024a08c2821c180928238180c28230a08a06020e08252421a08838220608838220e08818020e08616028a08838220e08515024a08838218580838220e08616020e08616030a088382 (by decide +kernel)

def state247_46 : List Sig := [0x3333333333333333333333333333333333333333333333333333333333330000,input 6,input 7,input 4,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_46 : Impossible true (goalAt 247) 6 state247_46.toFinset :=
  node_ok cuts247 [] 0x21a08a28219180868221a08928215140868219180868221a08646021a08c28219180868220e08868209490838220e08a28218580838220e08928214540838218580838220e08616020e08c28218580838238180a28228a08c06028a08c2821c140a28224a08a2821c18092821c180928224a08706024a08c2821c180928238180c28230a08a06021208848221200868220608838220600838228208a08228200a28224208908224200928218980850738180626030208c08230200c282 (by decide +kernel)

def state247_47 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000,input 6,input 7,input 4,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_47 : Impossible true (goalAt 247) 6 state247_47.toFinset :=
  node_ok cuts247 [] 0x28a08a08028208a08224a08908024208908218980e0602141c626030a08c08030208c08220600838220e08818220e08a28218580838220e08928214540838218580838220e08616020e08c28218580838238180a28228a08c06028a08c2821c140a28224a08a2821c18092821c180928224a08706024a08c2821c180928238180c28230a08a06021208848221a08848020e08252420e08868221a08646028a08868221a08545024a08868219180868221a08646021a08646030a088682 (by decide +kernel)

def state247_48 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000,input 6,input 7,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_48 : Impossible true (goalAt 247) 7 state247_48.toFinset :=
  node_ok cuts247 [⟨state247_4,exclude247_4⟩,⟨state247_45,exclude247_45⟩,⟨state247_46,exclude247_46⟩,⟨state247_47,exclude247_47⟩] 0x21a08a28219180868221a08928215140868219180868221a08646021a08c2821918086828000c868221a09000221a08848021208848228a08a08028208a08224a08908024208908218980e06080000626030a08c08030208c08280008626018981000020e08868209490838220600838220e08818220e08a28218580838220e08928214540838218580838220e08616020e08c28218580838280004838220e09000138180a28228a08c06028a08c2821c140a28209c1c928228a08706024a08706024a0892821c180928230a08706024a08170721c1ce06030a08c282281804707 (by decide +kernel)

def state247_49 : List Sig := [0xffffffffffffffff0000000000000000ffffffffffff0000,input 6,input 7,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_49 : Impossible true (goalAt 247) 7 state247_49.toFinset :=
  node_ok cuts247 [⟨state247_5,exclude247_5⟩] 0x868228a08646021a08868224a08545021a08646021a08868219180868219180646021a08868221200848221208a28228200a08228208928224200908224208626038182000018980262418980626009890838221a08252420e08818020e08838220608838228a08616020e08838224a08515020e08616020e08838218580838218580616020e08e06028a08a28230180a2821c140705028a08928228a08706024a08706024a0892821c18092821c180706024a08e06029090e06029090868219180868219180262418980262418980838218580838218580a2821c140a2821c14092821c18092821c180a42438180a42438180c282 (by decide +kernel)

def state247_50 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_50 : Impossible true (goalAt 247) 8 state247_50.toFinset :=
  node_ok cuts247 [⟨state247_6,exclude247_6⟩,⟨state247_48,exclude247_48⟩,⟨state247_49,exclude247_49⟩] 0xe06019090e06029090c28230a08e06030a08c28229090642428182000211c1c47074000cc28230a0a000130a08c2824000c470711c1c642421a08868230a08646030a08642419180646030a08868221a08341421a08868228a08646028a08341419180646028a08868221a08342421a08868224a08545024a08342415140545024a08868221a08a42419180646038180868221a08a42421a08868238180646019181002711100444040008868221a09002721a08868240008444011100c28209890c28230200626030200c28218980c08230200262430208868218980868221200262421200868209890848221200626021208a28214940a28228200626028200a28218980a08228200525028208928218980928224200525024200928214940908224200626024209001218980626038181001238181001240086000038180626018981001210900424040000626018981001218980626040000424010900470720e08838230a08616030a08470718580616030a08838220e09002720e08838221a08252421a09002509490252421a08838220e09001220600818018980838220e09002520e08838218980818020609002420e08838228a08616028a09002518580616028a08838220e09002420e08838224a08515024a09002514540515024a08838220e09002518580616038180838220e09002520e08838238180616018581002510500414040004838220e09002520e08838240004414010500642428a08a28230a08705030a0864241c140705030a08a28228a08e0601c140e06034140a28228a08e06028a08a28234140705030181002440040270715050928224a08c2821c180c2821505070601c180c28224a0892821c140928224a08a2821c180a2821c14070601c180a28224a0892823414070601c180e06024a08928234140928224a08e0601c180706040091001a05c1d002440090c040 (by decide +kernel)

def state247_51 : List Sig := [0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_51 : Impossible true (goalAt 247) 6 state247_51.toFinset :=
  node_ok cuts247 [] 0x646021a08868219180545021a08868215140868219180646021a08868224a08646021a0886822120084822120862601c180525018980525018980626014940262418980626009890928224200908224208838221a08252420e08818020e08838220608616020e08838218580515020e08838214540838218580616020e08838224a08616020e0870501c18070604008870600d090706024180705019090705024140c2821c180928224a0884241c140928224a088414 (by decide +kernel)

def state247_52 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_52 : Impossible true (goalAt 247) 7 state247_52.toFinset :=
  node_ok cuts247 [⟨state247_51,exclude247_51⟩] 0x1c18064241c180342430a08c2821c180c28230a0834241909090601c14054141c140341430a08c2821c140c28230a08341415050905019090868221a08c28219180c28219090646019180c28221a08868240090868221a0892821918092824009c646019180928221a0886820d090646019180706021a0886820d090868221a0870601918064600d050545015140705021a0886820d050868221a08705015140545030a08262430a08c08018980c08030a08626030208c08009890c08221a08626021a08848009890848021a08262421208848018980848224a08424024a08908018980908024a08626024208908010900908240048626018980706014940706040048525014940706018980626040048525014940705018980626040048626018980705014940525011c1c838220e08c28218580c28211c1c616018580c28220e0883824009c838220e08868209490868240094252409490868220e08838240048818020600626020e08838240094838220e08626020600818240090838220e08928218580928240094616018580928220e08838240094616018580706020e08838240094838220e08706018580616040094515014540705020e08838240094838220e08705014540515019090928224a08c28240090c28219092000019090c28224a0892821c18100061c181000424a0892821c180928224a09000440018c0601c14100061c141000524a0892821c140928224a09000540018c0501c14100041c14100051c18070601c14070601c1810005400110004 (by decide +kernel)

def state247_53 : List Sig := [0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000,input 6,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_53 : Impossible true (goalAt 247) 7 state247_53.toFinset :=
  node_ok cuts247 [⟨state247_51,exclude247_51⟩,⟨state247_0,exclude247_0⟩] 0x868219180646021a08646021a08868219180646021a08868219180868219180646021a08868224a08646021a0886822120084822120852501898062601494062603014200011898062601c180525018980262418980626009890928224200908224208838221a08252420e08818020e08838220608838218580616020e08616020e08838218580616020e08838218580838218580616020e08838224a08616020e0870503014200001c14070601c14070604008864241c14070500c140a28238180c0502505090502414070600d09070600c180c28230140928224a0884141c180928224a090006 (by decide +kernel)

def state247_54 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_54 : Impossible true (goalAt 247) 8 state247_54.toFinset :=
  node_ok cuts247 [⟨state247_1,exclude247_1⟩,⟨state247_52,exclude247_52⟩,⟨state247_53,exclude247_53⟩] 0x34140642434140941430a08c28234140c28230a0894141909090501c18064241c180342430a08c2821c180c28230a08342419090306019090868221a08c28219180c28219090646019180c28221a0886820d050868221a0870501918064600d050646019180705021a08868240090868221a0892821918092824009c646019180928221a08868225050646019180d05021a08868225050868221a08d0501918064600d090646019180706021a0886820d090868221a08706019180646030a08262430a08c08018980c08030a08626030208c08009890c08221a08626021a08848009890848021a08262421208848018980848240024525014940705018980626040024626018980705014940525024a08424024a08908018980908024a08626024208908010900908240024626018980d05040024d05040025002180000d05018980626040024626018980706014940706040024525014940706018980626011c1c838220e08c28218580c28211c1c616018580c28220e0883824009c838220e08868209490868240094252409490868220e08838240024818020600626020e08838240094838220e08626020600818240090838220e08705018580616040094616018580705020e08838240090838220e08928218580928240094616018580928220e08838240094616018580d05020e08838240094838220e08d05018580616040094616018580706020e08838240094838220e08706018580616019090341419090c2821c140c2821909070501c140c2820d050c28240015000528a0900241c14070503414100243414100244008600013414070501c14070604004070604001070501c14070601c140706040011002440010642424a08928230a09002430a08642480008642430a08928224a08d05040018d05040090928224a08d05024a08928240091000630140706040018706040010928224a08706024a08928240011000640019000540014e060 (by decide +kernel)

def state247_55 : List Sig := [0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,input 4,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_55 : Impossible true (goalAt 247) 7 state247_55.toFinset :=
  node_ok cuts247 [⟨state247_51,exclude247_51⟩,⟨state247_21,exclude247_21⟩] 0x86821c180545021a08646021a08868219180545021a08868215140868219180646021a08868228a08646021a0886822120084822120862601c180525018980626030182000118980525018980626014940262418980626009890a28228200a08228208838221a08252420e08818020e0883822060883821c180515020e08616020e08838218580515020e08838214540838218580616020e08838228a08616020e0870603018200001c18070501c1807060400a834241c18070600c180928234140c06029090a0602818070501909070500c140c28230180a28228a0884241c140a28228a090006 (by decide +kernel)

def state247_56 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_56 : Impossible true (goalAt 247) 8 state247_56.toFinset :=
  node_ok cuts247 [⟨state247_52,exclude247_52⟩,⟨state247_27,exclude247_27⟩,⟨state247_55,exclude247_55⟩] 0x38180642438180a42430a08c28238180c28230a08a42419090a0601c14054141c140341430a08c2821c140c28230a08341415050305019090868221a08c28219180c28219090646019180c28221a0886820d090868221a0870601514070600d090545015140706021a08868240090868221a08a28219180a2824009c646019180a28221a08868229090646019180e06021a08868229090868221a08e0601918064600d050545015140705021a0886820d050868221a08705015140545030a08262430a08c08018980c08030a08626030208c08009890c08221a08626021a08848009890848021a0826242120884801898084824002c62601898070601494070604002c525014940706018980626028a08424028a08a08018980a08028a08626028208a08010900a0824002c626018980e0604002ce0604002d002180004e0601898062604002c52501494070501898062604002c626018980705014940525011c1c838220e08c28218580c28211c1c616018580c28220e0883824009c838220e08868209490868240094252409490868220e0883824002c818020600626020e08838240094838220e08626020600818240090838220e08706014540706040094515014540706020e08838240090838220e08a28218580a28240094616018580a28220e08838240094616018580e06020e08838240094838220e08e06018580616040094515014540705020e08838240094838220e0870501454051501505034240d090c2821c180c2821505070601c180c2820d090c28240011000424a0900241c18070603818100243418100244008600003818070601c18070504006870504001470601c18070501c180706040015002440014642428a08a28230a09002430a08642480008642430a08a28228a08e06040018e06040090a28228a08e06028a08a28240091000630180705040018705040014a28228a08705028a08a28240015000640019000440010d050 (by decide +kernel)

def state247_57 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 1,input 2,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_57 : Impossible true (goalAt 247) 9 state247_57.toFinset :=
  node_ok cuts247 [⟨state247_43,exclude247_43⟩,⟨state247_50,exclude247_50⟩,⟨state247_54,exclude247_54⟩,⟨state247_56,exclude247_56⟩] 0x4008ce06019090e06040088a42430a08c2824008ce06030a08c28240088a42419090a0604009ca424191806460400a0e06021a0886824009ca42421a088682400a0e06019180646040088642421a088682400a0c28219180c282400a4642419180646040088c28221a08868240010341421a08868240010705019180646040010341419180646040010705021a08868240014342421a08868240014706015140706040014342415140545040014706021a08868240091002421a08868240091000219180646040091002719180646040091000221a08868240024870718980626040024e06040024e06040024870780000850740024e06018980626040024c28209890c28240024c08018980c08040024c28218980c08240024c08009890c08240024868218980868240024848009890848040024868209890848240024848018980848240011000414940525040010705018980626040011000918980626040010705014940525040015000518980626040014706014940706040015000914940525040014706018980626040025000910900424040025000018980626040025000918980626040025000010900424040094870718580616040098e06020e08838240094870720e08838240098e06018580616040088470720e08838240098c28218580c28240094470718580616040088c28220e088382400a1002720e0883824009886820949086824009d002509490252440098868220e08838240025000920600818040024626020e08838240025002520e08838240024626020600818240011000420e08838240010705018580616040011002518580616040010705020e08838240015000520e08838240014706014540706040015002514540515040014706020e08838240091002420e08838240091000118580616040091002518580616040091000120e08838240010e0601c140e06040010d05040010d05040010e0608000ce06040010d0501c14070504001064240d050642440010c2821c140c2824001064241c140705040010c2820d050c28240011000440014a28240014d0501c180706040014e06040014e06040014d05080008d05040014e0601c18070604001454140d090342440014c2821c180c2824001454141c180706040014c2820d090c2824001070504001070504001100051c180706040011000440011000440011000440010928240090e06040018e06040090c04040090c04040090e06080004e06040090c04040018c0404008864244000c642440090c28240090c2824009064244008c642440088c2824000cc282 (by decide +kernel)

def state247_58 : List Sig := [0xf0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0000,input 6,input 5,input 4,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_58 : Impossible true (goalAt 247) 6 state247_58.toFinset :=
  node_ok cuts247 [] 0x18980e0602141c626024a08908024208908214940626018980525030a08c08030208c08220600838220e08818218580838220e08616020e08928214540838220e08616018580838220e08c2821858083821c180928224a08706024a0870601c180928224a08c2821c180928238180d05030180c06038a08c2821c140c28238180c28230a08905021208848221a08848020e08252420e08868219180868221a08646021a08545024a08868221a08646028a08868221a08646030a088682 (by decide +kernel)

def state247_59 : List Sig := [0xffffffffffffffff00000000ffffffffffffffffffffffff00000000ffff0000,input 6,input 5,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_59 : Impossible true (goalAt 247) 7 state247_59.toFinset :=
  node_ok cuts247 [⟨state247_7,exclude247_7⟩,⟨state247_58,exclude247_58⟩] 0x646021a08868219180868224a08545021a08868219180646021a08868230a08646021a0a000121a08868240008868221200848221208626038182000018980928224200908224208525018980626014940c28230200c08230208262418980626009890838221a08252420e08818020e08838220608616020e08838218580838224a08515020e08838218580616020e08838230a08616020e08252420e08838209490706024a0892821c18092821c180706024a08928230a08706024a08342424a0892820d090e06034140c06030180e28230a08705030a0827071c140a28228a08e06030a08c28224140642438180a42438180a424 (by decide +kernel)

def state247_60 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_60 : Impossible true (goalAt 247) 7 state247_60.toFinset :=
  node_ok cuts247 [⟨state247_8,exclude247_8⟩] 0x646021a08868219180868224a08545021a08868219180646021a08868219180646021a08868221200848221208626038182000018980928224200908224208262418980626009890161418980626005850838221a08252420e08818020e08838220608616020e08838218580838224a08515020e08838218580616020e08838218580616020e08706024a0892821c18092821c180706024a0892821c180706024a08868219180868219180525018980525018980838218580838218580c06030180d0503818092821c18092821c18030501c14070501109100031c140a28228a08e06029090a06028180c282381809414381809414 (by decide +kernel)

def state247_61 : List Sig := [0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,input 5,input 4,input 7,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_61 : Impossible true (goalAt 247) 8 state247_61.toFinset :=
  node_ok cuts247 [⟨state247_9,exclude247_9⟩,⟨state247_59,exclude247_59⟩,⟨state247_60,exclude247_60⟩] 0xe06019090e06029090c28230a08e06030a08c28229090642428180642421a08868230a08646030a08642419180646030a08868221a08a42419180646038180868221a08a42421a08868238180646019180342421a08868224a08545024a08342415140545024a08868221a08270721a08868208c0c646019180270719180646008c0c868221a08c28209890c28230200626030200c28218980c08230200262430208868218980868221200262421200868209890848221200626021209001018980626038181001038181001240042000038180626018980928218980928224200525024200928214940908224200626024208270714940525009414626018980270718980626009414525014940470720e08838230a08616030a08470718580616030a08838220e09002720e08838221a08252421a09002509490252421a08838220e09001220600818018980838220e09002520e08838218980818020609001018580616038180838220e09002520e08838238180616018581002420e08838224a08515024a09002514540515024a08838220e08270720e08838209818616018580270718580616009818838220e08541424a08928230a08706030a0854141c180706030a08928224a08d0501c180706038180928224a08d05024a0892823818070601c181002424a08928209c1c70601c18100241c180706009c1c928224a08642409c1c642430a09002430a08642480008442430a08270730a08e06009c1ce06034141002434140e06040040e06034140270734140c2824000cc28219091001019090c28280004c2821909100031909086824000886821918100101918086824009c868219181000219180525040000525018981001018980525040048525018981000018980838240004838218581001018580838240094838218581000118580d05040018d05038181000538180d05040014d0503818100063818092824001092821c18100061c18092824001892821c18100041c181001040090a282 (by decide +kernel)

def state247_62 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_62 : Impossible true (goalAt 247) 6 state247_62.toFinset :=
  node_ok cuts247 [] 0x19180868221a08646015140868221a08545021a08a28219180868221a08928219180868221a08848021208848218980706014940626014940626018980525028a08a08028208a08224a08908024208908220e08868209490838220600838220e08818218580838220e08616014540838220e08515020e08a28218580838220e0892821858083821c14070601c18100221c180a28228a0890601c140a28228a0890501c180928224a08a0601c140928224a08a05024a08a282190909282 (by decide +kernel)

def state247_63 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_63 : Impossible true (goalAt 247) 7 state247_63.toFinset :=
  node_ok cuts247 [⟨state247_51,exclude247_51⟩,⟨state247_62,exclude247_62⟩] 0x21a08928215140868219180868221a08646015140868221a08545021a08646019180868221a08a28219180868221a08848021208848224a08908024208908218980c06014940626014940626018980525009890626018980262428a08a08028208a08220e08868209490838220600838220e08818220e08928214540838218580838220e08616014540838220e08515020e08616018580838220e08a2821858083821c180705024a08928230140928219092000124a08928228a0a000024a08705030180c06040010c06029090a0602818070501909070502c140c28230180a28228a0884241c140a28228a089414 (by decide +kernel)

def state247_64 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_64 : Impossible true (goalAt 247) 7 state247_64.toFinset :=
  node_ok cuts247 [⟨state247_51,exclude247_51⟩,⟨state247_62,exclude247_62⟩] 0x19180868221a08646021a08a28219180868215140868221a08545021a08646019180868221a08928219180868221a08848021208848218980706014940626028a08a08028208a08214940626018980525009890626018980262424a08908024208908220e08868209490838220600838220e08818218580838220e08616020e08a28218580838214540838220e08515020e08616018580838220e0892821858083823014070601c18100051c180a28228a08c0601c140a28215052000128a08a28224a0a000024a0870602909070602c180c05025050905024140c2821c180928224a08a42430140928224a088414 (by decide +kernel)

def state247_65 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_65 : Impossible true (goalAt 247) 8 state247_65.toFinset :=
  node_ok cuts247 [⟨state247_52,exclude247_52⟩,⟨state247_63,exclude247_63⟩,⟨state247_64,exclude247_64⟩] 0x38180642438180a42430a08c28238180c28230a08a42419090a06034140541434140941430a08c28234140c28230a08941415050905019090868221a08c28219180c28219090646019180c28221a08868240090868221a0892821514092824009c545015140928221a08868229090646019180e06021a08868229090868221a08e06019180646040090868221a08a28219180a2824009c646019180a28221a08868225050545015140d05021a08868225050868221a08d05015140545030a08262430a08c08018980c08030a08626030208c08009890c08221a08626021a08848009890848021a08262421208848018980848224a08626024a08908014940908024a08525024208908018980908240028626018980e06014940e06040028525014940e06018980626028a08525028a08a08018980a08028a08626028208a08014940a08240028525014940d05018980626040028626018980d05014940525011c1c838220e08c28218580c28211c1c616018580c28220e0883824001c838220e0886820949086824001c252409490868220e0883824001c818020600626020e0883824001c838220e0862602060081824001c838220e0892821454092824001c515014540928220e0883824001c616018580e06020e0883824001c838220e08e0601858061604001c838220e08a28218580a2824001c616018580a28220e0883824001c515014540d05020e0883824001c838220e08d05014540515015050928224a08c28240090c28215052000215050c28224a0892824001900061c181002424a08928228a09002428a09002440092000028a08928224a08d05040068d05040014928224a08d05024a08928240015002430140d05040010d05040014e06038180d05038180e06040015000440010642428a08a28230a09002430a08642480004642430a08a28228a08e06040040e06040010a28228a08e06028a08a282400110024301810006400187050 (by decide +kernel)

def state247_66 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 5,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_66 : Impossible true (goalAt 247) 8 state247_66.toFinset :=
  node_ok cuts247 [⟨state247_16,exclude247_16⟩] 0x34140c28230a08905019090c28230a08642411c1cc28230a08470721a08c28219180868219180868221a08646021a08928215140868219180868221a08646021a08a28219180868211100868221a08444030a08c08030208c08221a08848021208848218980d05080000626024a08908024208908218980525014940626028a08a08028208a08210900626018980424020e08c28218580838220e08868209490838220600838220e08818218580838220e08616020e08928214540838218580838220e08616020e08a28218580838210500838220e08414038181002424a08c28215050928234140928230140706024a08a2821c140928240069000428a08c2821c140a2821c140a28228a08705040040a282400902707 (by decide +kernel)

def state247_67 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_67 : Impossible true (goalAt 247) 9 state247_67.toFinset :=
  node_ok cuts247 [⟨state247_54,exclude247_54⟩,⟨state247_20,exclude247_20⟩,⟨state247_50,exclude247_50⟩,⟨state247_61,exclude247_61⟩,⟨state247_65,exclude247_65⟩,⟨state247_66,exclude247_66⟩] 0x40018d05019090d05040018941430a08c28240018d05030a08c28240018941419090905040041002b190906424400a9000330a08c282400ad002b30a08c282400a90003190906424400a8642428a08a28240090c2821c140c282400ac64241c1407050400a8c28228a08a2824001900061c140705040018d05028a08a2824001a000428a08a28240018d0501c140705040042000309c1c270740091000428a08a28280016000228a08a28240091000409c1c2707400a8642421a08868240038c28219180c282400b46424191806460400a8c28221a08868240090341421a08868240038a28219180a2824009c341419180646040038a28221a08868240018941419180646040018d05021a08868240018941421a08868240018d05019180646040015000521a08868240014928215140928240015002c15140545040014928221a08868240041002c19180646040039000221a088682400b1002c21a08868240039000219180646040024c28209890c28240024c08018980c08040024c28218980c08240024c08009890c08240024a28214940a28240024a08018980a08040024a28218980a08240024a08014940a08240024868218980868240024848009890848040024868209890848240024848018980848240019000618980626040018d05040018d0504001900094001a000140018d0501898062604001492821898092824001490801494090804001492821494090824001490801898090824002500091898062604002500001494052504002500091494052504002500001898062604001c470720e0883824001cc28218580c2824001c47071858061604001cc28220e0883824001c270720e0883824001ca28218580a2824001c27071858061604001ca28220e0883824001d000720e0883824001c86820949086824001d00070949025244001c868220e0883824001d00072060081804001c626020e0883824001d000720e0883824001c626020600818240019000618580616040018d05020e08838240019000720e08838240018d05018580616040015000520e08838240014928214540928240015000714540515040014928220e0883824001d00071858061604001d000120e0883824001d000720e0883824001d000118580616040019000640014e06040014541424a08928240014c28240014c282400145414400ac541440014c28224a08928240014705024a08928240014a28240014a28240014705080000705040014a28224a08928240018d05040018d05040019000524a08928240019000640018c050400190006400187060 (by decide +kernel)

def state247_68 : List Sig := [0xf0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f00000000,input 6,input 4,input 5,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_68 : Impossible true (goalAt 247) 6 state247_68.toFinset :=
  node_ok cuts247 [] 0x18980e0602141c626028a08a08028208a08218980706014940626030a08c08030208c08220600838220e08818218580838220e08616020e08a28218580838220e08706014540838220e08c28218580838238180a28228a08c06028a08c2821c140a2821c180e0603014070601c140a2821c180a28234a08c2821c180c28238180c28230a08a06021208848221a08848020e08252420e08868219180868221a08646021a08646028a08868221a08545024a08868221a08646030a088682 (by decide +kernel)

def state247_69 : List Sig := [0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff00000000,input 6,input 4,input 5,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_69 : Impossible true (goalAt 247) 7 state247_69.toFinset :=
  node_ok cuts247 [⟨state247_24,exclude247_24⟩,⟨state247_68,exclude247_68⟩] 0x646021a08868219180868228a08646021a0886821c180545021a08868230a08646021a0a000121a08868240008868221200848221208626038182000018980a28228200a0822820862601c180525018980c28230200c08230208161418980626005850838221a08252420e08818020e08838220608616020e08838218580838228a08616020e0883821c180515020e08838230a08616020e08151420e08838205450e06028a08a28230180a28230a08705028a08341428a08a2820d050706038180c0501c180705028a08706028a08d28230a08706030a0817071c180928224a08e06030a08c282281805414381809414381809414 (by decide +kernel)

def state247_70 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000,input 5,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_70 : Impossible true (goalAt 247) 7 state247_70.toFinset :=
  node_ok cuts247 [⟨state247_25,exclude247_25⟩] 0x646021a08868219180868228a08646021a08868219180646021a08868219180646021a08868221200848221208626038182000018980a28228200a08228208262418980626009890262418980626009890838221a08252420e08818020e08838220608616020e08838218580838228a08616020e08838218580616020e08838218580616020e08e06028a08a28230180a2821c140705028a08a2821c140705028a0886821514086821c18062601494062601c18083821454083821c180706030140e0601c180a2821c180a2821c14030601c18070601105100031c180928224a08e06029090e06024140c28238180a42438180a424 (by decide +kernel)

def state247_71 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000,input 4,input 5,input 7,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_71 : Impossible true (goalAt 247) 8 state247_71.toFinset :=
  node_ok cuts247 [⟨state247_26,exclude247_26⟩,⟨state247_69,exclude247_69⟩,⟨state247_70,exclude247_70⟩] 0xe06019090e06029090c28230a08e06030a08c28229090642428180642421a08868230a08646030a08642419180646030a08868221a08a42419180646038180868221a08a42421a08868238180646019180341421a08868228a08646028a08341419180646028a08868221a08170721a08868204c0c545015140170715140545004c0c868221a08c28209890c28230200626030200c28218980c08230200262430208868218980868221200262421200868209890848221200626021209001a18980626038181001a3818100124006a000038180626018980a28214940a28228200626028200a28218980a08228200525028208170718980626005414525014940170714940525005414626018980470720e08838230a08616030a08470718580616030a08838220e09002720e08838221a08252421a09002509490252421a08838220e09001220600818018980838220e09002520e08838218980818020609001a18580616038180838220e09002520e08838238180616018581002420e08838228a08616028a09002518580616028a08838220e08170720e08838205818515014540170714540515005818838220e08642428a08a28230a08705030a0864241c140705030a08a28228a08e0601c140e06034140a28228a08e06028a08a28234140705030180541405c1c541430a09002430a08541480008441430a08170730a08d05005c1cd05038181002438180d05040068d05038180170738180705005c1c705028a09002428a08705040090705028a08170728a08c2824000cc28215051001a15050c28280004c28215051000315050868240008868215141001a1514086824009c868215141000215140626040000626014941001a14940626040048626014941000014940838240004838214541001a14540838240094838214541000114540e06040018e06034141000434140e06040010e06034141000634140a28240010a2821c14100061c140a28240018a2821c14100041c141001a400909282 (by decide +kernel)

def state247_72 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 4,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_72 : Impossible true (goalAt 247) 8 state247_72.toFinset :=
  node_ok cuts247 [⟨state247_34,exclude247_34⟩] 0x38180c28230a08a06015050c28230a08541411c1cc28230a08470721a08c28219180868219180868221a08646021a08a28219180868215140868221a08545021a08928215140868211100868221a08444030a08c08030208c08221a08848021208848218980e06080000626028a08a08028208a08214940626018980525024a08908024208908210900626018980424020e08c28218580838220e08868209490838220600838220e08818218580838220e08616020e08a28218580838214540838220e08515020e08928214540838210500838220e08414034141002428a08c28219090a28238180a28230180705040041000524a08c2821c18092821c180928224a08706024a08a2821c1809282400689282400901707 (by decide +kernel)

def state247_73 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_73 : Impossible true (goalAt 247) 9 state247_73.toFinset :=
  node_ok cuts247 [⟨state247_38,exclude247_38⟩,⟨state247_50,exclude247_50⟩,⟨state247_56,exclude247_56⟩,⟨state247_65,exclude247_65⟩,⟨state247_71,exclude247_71⟩,⟨state247_72,exclude247_72⟩] 0x40018e06019090e06040018a42430a08c28240018e06030a08c28240018a42419090a06040069002e15050541440089000330a08c282400b9002e30a08c28240089000315050541440088541424a08928240090c2821c180c282400b854141c180706040088c28224a0892824001900061c180706040018e06024a0892824001a000324a08928240018e0601c180706040011000424a08928240010a2821c180a2824001200021c180706040010a28224a0892824006a000405c1c170740091000524a08928280016000124a08928240091000505c1c170740088642421a08868240038c28219180c282400a4642419180646040088c28221a08868240090342421a0886824003892821514092824009c342415140545040038928221a08868240018a42419180646040018e06021a08868240018a42421a08868240018e06019180646040011000421a08868240010a28219180a28240011002f19180646040010a28221a08868240069002f15140545040039000221a088682400bd002f21a08868240039000215140545040028c28209890c28240028c08018980c08040028c28218980c08240028c08009890c08240028928218980928240028908014940908040028928214940908240028908018980908240028868218980868240028848009890848040028868209890848240028848018980848240019000618980626040018e06040018e06040019000a4001a000040018e06018980626040010a28214940a28240010a08018980a08040010a28218980a08240010a08014940a08240029000a14940525040029000018980626040029000a1898062604002900001494052504001c470720e0883824001cc28218580c2824001c47071858061604001cc28220e0883824001c170720e0883824001c92821454092824001c17071454051504001c928220e0883824001d000720e0883824001c86820949086824001d00070949025244001c868220e0883824001d00072060081804001c626020e0883824001d000720e0883824001c626020600818240019000618580616040018e06020e08838240019000720e08838240018e06018580616040011000420e08838240010a28218580a28240011000718580616040010a28220e0883824001d00071454051504001d000120e0883824001d000720e0883824001d000114540515040019000640010d05040010642428a08a28240010c28240010c282400106424400b8642440010c28228a08a28240018e06040018e06040019000428a08a28240019000640018c060400190006400187050 (by decide +kernel)

def state247_74 : List Sig := roots 247
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_74 : Impossible true (goalAt 247) 10 state247_74.toFinset :=
  node_ok cuts247 [⟨state247_44,exclude247_44⟩,⟨state247_57,exclude247_57⟩,⟨state247_67,exclude247_67⟩,⟨state247_73,exclude247_73⟩] 0x4000ce06019090e0604000ca42430a08c2824000ce06030a08c2824000ca42419090a06040018e0601c140e06040010d05028a08a2828000ce06028a08a28240018d0501c140c0604000c642428a08a2824000cc2821c140c2824000c64241c14070504000cc28228a08a28240018d0501c180706040014e06024a08928280008d05024a08928240018e0601c18070604000c541424a0892824000cc2821c180c2824000c54141c18070604000cc28224a08928240010705024a08928240014a2821c180a2828000470501c180706040010a28224a08928240008a42419180646040008e06021a08868240008a42421a08868240008e0601918064604000c642421a0886824000cc28219180c2824000c64241918064604000cc28221a08868240008341421a08868240008a28219180a28240008341419180646040008a28221a08868240008342421a08868240008928215140928240008342415140545040008928221a08868240000870718980626040000e06040000e06040000870780000850740000e06018980626040000c28209890c28240000c08018980c08040000c28218980c08240000c08009890c08240000a28214940a28240000a08018980a08040000a28218980a08240000a08014940a08240000928218980928240000908014940908040000928214940908240000908018980908240000868218980868240000848009890848040000868209890848240000848018980848240004870718580616040004e06020e08838240004870720e08838240004e0601858061604000c470720e0883824000cc28218580c2824000c47071858061604000cc28220e08838240004270720e08838240004a28218580a28240004270718580616040004a28220e08838240004170720e08838240004928214540928240004170714540515040004928220e08838240009000220e08838240008868209490868240009000109490252440008868220e08838240001000020600818040000626020e08838240001000120e088382400006260206008182 (by decide +kernel)

theorem lower247 : Claim 247 11 :=
  fromSearch 1604 (by decide +kernel) exclude247_74


open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

def smallCircuit : Circuit := ⟨[⟨.or, [4, 5]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [9, 11]⟩, ⟨.and, [12, 7]⟩, ⟨.and, [13, 6]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [19, 17]⟩], 20⟩

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


def lowRow (i : Fin 8) : Row := Fin.ofNat 256 (1 <<< ([4, 4, 6, 6, 0, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 256 ((1 <<< i.val) ||| (1 <<< ([4, 4, 6, 6, 0, 0, 0, 0] : List Nat).getD i.val 0))

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

end PEqualNP.Outside.L_meta_31081_aux

open PEqualNP.Outside.L_meta_31081_aux in
theorem PEqualNP.Outside.L_meta_31081 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true))  := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct

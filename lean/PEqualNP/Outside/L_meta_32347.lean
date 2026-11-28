import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32347_aux


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
  (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 4 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)


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
  fromLift 5 2 353370192 lower224 (by decide +kernel)

theorem lower210 : Claim 210 5 :=
  fromLift 5 2 335937648 lower208 (by decide +kernel)

def cuts162 : Cuts (goalAt 162) := []

def state162_0 : List Sig := roots 162
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude162_0 : Impossible true (goalAt 162) 3 state162_0.toFinset :=
  node_ok cuts162 [] 0x28080220228080820228200a08028080a08028200820208808220220808222008880a02020a00828020808828020a00a02008880222008808828020a00a08008880a08008808222008880a08020a008280 (by decide +kernel)

theorem lower162 : Claim 162 4 :=
  fromSearch 269484112 (by decide +kernel) exclude162_0

theorem lower178 : Claim 178 5 :=
  fromLift 5 2 269811792 lower176 (by decide +kernel)

theorem lower114 : Claim 114 5 :=
  fromLift 5 2 68485200 lower112 (by decide +kernel)

def rule242_0 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower240 none (by decide +kernel)

def rule242_1 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower226 none (by decide +kernel)

def rule242_2 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower210 none (by decide +kernel)

def rule242_3 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower162 none (by decide +kernel)

def rule242_4 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower178 none (by decide +kernel)

def rule242_5 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower114 none (by decide +kernel)

def rule242_6 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower224 none (by decide +kernel)

def rule242_7 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower176 none (by decide +kernel)

def rule242_8 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower208 none (by decide +kernel)

def rule242_9 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower112 none (by decide +kernel)

def cuts242 : Cuts (goalAt 242) := [rule242_0,rule242_1,rule242_2,rule242_3,rule242_4,rule242_5,rule242_6,rule242_7,rule242_8,rule242_9]

def state242_0 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 7,input 5,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_0 : Impossible true (goalAt 242) 4 state242_0.toFinset :=
  node_ok cuts242 [] 0x18080c08030200602014108c08030201000720a00c08014048828020a00a08008880828008880828020a00222014108828020a01000028200c08018080a08028080a08028200221218908c242 (by decide +kernel)

def state242_1 : List Sig := [0xffffffffffff0000ffffffffffff0000,input 7,input 5,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_1 : Impossible true (goalAt 242) 4 state242_1.toFinset :=
  node_ok cuts242 [] 0xc24230200c08020908828030200501220a00828028200222020a00c24220a00828030108a08030200602028200e24228200a08030908602030200504230200504020a00504220a00504228200221228200a020 (by decide +kernel)

def state242_2 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_2 : Impossible true (goalAt 242) 4 state242_2.toFinset :=
  node_ok cuts242 [] 0x602030200c08018080501230200c08008848828030200501220a00828024200504220a00222020a00828008880221220a00828040018a08030200504228200504228200a08014108504228200a08014108c242 (by decide +kernel)

def state242_3 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_3 : Impossible true (goalAt 242) 5 state242_3.toFinset :=
  node_ok cuts242 [⟨state242_0,exclude242_0⟩,⟨state242_1,exclude242_1⟩,⟨state242_2,exclude242_2⟩] 0xc24218080c24228080c08030200c24230200c08028080602020908c24208880c24230100828020a00c24220a00828030100222030108501220a0082803020100063020050124000c501230200828020a00221220a00828040018222008880221208880222040018828020a00504220a00828040000222024200504208880504240000828020a00a02008848a02030909000830908a02080008a0203090822123090860200884860203020100083020060204000c602030200221230201000140004a08028080504214108c24280004c24228082000028080c24214108504218081000718080c08014108c08018080504214108c0804001cc080 (by decide +kernel)

def state242_4 : List Sig := [0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,input 5,input 7,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_4 : Impossible true (goalAt 242) 4 state242_4.toFinset :=
  node_ok cuts242 [] 0x602030200c08018080828030200501220a00222020a00828008880828018100604220a00602030200624230200624238908a02018908c08014108c08018080828014108828008880504230908821214108a080 (by decide +kernel)

def state242_5 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_5 : Impossible true (goalAt 242) 4 state242_5.toFinset :=
  node_ok cuts242 [] 0x504230200c08018080501230200c08014048828030200501220a00504220a00828008880828028200222020a00821220a00828040018504230908a02014108a08030200602028200a02028200a080141086242 (by decide +kernel)

def state242_6 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_6 : Impossible true (goalAt 242) 5 state242_6.toFinset :=
  node_ok cuts242 [⟨state242_0,exclude242_0⟩,⟨state242_4,exclude242_4⟩,⟨state242_5,exclude242_5⟩] 0x1000318080602020848c08030201000330200c0802084860201808050421808050424001cc08030200504230200c0804001c602018080602028200a08030200624230200602018908624230200a08028201000918908624220848a08028202000228200a0802084862421890a000118908624214108a08028202000028200a08014108624214108501220a0082803020100063020050124000c501230200828020a00624220a00828028200222028200624208880604228200828020a00821208880222040018828020a00821220a00828040018222008880504208880504240000828020a00504220a00828040000222008881000140004c242 (by decide +kernel)

def state242_7 : List Sig := [0x333300003333000033330000333300003333000000000000333300000000,input 5,input 7,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_7 : Impossible true (goalAt 242) 4 state242_7.toFinset :=
  node_ok cuts242 [] 0xc24230200c08020908501230200504230200504230908821214108504228200221228200a08030200624228200624228200a08018908828014048c08020a00908030108828020a00c24220a006042282008280 (by decide +kernel)

def state242_8 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_8 : Impossible true (goalAt 242) 5 state242_8.toFinset :=
  node_ok cuts242 [⟨state242_0,exclude242_0⟩,⟨state242_2,exclude242_2⟩,⟨state242_5,exclude242_5⟩,⟨state242_7,exclude242_7⟩] 0x18080c08030200602014048c08030200501214048c08014108c08024200504228082000214108504228202000128200504240006000014108828030200501220a00222020a00828008880828028200222020a02000320a00828040018c24228200c08018080a08028080a080400206242 (by decide +kernel)

def state242_9 : List Sig := [0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_9 : Impossible true (goalAt 242) 6 state242_9.toFinset :=
  node_ok cuts242 [⟨state242_3,exclude242_3⟩,⟨state242_6,exclude242_6⟩,⟨state242_8,exclude242_8⟩] 0x4000cc24218080c2424001ca02030200c0804000cc24230200c0804001ca02018080824240024a02018908624240020c24228200a08080008a02028200a08040020c2421890862424001c602028200a08040020c08018908c0804000c602018908624240020c08028200a08040004901214108504240004c24240004c24240004901280004821240004c2421410850424000450124001c501240004c08014108c08040004501214108504240004c08040004c08040004301214108504240004a08040004a08040004301280000221240004a08014108a08040001000040000908040018c24208880c24240018c04020a00828040018c24220a00828040018c04008880c04240018501220a00828040018c08040018c0804001850124000c501240018c08020a00828040018624220a00828040018a08008880a08040018624208880604240018a08020a008280 (by decide +kernel)

def state242_10 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 5,input 7,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_10 : Impossible true (goalAt 242) 4 state242_10.toFinset :=
  node_ok cuts242 [] 0x24200828014108828014108908024200504224200a0800c080908014048908024201000620908828020a00222014048828020a01000024848a08020a00604220a00604228200a080181083212 (by decide +kernel)

def state242_11 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff0000000000000000,input 5,input 7,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_11 : Impossible true (goalAt 242) 4 state242_11.toFinset :=
  node_ok cuts242 [] 0x908020a00504220a0050422420090801410890800c080302024200824220a00828008880222020a00222020a00a02020908a0202090890800c08090800c080828008880828008880824228080824228080a080 (by decide +kernel)

def state242_12 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_12 : Impossible true (goalAt 242) 4 state242_12.toFinset :=
  node_ok cuts242 [] 0x908020a00504220a0030202420090800c080908028200302024200504224200908014108222020a00828008880824220a0082804001ca08020a00222020a00a02028200a080140486042280808242209085012 (by decide +kernel)

def state242_13 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_13 : Impossible true (goalAt 242) 5 state242_13.toFinset :=
  node_ok cuts242 [⟨state242_10,exclude242_10⟩,⟨state242_11,exclude242_11⟩,⟨state242_12,exclude242_12⟩] 0x222028200a08020a00604220a00222018108604220a00a08020a01000918108604220908a08028202000228200a0802090860421810a00010c848321214048a08028202000028200a0801404832120890032122420090802820030202820032120c080302028200908024201000724200908020a00504220a01000314108504220a00908020a0100031410850422090890802420100032420090802090850421410850120c08030204001890802420050122420090804001830200c08082420888082424001c828020a00824220a0082804001c222008880501208880222040000828020a00501220a00828040000222008881000440010a020 (by decide +kernel)

def state242_14 : List Sig := [0xffffffffffffffffffffffff00000000,input 7,input 5,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_14 : Impossible true (goalAt 242) 4 state242_14.toFinset :=
  node_ok cuts242 [] 0x908020a00504220a00908028200302024200504224200908014108222020a00828008880a08020a00604220a00604228200a08018108504224200504224200222020a00222020a006042282006042282008242 (by decide +kernel)

def state242_15 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_15 : Impossible true (goalAt 242) 4 state242_15.toFinset :=
  node_ok cuts242 [] 0x908020a00504220a00908028200504224200504224200908014108504224200908014108828028200222020a00222020a00828008880604220a0082804001ca02028200a08014048604228200a08014048a242 (by decide +kernel)

def state242_16 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_16 : Impossible true (goalAt 242) 5 state242_16.toFinset :=
  node_ok cuts242 [⟨state242_10,exclude242_10⟩,⟨state242_14,exclude242_14⟩,⟨state242_15,exclude242_15⟩] 0x921214108504230108908024200921224200908030108504214109000724200908020a00504220a01000314108504220a00908020a0100082420090801810830201810900030c080302018108908024200501224200908040018504214108501214108504240018908024200c04208880c04228080828020a00c04220a00828028080222008880501220a00828040000222030200501208880222040000828020a00a02018108604230109000828908a02080008a0203010860421810822204001c222020a00604220a00222018108604220a01000820a01000440010a0803010850123010892128000492123010a0000209089212140488242 (by decide +kernel)

def state242_17 : List Sig := [0x333333333333333300000000000000003333333300000000,input 5,input 7,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_17 : Impossible true (goalAt 242) 4 state242_17.toFinset :=
  node_ok cuts242 [] 0x908014108504224200504224200908014108908028200302024200c04228080824220908a08018108604228200604228200a08018108828014108908020a00c08008880828020a00c04220a006042282008280 (by decide +kernel)

def state242_18 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_18 : Impossible true (goalAt 242) 5 state242_18.toFinset :=
  node_ok cuts242 [⟨state242_15,exclude242_15⟩,⟨state242_10,exclude242_10⟩,⟨state242_12,exclude242_12⟩,⟨state242_17,exclude242_17⟩] 0x24200504214108908024200828014108828014108908024200504224200a0800c080908014108908024200504230200501228082000228080501240012000114048222020a00828008882000320a0082804001cc04228200501280000a08028200828008880828028080a080400206042 (by decide +kernel)

def state242_19 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_19 : Impossible true (goalAt 242) 6 state242_19.toFinset :=
  node_ok cuts242 [⟨state242_13,exclude242_13⟩,⟨state242_16,exclude242_16⟩,⟨state242_18,exclude242_18⟩] 0x40024a02018108604240020c04228200a08080008a02028200a08040020c04218108604240011000428200a08040010501218108604240012000118108604240010501228200a0804001c222028200a0804002082801810882804001c22201810860424002082802820082804000c921214108504240018c0422420090804000c921224200908040018c04214108504240020321224200908040018a0800c080a0804000c32120c080302040018a0802420090804001050122420090804001100061410850424001050121410850424001100042420090804001d00072420090804001882801410882804001d000314108504240018828024200828040010c04214048c04240010a02040010a02040010c04280000824240010a02014048824240001000040000c0804001cc04208880c0424001ca02020a0082804001cc04220a0082804001ca020088802220 (by decide +kernel)

def state242_20 : List Sig := [0x3333333333333333333333333333333333333333333300003333333333330000,input 7,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_20 : Impossible true (goalAt 242) 4 state242_20.toFinset :=
  node_ok cuts242 [] 0x30908c08030200824228200c08018908a08018908a08028200624224200c08014908908024200a0800c080908014908908024200524220a00501230200828020a00604228200828020a00504224200828030108828020a00c242 (by decide +kernel)

def state242_21 : List Sig := [0xffffffffffffffff0000000000000000ffffffffffff0000,input 7,input 4,input 5,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_21 : Impossible true (goalAt 242) 4 state242_21.toFinset :=
  node_ok cuts242 [] 0x20a00a08018108828020a00908014108828030908828020a00c04218908a08028200624224200a0800c080908014908908024200524220a00501220a00c08028200624228200c08024200524224200c08020908c08030200c242 (by decide +kernel)

def state242_22 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_22 : Impossible true (goalAt 242) 5 state242_22.toFinset :=
  node_ok cuts242 [⟨state242_0,exclude242_0⟩,⟨state242_20,exclude242_20⟩,⟨state242_21,exclude242_21⟩] 0x602030200c08018082000230200c08040010828030200501220a00828028200222020a00828024202000020a00222020a00828008882000120a00828040000a08030200602028200a02028200a0800c848624224200c08014848908024200a0800c08090800c080908024200302014908c242 (by decide +kernel)

def state242_23 : List Sig := [0xffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_23 : Impossible true (goalAt 242) 5 state242_23.toFinset :=
  node_ok cuts242 [⟨state242_1,exclude242_1⟩] 0xc24230200c08020908828030200501220a00828028200222020a00828024202000020a00c24220a00828030108a08030200602028200e24228200a08030908908030200521224200908028200302024200d24224200908030908602030200602030200222020a00222020a00624228200321228200524224200302024200a020 (by decide +kernel)

def state242_24 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_24 : Impossible true (goalAt 242) 4 state242_24.toFinset :=
  node_ok cuts242 [] 0x18080c08030200302014848c08030200321220a00c08014048828020a00908008880828008880828020a0022200c848828020a00301224200c08018080908014908908024201000218908908024200821230908c2420c0802212 (by decide +kernel)

def state242_25 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_25 : Impossible true (goalAt 242) 5 state242_25.toFinset :=
  node_ok cuts242 [⟨state242_24,exclude242_24⟩] 0x18080c08030200602018080c08030200302020a00c08014048828020a00222008880828020a00908008880828008880828020a00222008880828020a00222018080c08018080c0802820032122484a00000c84830200c848302008848908030200602024200921224200908020848524224200908040008c242 (by decide +kernel)

def state242_26 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_26 : Impossible true (goalAt 242) 5 state242_26.toFinset :=
  node_ok cuts242 [⟨state242_24,exclude242_24⟩,⟨state242_2,exclude242_2⟩] 0x18080c08030200602014848c08030200321220a00c08014048828020a00302080004828020a00a08008880828008880828020a0022200c848828020a0030120c080c08014848c0802420030202408200000c08032120c080302008848a08030200602028200a02028200a08040014624228200a08040004c242 (by decide +kernel)

def state242_27 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_27 : Impossible true (goalAt 242) 6 state242_27.toFinset :=
  node_ok cuts242 [⟨state242_3,exclude242_3⟩,⟨state242_22,exclude242_22⟩,⟨state242_23,exclude242_23⟩,⟨state242_25,exclude242_25⟩,⟨state242_26,exclude242_26⟩] 0xc24218080c24228080c08030200c24230200c08028080602020908c24208880c24230100828020a00c24220a00828030100222030108521220a0082803020100063020052124000c501230200828020a00321220a0082800c04022200888032120888022200c040828020a01000120a0082800c08100010c08100064000600000c080828020a01000620a00828040000222008881000608880222040000828020a00a0200c848a02030909000230908a02080010a0203090832123090860200c84860203020100023020060204000c602030200321230201000140004a0802484830200c080c24240004c2422484a000324848c2420c080c2421484830200c080c08040004c08014849000314848c0800c080c0800c84900020c84900010c080302040005000108849000140008908028081000528080c24280008c24228082000128080c24240014c24218081000418080c0804000cc08018081000318080c08040010c080 (by decide +kernel)

def state242_28 : List Sig := [0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,input 5,input 4,input 7,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_28 : Impossible true (goalAt 242) 5 state242_28.toFinset :=
  node_ok cuts242 [⟨state242_4,exclude242_4⟩] 0x602030200c08018080828030200501220a00222020a00828008880828024202000020a00828018100604220a0090803020052122420030202420090800c080908018908302024200602030200624230200624238908a02018908c08018080c08018080828008880828008880c2423090892122808090801490890800c080a080 (by decide +kernel)

def state242_29 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_29 : Impossible true (goalAt 242) 5 state242_29.toFinset :=
  node_ok cuts242 [⟨state242_24,exclude242_24⟩,⟨state242_5,exclude242_5⟩] 0x18080c08030200602014848c08030200521220a00c08014048828020a00908080004828008880828020a00222020a00a08008880828024848828020a00901224200c08014848908014908908028202000024200921224200908020848c24230908a02040004a08030200602028200a02028200a080400086242 (by decide +kernel)

def state242_30 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_30 : Impossible true (goalAt 242) 6 state242_30.toFinset :=
  node_ok cuts242 [⟨state242_25,exclude242_25⟩,⟨state242_6,exclude242_6⟩,⟨state242_22,exclude242_22⟩,⟨state242_28,exclude242_28⟩,⟨state242_29,exclude242_29⟩] 0x1000518080602024848c08030201000330200c08024848602018081000318080602040010c08030201000330200c08040010602018080602028200a08030200624230200602018908624230200a08028201000518908624224848a08028202000428200a0802484862421890a000318908624240008a08028202000228200a08040008624218908521220a0082803020100063020052124000c501230200828020a00624220a00828028200222028200624208880604228200828020a00921208880222024040828020a00921220a00828024040222008881000120a00828024201000124201000640006000124200828020a01000608880222040000828020a01000620a00828040000222008881000140004c24214848908024200c08040004c08014849000314848c0802420090800c848908024200a08040004a0800c84a00000c848a080242009080248490005248490001242009080400050001208490001400145242 (by decide +kernel)

def state242_31 : List Sig := [0x3333333333333333333333333333333333333333333333333333333300000000,input 7,input 5,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_31 : Impossible true (goalAt 242) 4 state242_31.toFinset :=
  node_ok cuts242 [] 0x24200c08014908908024200a0800c080908014908908024200524230908c08030200824228200c08018908a08018908a08028200624220a00504224200828020a00501230200828020a00604228200828030108828020a00c242 (by decide +kernel)

def state242_32 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000,input 7,input 5,input 6,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_32 : Impossible true (goalAt 242) 4 state242_32.toFinset :=
  node_ok cuts242 [] 0x20a00c08014048828020a00a08018108828030908828020a00c04230908c08030200824228200c08018908a08018908a08028200624220a00504220a009080242005242302009080242003020282009080149089080242005242 (by decide +kernel)

def state242_33 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 7,input 5,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_33 : Impossible true (goalAt 242) 5 state242_33.toFinset :=
  node_ok cuts242 [⟨state242_10,exclude242_10⟩,⟨state242_31,exclude242_31⟩,⟨state242_32,exclude242_32⟩] 0x90803020052422420090802820030202420052422420090801490a000224200908040004828024200504220a00828030202000020a00828028200604220a00c24220a0082803010a000120a00828040000c24230200c08020908521228200c08018908a08018908a0802820062420c8489212 (by decide +kernel)

def state242_34 : List Sig := [0xffffffffffffffffffffffff00000000,input 7,input 5,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_34 : Impossible true (goalAt 242) 5 state242_34.toFinset :=
  node_ok cuts242 [⟨state242_14,exclude242_14⟩] 0x908030200524224200908028200302024200524224200908014908828024200504220a00828030202000020a00828028200604220a00222020a00828008880602030200c08018080a08030200624228200624228200a08018908524224200524224200222020a00222020a00602030200602030200624228200624228200c242 (by decide +kernel)

def state242_35 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_35 : Impossible true (goalAt 242) 4 state242_35.toFinset :=
  node_ok cuts242 [] 0x24200a0801490890801490890802420052420c080908024200302020a00908014108828020a00a08008880828018908828020a00604208880828020a00222018908a08028200824218080a080282010002180806242189082242 (by decide +kernel)

def state242_36 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_36 : Impossible true (goalAt 242) 5 state242_36.toFinset :=
  node_ok cuts242 [⟨state242_15,exclude242_15⟩,⟨state242_35,exclude242_35⟩] 0x24200524214908908024200a08014908908014908908024200524214908908024200524220a00908014108828020a00602080000828020a00a08008880828008880828020a00222018908828020a00604230200602028082000118080624218080624208908a02028200a08040014624228200a08040010c242 (by decide +kernel)

def state242_37 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_37 : Impossible true (goalAt 242) 5 state242_37.toFinset :=
  node_ok cuts242 [⟨state242_35,exclude242_35⟩] 0x2420062420c080908024200c0801490890801490890802420052420c080908024200302020a00908014108828020a00604018108828020a00c08008880828030908828020a00c04208880828020a0022202820062422890a000018908602018908624208908c24230200c08020908602030200c08040008a020 (by decide +kernel)

def state242_38 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_38 : Impossible true (goalAt 242) 6 state242_38.toFinset :=
  node_ok cuts242 [⟨state242_16,exclude242_16⟩,⟨state242_33,exclude242_33⟩,⟨state242_34,exclude242_34⟩,⟨state242_36,exclude242_36⟩,⟨state242_37,exclude242_37⟩] 0x92121490852423090890802420092122420090803090852421490900042420090801808052421490900031490852421808090802420100022420090801890830201890900030c080302018908908024201000324200908040004524214909000314908524240004908024200c24208880c24230100828020a00c24220a00828030100222030108524220a0082802420100082420052424000c504224200828020a01000420a00828018081000418081000840012000018080828020a00624220a00828018100222018100624208880604218100828020a01000820a00828040000222008881000808880222040000828020a00c24218080c24228081000428080c24280010c24228080602018081000240008c08028080624218908c24240008c24228082000328080c24218908624218081000418081000218908624240009000208909000240010a0803090900053090892128000892123090a0001309089212400149212 (by decide +kernel)

def state242_39 : List Sig := [0xffff3333ffff33330000000000000000ffff3333ffff0000,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_39 : Impossible true (goalAt 242) 3 state242_39.toFinset :=
  node_ok cuts242 [] 0x18108a08028200604214108908024200504224200a0800c080908008880828020a00824220a00604228200828020a005042242008280 (by decide +kernel)

def state242_40 : List Sig := [0xffff3333ffff3333ffff3333ffff3333ffff3333ffff0000ffff3333ffff0000,input 4,input 5,input 7,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_40 : Impossible true (goalAt 242) 4 state242_40.toFinset :=
  node_ok cuts242 [⟨state242_39,exclude242_39⟩] 0xc24230200c08020908a08030200624228200624228200a08018908908030200501224200302024200908030908908028200302024200504220a02000030200828030108828020a00c24220a006042282008280 (by decide +kernel)

def state242_41 : List Sig := [0xffff0000ffff00003333000033330000ffff0000ffff0000333300000000,input 6,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_41 : Impossible true (goalAt 242) 3 state242_41.toFinset :=
  node_ok cuts242 [] 0x18108a08028200604228200c08018108a08030108c08030200602014108828020a00504220a00222028200828020a005042302008280 (by decide +kernel)

def state242_42 : List Sig := [0xffffffffffffffff3333333333333333ffffffffffffffff3333333300000000,input 6,input 5,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_42 : Impossible true (goalAt 242) 4 state242_42.toFinset :=
  node_ok cuts242 [⟨state242_41,exclude242_41⟩] 0x504224200908014108908028200302024200908030200504224202000020a00908020a00604228200a08018108a08030200604228200222020a00a08020a00c04230200c08018080501230108828020a002220 (by decide +kernel)

def state242_43 : List Sig := [0x3333333333333333333333333333333333333333000000003333333300000000,input 5,input 7,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_43 : Impossible true (goalAt 242) 5 state242_43.toFinset :=
  node_ok cuts242 [⟨state242_7,exclude242_7⟩,⟨state242_17,exclude242_17⟩,⟨state242_40,exclude242_40⟩,⟨state242_42,exclude242_42⟩] 0x30908602030908a02030200c08030908c08030200a02018080824214048908024200c08014108c08014048504214108c08024200908024848504214108c24224200908024848908024200c2421410850420c848908024200a0800c080a0800c84830200c080a08024200908018080a08028200c08018908c08018080624218908c08028200a08028080624218908c24228200a08028080a08028200c24218908624230200828020a00501280004501230202000330200501220a00828024200828020a00504280000504224202000224200504220a00828028080222030108c24220a00828028080828020a00c24208880c24228200828020a00624208880604228200222028200624220a008280 (by decide +kernel)

def state242_44 : List Sig := [0x3333333333333333333333333333333333333333000000003333333300000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_44 : Impossible true (goalAt 242) 5 state242_44.toFinset :=
  node_ok cuts242 [] 0x18080c08030200602014048c08030200501224200c08014108908014108908024200504224200a0800c080908014108908024200504230908a08030200602028200a02028201000818908828014048c08020a00828014108908020a00222020a00828008880828008880a08020a010000 (by decide +kernel)

def state242_45 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000,input 4,input 5,input 7,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_45 : Impossible true (goalAt 242) 5 state242_45.toFinset :=
  node_ok cuts242 [⟨state242_7,exclude242_7⟩] 0x602030200c08018080828030200501220a00222020a00828008880828028200222020a00828014100504220a00a08030200602028200a02028200a0800c848521230200524230200524234908921214908524228200321228200c08014848c08014848828080000828040000c24230908a02024848a08018908a0800c8489080 (by decide +kernel)

def state242_46 : List Sig := [0xffffffffffffffff0000000000000000ffffffff00000000,input 6,input 5,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_46 : Impossible true (goalAt 242) 5 state242_46.toFinset :=
  node_ok cuts242 [⟨state242_17,exclude242_17⟩] 0x524224200908014908908028200302024200908014908524224200828024200504220a00c24220a00828030108828028200604220a00828014040501220a00624228200a08018908a08018908624228200c24228080c24228080908014908908014908828080000828040000a02030908a02030908a08018908a08018908c080 (by decide +kernel)

def state242_47 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_47 : Impossible true (goalAt 242) 5 state242_47.toFinset :=
  node_ok cuts242 [⟨state242_35,exclude242_35⟩,⟨state242_12,exclude242_12⟩] 0x24200a0800c080908014908908024200524224200c0801490890800c080908024200302020a00908014108828020a00a08008880828030908828020a00c04220a00c08080004828008880828020a00222018908a08030202000028200a02028200a08040008a02030908c24240008c24230200c080209086020 (by decide +kernel)

def state242_48 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_48 : Impossible true (goalAt 242) 6 state242_48.toFinset :=
  node_ok cuts242 [⟨state242_36,exclude242_36⟩,⟨state242_8,exclude242_8⟩,⟨state242_18,exclude242_18⟩,⟨state242_22,exclude242_22⟩,⟨state242_26,exclude242_26⟩,⟨state242_29,exclude242_29⟩,⟨state242_33,exclude242_33⟩,⟨state242_43,exclude242_43⟩,⟨state242_44,exclude242_44⟩,⟨state242_45,exclude242_45⟩,⟨state242_46,exclude242_46⟩,⟨state242_47,exclude242_47⟩] 0x1000518080602028080c08030202000b30200c08028080602018082000a14848521240010c08030202000630200c0804001052121484852122420090803020052423020052121490852423020090802420100051490852422808090802420200052420090802808052421490900022420090802820030202820200040c080302028200908024202000914908524240004908024202000324200908040004524214908521220a00828030201000830200521280008501230200828020a00524220a00828024201000824200524280004504224200828020a01000508880222028080828020a01000820a00828028080222008881000220a00828028200222028201000808880222028200828020a01000880022000740000828020a01000820a00828040001000840001000240008c24218080a08028200c08040008c08018082000018080c08028200a08028081000528081000228200a080400090002400090002400146242 (by decide +kernel)

def state242_49 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff0000000000000000,input 5,input 6,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_49 : Impossible true (goalAt 242) 5 state242_49.toFinset :=
  node_ok cuts242 [⟨state242_11,exclude242_11⟩] 0x52422420090801490890803020052422420090800c080302024200828024200504220a00c24220a00828030108828030202000020a00828008880222020a00c24230200c08020908a02030908a0203090860203020060203020090800c08090800c080828008880828008880c24228080c24228080c08018080c08018080a080 (by decide +kernel)

def state242_50 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_50 : Impossible true (goalAt 242) 6 state242_50.toFinset :=
  node_ok cuts242 [⟨state242_13,exclude242_13⟩,⟨state242_33,exclude242_33⟩,⟨state242_37,exclude242_37⟩,⟨state242_47,exclude242_47⟩,⟨state242_49,exclude242_49⟩] 0x1000518908624230908a08028202000328200a08030908624218909000428200a08030200624230202000218908624230200a0802820200040c848321240008a08028202000128200a0804000832120c84832122420090802820030202820032120c08030202820090802420100051490852423090890802420100032420090803090852421490900042420090803020052423020100031490852423020090802420100030c08030204000490802420100032420090804000430200c080624220a00828028200222028200624208880604228200828020a00524220a0082802420100072420052424000c504224200828020a00c24208880c24230100828020a00c24220a00828030100222030109000420a00828030201000430201000740012000030200828020a01000708880222040000828020a01000720a00828040000222008881000440010a02030909000530909000430200c080400110004209090004400146020 (by decide +kernel)

def state242_51 : List Sig := roots 242
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_51 : Impossible true (goalAt 242) 7 state242_51.toFinset :=
  node_ok cuts242 [⟨state242_9,exclude242_9⟩,⟨state242_19,exclude242_19⟩,⟨state242_27,exclude242_27⟩,⟨state242_30,exclude242_30⟩,⟨state242_38,exclude242_38⟩,⟨state242_48,exclude242_48⟩,⟨state242_50,exclude242_50⟩] 0x40014c24218080c24240010a02030200c08080018c24230200c08040010a02018080824240014a02018908624240008c24228200a08080014a02028200a08040008c24218908624240010602028200a08040008c08018908c08080010602018908624240008c08028200a08040014921214908524240004c2422420090808000c921224200908040004c24214908524240010521224200908040004c08014908c0804000c521214908524240004c08024200908040008321224200908040004a0800c080a0808000832120c080302040004a08024200908040000c24208880c24240000c04020a00828040000c24220a00828040000c04008880c04240000521220a00828040000c08040000c08040000521280004501240000c08020a00828040000624220a00828040000a08008880a08040000624208880604240000a08020a00828040000524220a00828040000908040000908040000524280000504240000908020a008280 (by decide +kernel)

theorem lower242 : Claim 242 8 :=
  fromSearch 336920656 (by decide +kernel) exclude242_51

theorem lower195 : Claim 195 5 :=
  fromLift 5 2 118 lower193 (by decide +kernel)

theorem lower163 : Claim 163 5 :=
  fromLift 5 1 85 lower162 (by decide +kernel)

theorem lower99 : Claim 99 5 :=
  fromLift 5 2 85 lower97 (by decide +kernel)

def rule227_0 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower225 none (by decide +kernel)

def rule227_1 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower195 none (by decide +kernel)

def rule227_2 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower226 none (by decide +kernel)

def rule227_3 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower163 none (by decide +kernel)

def rule227_4 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower162 none (by decide +kernel)

def rule227_5 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower99 none (by decide +kernel)

def rule227_6 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower224 none (by decide +kernel)

def rule227_7 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower193 none (by decide +kernel)

def rule227_8 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower97 none (by decide +kernel)

def rule227_9 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower161 none (by decide +kernel)

def cuts227 : Cuts (goalAt 227) := [rule227_0,rule227_1,rule227_2,rule227_3,rule227_4,rule227_5,rule227_6,rule227_7,rule227_8,rule227_9]

def state227_0 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa,input 7,input 5,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_0 : Impossible true (goalAt 227) 4 state227_0.toFinset :=
  node_ok cuts227 [] 0x18080c08030200602010d08c08030201000420600c0801040c818020600a08008480818008480818020600212010d08818020601000028200c08018080a08028080a08028200210318508c142 (by decide +kernel)

def state227_1 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaa,input 7,input 5,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_1 : Impossible true (goalAt 227) 4 state227_1.toFinset :=
  node_ok cuts227 [] 0xc14230200c08020508818030200410320600818028200212020600c14220600818030108a08030200602028200e14228200a08030508602030200434230200414020600434220600434228200210328200a020 (by decide +kernel)

def state227_2 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_2 : Impossible true (goalAt 227) 4 state227_2.toFinset :=
  node_ok cuts227 [] 0x602030200c08018080410330200c0800840c828030200410320a00818020600434220a00212020a00828008480210320a00828040018a08030200434228200434228200a08010d08434228200a08010d08c242 (by decide +kernel)

def state227_3 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 5,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_3 : Impossible true (goalAt 227) 5 state227_3.toFinset :=
  node_ok cuts227 [⟨state227_0,exclude227_0⟩,⟨state227_1,exclude227_1⟩,⟨state227_2,exclude227_2⟩] 0xc24218080c24228080c08030200c24230200c08028080602020908c24208480c24230100828020a00c24220a00828030100212030108410320a00828030201000630200410340010410330200828020a00210320a00828040018212008480210308480212040018828020a00434220a00818040000212020600434208480434240000828020a00a0200840ca02030909000730908a02080008a0203090821033090860200840c602030201000730200602040010602030200210330201000240008a08028080434210d08c24280004c14228082000028080c24210d08434218081000418080c08010d08c08018080434210d08c08040010c080 (by decide +kernel)

def state227_4 : List Sig := [0xffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa,input 5,input 7,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_4 : Impossible true (goalAt 227) 4 state227_4.toFinset :=
  node_ok cuts227 [] 0x602030200c08018080818030200410320600212020600818008480818018100604220600602030200614230200614238508a02018508c08010d08c08018080818010d08818008480434230508810310d08a080 (by decide +kernel)

def state227_5 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_5 : Impossible true (goalAt 227) 4 state227_5.toFinset :=
  node_ok cuts227 [] 0x434230200c08018080410330200c0801040c818030200410320600434220600818008880818028200222020600810320600818040018434230508a02010d08a08030200602028200a02028200a08010d086242 (by decide +kernel)

def state227_6 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_6 : Impossible true (goalAt 227) 5 state227_6.toFinset :=
  node_ok cuts227 [⟨state227_0,exclude227_0⟩,⟨state227_4,exclude227_4⟩,⟨state227_5,exclude227_5⟩] 0x100081808060202040cc08030201000430200c0802040c602018080434218080434240010c08030200434230200c08040010602018080602028200a08030200624230200602018908624230200a0802820100081890862422040ca08028202000228200a0802040c62421890a000118908614210d08a08028202000028200a08010d08624210d08410320600818030201000630200410340010410330200818020600624220600818028200222028200624208880604228200818020600810308880222040018818020600810320600818040018222008880434208880434240000818020600434220600818040000222008881000240008c142 (by decide +kernel)

def state227_7 : List Sig := [0x1111111111111111111111111111111111111111000000001111111100000000,input 5,input 7,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_7 : Impossible true (goalAt 227) 4 state227_7.toFinset :=
  node_ok cuts227 [] 0xc24230200c08020908410330200434230200434230508810310d08434228200210328200a08030200624228200624228200a0801890882801040cc08020a00818030108828020a00c24220a006042282008280 (by decide +kernel)

def state227_8 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_8 : Impossible true (goalAt 227) 5 state227_8.toFinset :=
  node_ok cuts227 [⟨state227_0,exclude227_0⟩,⟨state227_2,exclude227_2⟩,⟨state227_5,exclude227_5⟩,⟨state227_7,exclude227_7⟩] 0x18080c0803020060201040cc0803020041031040cc08010d08c08020600434228082000210d0843422820200012820043424000a000010d08828030200410320a00222020a00828008880828028200222020a02000320a00828040018c24228200c08018080a08028080a0804001c6242 (by decide +kernel)

def state227_9 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_9 : Impossible true (goalAt 227) 6 state227_9.toFinset :=
  node_ok cuts227 [⟨state227_3,exclude227_3⟩,⟨state227_6,exclude227_6⟩,⟨state227_8,exclude227_8⟩] 0x40020c24218080c24240010a02030200c08040010c24230200c08040020a02018080824240020a0201890862424001cc24228200a08080008a02028200a0804001cc24218908624240010602028200a0804001cc08018908c0804001060201890862424001cc08028200a08040008810310d08434240008c24240008c14240008810380004810340008c24210d08434240008410340010410340008c08010d08c08040008410310d08434240008c08040008c08040008210310d08434240008a08040008a08040008210380000210340008a08010d08a08040001000040000818040018c24208880c24240018c04020a00828040018c24220a00828040018c04008880c04240018410320a00828040018c08040018c08040018410340010410340018c08020a00828040018624220a00828040018a08008880a08040018624208880604240018a08020a008280 (by decide +kernel)

def state227_10 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 5,input 7,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_10 : Impossible true (goalAt 227) 4 state227_10.toFinset :=
  node_ok cuts227 [] 0x20600828010d08818010d08818020600434220600a0800848081801040c818020601000620908828020a0022201040c828020a01000020c0ca08020a00604220a00604228200a080181082303 (by decide +kernel)

def state227_11 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff0000000000000000,input 5,input 7,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_11 : Impossible true (goalAt 227) 4 state227_11.toFinset :=
  node_ok cuts227 [] 0x818020a00434220600434220600818010d08818008480212020600824220a00828008880222020a00222020a00a02020908a02020908818008480818008480828008880828008880824228080824228080a080 (by decide +kernel)

def state227_12 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_12 : Impossible true (goalAt 227) 4 state227_12.toFinset :=
  node_ok cuts227 [] 0x818020a00434220600212020600818008480818028200212020600434220600818010d08222020a00828008880824220a00828040024a08020a00222020a00a02028200a0801040c6042280808242209084103 (by decide +kernel)

def state227_13 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_13 : Impossible true (goalAt 227) 5 state227_13.toFinset :=
  node_ok cuts227 [⟨state227_10,exclude227_10⟩,⟨state227_11,exclude227_11⟩,⟨state227_12,exclude227_12⟩] 0x222028200a08020a00604220a00222018108604220a00a08020a01000818108604220908a08028202000228200a0802090860421810a000108c0c23031040ca08028202000028200a0801040c230308900230320600818028200212028200230308480212028200818020601000420600818020a00434220a01000410d08434220a00818020601000810d08434220908818020601000420600818020908434210d08410308480212040018818020600410320600818040018212008480824208880824240024828020a00824220a00828040020222008880410308880222040000828020a00410320a0082804000022200888100034000ca020 (by decide +kernel)

def state227_14 : List Sig := [0xffffffffffffffffffffffff00000000,input 7,input 5,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_14 : Impossible true (goalAt 227) 4 state227_14.toFinset :=
  node_ok cuts227 [] 0x818020a00434220600818028200212020600434220600818010d08222020a00828008880a08020a00604220a00604228200a08018108434220600434220600222020a00222020a006042282006042282008242 (by decide +kernel)

def state227_15 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_15 : Impossible true (goalAt 227) 4 state227_15.toFinset :=
  node_ok cuts227 [] 0x818020a00434220600818028200434220600434220600818010d08434220600818010d08828028200222020a00222020a00828008880604220a00828040024a02028200a0801040c604228200a0801040ca242 (by decide +kernel)

def state227_16 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_16 : Impossible true (goalAt 227) 5 state227_16.toFinset :=
  node_ok cuts227 [⟨state227_10,exclude227_10⟩,⟨state227_14,exclude227_14⟩,⟨state227_15,exclude227_15⟩] 0x830310d08434230108818020600830320600818030108434210d09000420600818020a00434220a01000410d08434220a00818020601000720600818018108212018109000408480212018108818020600410320600818040018434210d08410310d08434240018818020600c04208880c04228080828020a00c04220a00828028080222008880410320a00828040000222030200410308880222040000828020a00a02018108604230109000728908a02080008a02030108604218108222040024222020a00604220a00222018108604220a01000720a0100034000ca0803010841033010883038000483033010a00002090883031040c8242 (by decide +kernel)

def state227_17 : List Sig := [0x333333333333333300000000000000003333333300000000,input 5,input 7,input 6,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_17 : Impossible true (goalAt 227) 4 state227_17.toFinset :=
  node_ok cuts227 [] 0x818010d08434220600434220600818010d08818028200212020600c04228080824220908a08018108604228200604228200a08018108818010d08818020a00c08008880828020a00c04220a006042282008280 (by decide +kernel)

def state227_18 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_18 : Impossible true (goalAt 227) 5 state227_18.toFinset :=
  node_ok cuts227 [⟨state227_15,exclude227_15⟩,⟨state227_10,exclude227_10⟩,⟨state227_12,exclude227_12⟩,⟨state227_17,exclude227_17⟩] 0x20600434210d08818020600828010d08818010d08818020600434220600a08008480818010d0881802060043423020041032808200022808041034000e00011040c222020a00828008882000320a00828040024c04228200410380000a08028200828008880828028080a0804001c6042 (by decide +kernel)

def state227_19 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 0,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_19 : Impossible true (goalAt 227) 6 state227_19.toFinset :=
  node_ok cuts227 [⟨state227_13,exclude227_13⟩,⟨state227_16,exclude227_16⟩,⟨state227_18,exclude227_18⟩] 0x40020a0201810860424001cc04228200a08080008a02028200a0804001cc0421810860424000d000328200a0804000c41031810860424000e00011810860424000c410328200a08040024222028200a0804001c82801810882804002422201810860424001c828028200828040020830310d08434240018c04220600818040010830320600818040018c04210d0843424001c230320600818040018a08008480a08040010230308480212040018a0802060081804000c41032060081804000d000610d0843424000c410310d0843424000d000320600818040011000420600818040018828010d08828040011000410d0843424001882802060081804000cc0421040cc0424000ca0204000ca0204000cc0428000082424000ca0201040c824240001000040000c08040020c04208880c04240024a02020a00828040024c04220a00828040020a020088802220 (by decide +kernel)

def state227_20 : List Sig := [0x3333333333333333333333333333333333333333222222223333333322222222,input 7,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_20 : Impossible true (goalAt 227) 4 state227_20.toFinset :=
  node_ok cuts227 [] 0x30908c08030200824228200c08018908a08018908a08028200624220600c08010d08818020600a08008480818010d08818020600434220a00410330200828020a00604228200828020600434220600828030108828020a00c242 (by decide +kernel)

def state227_21 : List Sig := [0xffffffffffffffff0000000000000000ffffffffaaaaaaaa,input 7,input 0,input 5,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_21 : Impossible true (goalAt 227) 4 state227_21.toFinset :=
  node_ok cuts227 [] 0x20a00a08018108828030908828020a00c04218908a08028200624220600828010d08818020600a08008480818010d08818020600434220a00410320a00c08028200624228200c08020600434220600c08020908c08030200c242 (by decide +kernel)

def state227_22 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa,input 7,input 0,input 5,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_22 : Impossible true (goalAt 227) 5 state227_22.toFinset :=
  node_ok cuts227 [⟨state227_0,exclude227_0⟩,⟨state227_20,exclude227_20⟩,⟨state227_21,exclude227_21⟩] 0x602030200c08018082000230200c0804000c828030200410320a00828028200222020a00222020a00828008882000120a00828040000a08030200602028200a02028200a08008c0c624220600c08010c0c818020600828080000818020600a08008480818008480818020600212010d08c242 (by decide +kernel)

def state227_23 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaa,input 7,input 0,input 5,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_23 : Impossible true (goalAt 227) 5 state227_23.toFinset :=
  node_ok cuts227 [⟨state227_1,exclude227_1⟩] 0xc24230200c08020908828030200410320a00828028200222020a00c24220a00828030108a08030200602028200e24228200a08030908818030200430320600818020a02000020600818028200212020600c34220600818030908602030200602030200222020a00222020a00624228200230328200434220600212020600a020 (by decide +kernel)

def state227_24 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_24 : Impossible true (goalAt 227) 4 state227_24.toFinset :=
  node_ok cuts227 [] 0x18080c08030200212010c0cc08030200230320a00c0801040c828020a00818008880818008880828020a00212008c0c828020a00210320600c08018080818010d08818020601000118908818020600820330908c242084802203 (by decide +kernel)

def state227_25 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 5,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_25 : Impossible true (goalAt 227) 5 state227_25.toFinset :=
  node_ok cuts227 [⟨state227_24,exclude227_24⟩] 0x18080c08030200602018080c08030200212020a00c0801040c828020a00222008880828020a00818008880818008880828020a00222008880828020a00212018080c08018080c08028200230320c0e000008c0c212008c0c21200880c81803020060202060083032060081802080c434220600818040004c242 (by decide +kernel)

def state227_26 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_26 : Impossible true (goalAt 227) 5 state227_26.toFinset :=
  node_ok cuts227 [⟨state227_24,exclude227_24⟩,⟨state227_2,exclude227_2⟩] 0x18080c08030200602010c0cc08030200230320a00c0801040c828020a00a08008880828008880828020a00222008c0c828020a00210308480c08010c0cc0800848082808000482802060021202048200000848023030848021200880ca08030200602028200a02028200a08040014624228200a08040008c242 (by decide +kernel)

def state227_27 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 5,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_27 : Impossible true (goalAt 227) 6 state227_27.toFinset :=
  node_ok cuts227 [⟨state227_3,exclude227_3⟩,⟨state227_22,exclude227_22⟩,⟨state227_23,exclude227_23⟩,⟨state227_25,exclude227_25⟩,⟨state227_26,exclude227_26⟩] 0xc24218080c24228080c08030200c24230200c08028080602020908c24208880c24230100828020a00c24220a00828030100222030108430320a00828030201000630200430340010410330200828020a00230320a00828008404222008880230308880222008404828020a01000620a00828040000222008881000608880222040000828020a00a02008c0ca02030909000130908a02080010a02030908230330908602008c0c602030201000130200602040010602030200230330201000140008a08020c0c212008480c24240008c24220c0e000320c0cc24208480c24210c0c212008480c08040008c08010c0d000410c0cc08008480c08040008212008480828040008828040009000680000828008480828008c0d000108c0d00020848021204000500010880d000140004818028081000528080c24280008c24228082000128080c24240014c24218081000318080c08040010c08018081000418080c0804000cc080 (by decide +kernel)

def state227_28 : List Sig := [0xffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa,input 5,input 0,input 7,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_28 : Impossible true (goalAt 227) 5 state227_28.toFinset :=
  node_ok cuts227 [⟨state227_4,exclude227_4⟩] 0x602030200c08018080828030200410320a00222020a00828008880828018100604220a00818030200430320600818020a02000020600212020600818008480818018908212020600602030200624230200624238908a02018908c08018080c08018080828008880828008880c24230908830328080818010d08818008480a080 (by decide +kernel)

def state227_29 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_29 : Impossible true (goalAt 227) 5 state227_29.toFinset :=
  node_ok cuts227 [⟨state227_24,exclude227_24⟩,⟨state227_5,exclude227_5⟩] 0x18080c08030200602010c0cc08030200430320a00c0801040c828008880828020a00222020a00a08008880828020c0c828020a00810320600c08010c0c818020600828080004818010d0881802820200002060083032060081802080cc24230908a02040004a08030200602028200a02028200a080400046242 (by decide +kernel)

def state227_30 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_30 : Impossible true (goalAt 227) 6 state227_30.toFinset :=
  node_ok cuts227 [⟨state227_6,exclude227_6⟩,⟨state227_25,exclude227_25⟩,⟨state227_22,exclude227_22⟩,⟨state227_28,exclude227_28⟩,⟨state227_29,exclude227_29⟩] 0x1000518080602020c0cc08030201000430200c08020c0c60201808100041808060204000cc08030201000430200c0804000c602018080602028200a08030200624230200602018908624230200a08028201000518908624220c0ca08028202000428200a08020c0c62421890a000318908624240004a08028202000228200a08040004624218908430320a00828030201000630200430340010410330200828020a00624220a00828028200222028200624208880604228200828020a00830308880222020404828020a00830320a00828020404222008881000608880222040000828020a01000620a00828040000222008881000240008c24210c0c818020600c08040008c08010c0d000410c0cc08020600818008c0c818020600a08040008a08008c0e000108c0ca08020600818040008818020600828040008828040009000680000828020600818020c0d000520c0d00022060081804000900022080d0002400144342 (by decide +kernel)

def state227_31 : List Sig := [0x5555555555555555555555555555555555555555555555555555555500000000,input 7,input 5,input 6,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_31 : Impossible true (goalAt 227) 4 state227_31.toFinset :=
  node_ok cuts227 [] 0x20a00c0801040c828020a00a08018108828030908828020a00c04230908c08030200824228200c08018908a08018908a08028200624220600434220a00818020600434230200818020600212028200818010d088180206004342 (by decide +kernel)

def state227_32 : List Sig := [0x3333333333333333333333333333333333333333333333333333333300000000,input 7,input 5,input 6,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_32 : Impossible true (goalAt 227) 4 state227_32.toFinset :=
  node_ok cuts227 [] 0x20600c08010d08818020600a08008480818010d08818020600434230908c08030200824228200c08018908a08018908a08028200624220600434220600828020a00410330200828020a00604228200828030108828020a00c242 (by decide +kernel)

def state227_33 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 7,input 5,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_33 : Impossible true (goalAt 227) 5 state227_33.toFinset :=
  node_ok cuts227 [⟨state227_10,exclude227_10⟩,⟨state227_31,exclude227_31⟩,⟨state227_32,exclude227_32⟩] 0x828030202000020a00828028200604220a00c24220a0082803010a000220a00828040000818020a00434220600818030200434220600818028200212020600434220600818010d0a000120600818040008c24230200c08020908430328200c08018908a08018908a08028200624208c0c8303 (by decide +kernel)

def state227_34 : List Sig := [0xffffffffffffffffffffffff00000000,input 7,input 5,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_34 : Impossible true (goalAt 227) 5 state227_34.toFinset :=
  node_ok cuts227 [⟨state227_14,exclude227_14⟩] 0x828030202000020a00828028200604220a00222020a00828008880818020a00434220600818030200434220600818028200212020600434220600818010d08602030200c08018080a08030200624228200624228200a08018908222020a00222020a00434220600434220600602030200602030200624228200624228200c242 (by decide +kernel)

def state227_35 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_35 : Impossible true (goalAt 227) 4 state227_35.toFinset :=
  node_ok cuts227 [] 0x20a00a08008880828018908828020a00604208880828020a00222020600828010d08818020600a08010d08818010d08818020600434208480818020600212018908a08028200824218080a080282010001180806242189082242 (by decide +kernel)

def state227_36 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_36 : Impossible true (goalAt 227) 5 state227_36.toFinset :=
  node_ok cuts227 [⟨state227_15,exclude227_15⟩,⟨state227_35,exclude227_35⟩] 0x20a00602080000828020a00a08008880828008880828020a00222018908828020a00604220600828010d08818020600434210d08818020600a08010d08818010d08818020600434210d08818020600434230200602028082000118080624218080624208908a02028200a08040014624228200a0804000cc242 (by decide +kernel)

def state227_37 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_37 : Impossible true (goalAt 227) 5 state227_37.toFinset :=
  node_ok cuts227 [⟨state227_35,exclude227_35⟩] 0x20a00604018108828020a00c08008880828030908828020a00c04208880828020a00222020600828010d08818020600624208480818020600c08010d08818010d0881802060043420848081802060021202820062422890a000018908602018908624208908c24230200c08020908602030200c08040004a020 (by decide +kernel)

def state227_38 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_38 : Impossible true (goalAt 227) 6 state227_38.toFinset :=
  node_ok cuts227 [⟨state227_16,exclude227_16⟩,⟨state227_33,exclude227_33⟩,⟨state227_34,exclude227_34⟩,⟨state227_36,exclude227_36⟩,⟨state227_37,exclude227_37⟩] 0xc24208880c24230100828020a00c24220a00828030100222030109000320a0082801808100031808100074000e000018080828020a00624220a00828018100222018100624208880604218100828020a01000720a00828040000222008881000708880222040000828020a00830310d08434230908818020600830320600818030908434210d09000720600818020a00434220a01000410d08434220a00818020601000320600818018080434210d09000410d08434218080818020601000120600818018908212018909000408480212018908818020601000420600818040008434210d09000410d08434240008818020600c24218080c24228081000328080c24280010c24228080602018081000140004c08028080624218908c24240004c24228082000328080c2421890862421808100031808100011890862424000500010890900014000ca0803090900053090883038000883033090a0001309088303400148303 (by decide +kernel)

def state227_39 : List Sig := [0xbbbbbbbbbbbbbbbb0000000000000000bbbbbbbbaaaaaaaa,input 0,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_39 : Impossible true (goalAt 227) 3 state227_39.toFinset :=
  node_ok cuts227 [] 0x18108a08028200604210d08818020600434220600a08008480818008880828020a00824220a006042282008280206004342206008280 (by decide +kernel)

def state227_40 : List Sig := [0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaaaaaabbbbbbbbaaaaaaaa,input 0,input 5,input 7,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_40 : Impossible true (goalAt 227) 4 state227_40.toFinset :=
  node_ok cuts227 [⟨state227_39,exclude227_39⟩] 0xc24230200c08020908a08030200624228200624228200a08018908818030200410320600212020600818030908818028200212020600434220a02000030200828030108828020a00c24220a006042282008280 (by decide +kernel)

def state227_41 : List Sig := [0x5555555555555555111111111111111155555555555555551111111100000000,input 6,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_41 : Impossible true (goalAt 227) 3 state227_41.toFinset :=
  node_ok cuts227 [] 0x18108a08028200604228200c08018108a08030108c08030200602010d088180206004342206002120282008180206004342302008180 (by decide +kernel)

def state227_42 : List Sig := [0xffffffffffffffff3333333333333333ffffffffffffffff3333333300000000,input 6,input 5,input 7,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_42 : Impossible true (goalAt 227) 4 state227_42.toFinset :=
  node_ok cuts227 [⟨state227_41,exclude227_41⟩] 0x434220600818010d08818028200212020600818030200434220602000020600818020a00604228200a08018108a08030200604228200222020a00a08020a00c04230200c08018080410330108828020a002220 (by decide +kernel)

def state227_43 : List Sig := [0x3333333333333333333333333333333333333333000000003333333300000000,input 5,input 7,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_43 : Impossible true (goalAt 227) 5 state227_43.toFinset :=
  node_ok cuts227 [⟨state227_7,exclude227_7⟩,⟨state227_17,exclude227_17⟩,⟨state227_40,exclude227_40⟩,⟨state227_42,exclude227_42⟩] 0x30908602030908a02030200c08030908c08030200a0201808082421040c818020600c08010d08c0801040c434210d08c08020600818020c0c434210d08c24220600818020c0c818020600c24210d08434208c0c818020600a08008480a08008c0c212008480a08020600818018080a08028200c08018908c08018080624218908c08028200a08028080624218908c24228200a08028080a08028200c24218908624230200828020a00410380004410330202000330200410320a00828020600828020600434280000434220602000220600434220a00828028080222030108c24220a00828028080828020a00c24208880c24228200828020a00624208880604228200222028200624220a008280 (by decide +kernel)

def state227_44 : List Sig := [0x5555555555555555555555555555555555555555000000005555555500000000,input 0,input 5,input 7,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_44 : Impossible true (goalAt 227) 5 state227_44.toFinset :=
  node_ok cuts227 [⟨state227_7,exclude227_7⟩] 0x602030200c08018080828030200410320a00222020a00828008880828028200222020a00a08030200602028200a02028200a08008c0c430330200434230200414020a00434220a00434230d08830310d08434228200230328200c08010c0cc08010c0c828080000828040000c24230908a02020c0ca08018908a08008c0c8180 (by decide +kernel)

def state227_45 : List Sig := [0x3333333333333333333333333333333333333333000000003333333300000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_45 : Impossible true (goalAt 227) 5 state227_45.toFinset :=
  node_ok cuts227 [] 0x18080c0803020060201040cc08030200410320600c08010d08818010d08818020600434220600a08008480818010d08818020600434230908a08030200602028200a0202820100071890882801040cc08020a00818010d08818020a00222020a00828008880828008880a08020a010000 (by decide +kernel)

def state227_46 : List Sig := [0xffffffffffffffff0000000000000000ffffffff00000000,input 6,input 5,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_46 : Impossible true (goalAt 227) 5 state227_46.toFinset :=
  node_ok cuts227 [⟨state227_17,exclude227_17⟩] 0xc24220a00828030108828028200604220a00828010404410320a00818020a00434220600434220600818010d08818028200212020600818010d08434220600624228200a08018908a08018908624228200c24228080c24228080828080000828040000818010d08818010d08a02030908a02030908a08018908a08018908c080 (by decide +kernel)

def state227_47 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_47 : Impossible true (goalAt 227) 5 state227_47.toFinset :=
  node_ok cuts227 [⟨state227_35,exclude227_35⟩,⟨state227_12,exclude227_12⟩] 0x20a00a08008880828030908828020a00c04220a00c08080004828008880828020a00222020600828010d08818020600a08008480818010d08818020600434220600c08010d08818008480818020600212018908a08030202000028200a02028200a08040004a02030908c24240004c24230200c080209086020 (by decide +kernel)

def state227_48 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_48 : Impossible true (goalAt 227) 6 state227_48.toFinset :=
  node_ok cuts227 [⟨state227_36,exclude227_36⟩,⟨state227_22,exclude227_22⟩,⟨state227_26,exclude227_26⟩,⟨state227_29,exclude227_29⟩,⟨state227_8,exclude227_8⟩,⟨state227_18,exclude227_18⟩,⟨state227_33,exclude227_33⟩,⟨state227_43,exclude227_43⟩,⟨state227_44,exclude227_44⟩,⟨state227_45,exclude227_45⟩,⟨state227_46,exclude227_46⟩,⟨state227_47,exclude227_47⟩] 0x1000518080602028080c08030202000b30200c08028080602018082000a10c0c43034000cc08030202000630200c0804000c430310c0c430320a00828030201000730200430380014410330200828020a01000508880222028080828020a01000720a00828028080222008881000120a00828028200222028201000708880222028200828020a01000780026000740000828020a01000720a00828040001000740000430320600818030200434230200430310d08434230200818020601000720600818020a00434220a02000410d08434220a00818020601000510d08434228080818020602000320600818028080434210d09000120600818028200212028202000208480212028200818020602000810d08434240008818020602000120600818040008434210d09000140004c24218080a08028200c08040004c08018082000018080c08028200a08028081000528081000128200a080400050001400050001400146242 (by decide +kernel)

def state227_49 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff0000000000000000,input 5,input 6,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_49 : Impossible true (goalAt 227) 5 state227_49.toFinset :=
  node_ok cuts227 [⟨state227_11,exclude227_11⟩] 0xc24220a00828030108828030202000020a00828008880222020a00818020a00434220600434220600818010d08818030200434220600818008480212020600c24230200c08020908a02030908a02030908602030200602030200828008880828008880818008480818008480c24228080c24228080c08018080c08018080a080 (by decide +kernel)

def state227_50 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_50 : Impossible true (goalAt 227) 6 state227_50.toFinset :=
  node_ok cuts227 [⟨state227_13,exclude227_13⟩,⟨state227_33,exclude227_33⟩,⟨state227_37,exclude227_37⟩,⟨state227_47,exclude227_47⟩,⟨state227_49,exclude227_49⟩] 0x1000518908624230908a08028202000328200a08030908624218909000328200a08030200624230202000218908624230200a08028202000408c0c230340004a08028202000128200a08040004230308c0c624220a00828028200222028200624208880604228200828020a00c24208880c24230100828020a00c24220a00828030100222030109000320a0082803020100033020100084000e000030200828020a01000808880222040000828020a01000820a00828040000222008880230320600818028200212028200230308480212028200818020601000820600818020a00434220a01000410d08434220a00818020601000510d08434230908818020601000420600818030908434210d09000320600818030200434230201000410d0843423020081802060100040848021204000881802060100042060081804000821200848100034000ca02030909000530909000330200c0804000d0003209090003400146020 (by decide +kernel)

def state227_51 : List Sig := roots 227
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_51 : Impossible true (goalAt 227) 7 state227_51.toFinset :=
  node_ok cuts227 [⟨state227_9,exclude227_9⟩,⟨state227_19,exclude227_19⟩,⟨state227_27,exclude227_27⟩,⟨state227_30,exclude227_30⟩,⟨state227_38,exclude227_38⟩,⟨state227_48,exclude227_48⟩,⟨state227_50,exclude227_50⟩] 0x40014c24218080c2424000ca02030200c08080018c24230200c0804000ca02018080824240014a02018908624240004c24228200a08080014a02028200a08040004c2421890862424000c602028200a08040004c08018908c08080010602018908624240004c08028200a08040000c24208880c24240000c04020a00828040000c24220a00828040000c04008880c04240000430320a00828040000c08040000c08040000430380004410340000c08020a00828040000624220a00828040000a08008880a08040000624208880604240000a08020a00828040014830310d08434240008c2422060081808000c830320600818040008c24210d0843424000c430320600818040008c08010d08c08040010430310d0843424000cc08020600818040004230320600818040008a08008480a08080008230308480212040004a08020600818040001000020600818040000828010d08828040002000010d084342400008280206008180 (by decide +kernel)

theorem lower227 : Claim 227 8 :=
  fromSearch 85 (by decide +kernel) exclude227_51

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

theorem lower147 : Claim 147 5 :=
  fromLift 5 2 116 lower145 (by decide +kernel)

def cuts49 : Cuts (goalAt 49) := []

def state49_0 : List Sig := roots 49
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude49_0 : Impossible true (goalAt 49) 3 state49_0.toFinset :=
  node_ok cuts49 [] 0xc04011010c04021010c08030200c04030200c0802101044041101084041110044403010084802120084042120084803010044401110044042120084803020044403020044041110044403020084802120 (by decide +kernel)

theorem lower49 : Claim 49 4 :=
  fromSearch 4 (by decide +kernel) exclude49_0

theorem lower51 : Claim 51 5 :=
  fromLift 5 2 84 lower49 (by decide +kernel)

def rule179_0 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower177 none (by decide +kernel)

def rule179_1 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower163 none (by decide +kernel)

def rule179_2 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower162 none (by decide +kernel)

def rule179_3 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower178 none (by decide +kernel)

def rule179_4 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower147 none (by decide +kernel)

def rule179_5 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower51 none (by decide +kernel)

def rule179_6 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower176 none (by decide +kernel)

def rule179_7 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower49 none (by decide +kernel)

def rule179_8 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower145 none (by decide +kernel)

def rule179_9 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower161 none (by decide +kernel)

def cuts179 : Cuts (goalAt 179) := [rule179_0,rule179_1,rule179_2,rule179_3,rule179_4,rule179_5,rule179_6,rule179_7,rule179_8,rule179_9]

def state179_0 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa,input 7,input 5,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_0 : Impossible true (goalAt 179) 4 state179_0.toFinset :=
  node_ok cuts179 [] 0x24200a0800c08090800c080908024200302004c4890802420100022060090800440c818020600a08008480818008480818020600212004c48818020601000028080a0802820021030c4489112 (by decide +kernel)

def state179_1 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaa,input 7,input 5,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_1 : Impossible true (goalAt 179) 4 state179_1.toFinset :=
  node_ok cuts179 [] 0x90802820030202420030202420090800c080818024200110320600818028200212020600212020600818008480b11228200a08024448302024200302024200212020600212020600131228200210328200a020 (by decide +kernel)

def state179_2 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_2 : Impossible true (goalAt 179) 4 state179_2.toFinset :=
  node_ok cuts179 [] 0x90802820030202420030202420090800c08011032420090800440c828024200110320a00818020600212020a00212020a00828008480210320a00828040018a02028200a08004c48131228200a08004c489212 (by decide +kernel)

def state179_3 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 5,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_3 : Impossible true (goalAt 179) 5 state179_3.toFinset :=
  node_ok cuts179 [⟨state179_0,exclude179_0⟩,⟨state179_1,exclude179_1⟩,⟨state179_2,exclude179_2⟩] 0x92120c08030202808090802420092122420090802808030200c08100022420090800840c30200c08100020c08030200840c90802420013122420090804000830200c08013120c080302040008908024200921208480212028080828020a00921220a00828028080212008480110320a00828024201000624200110340008110324200828020a00210320a00828040018212008480210308480212040018828020a00131220a00818040000212020600131208480212040000828020a00a0200840ca02024849000824848a02080008a0202484821032484900034000ca08028080131228080921280004911228082000028080921204c481312 (by decide +kernel)

def state179_4 : List Sig := [0xffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa,input 5,input 7,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_4 : Impossible true (goalAt 179) 4 state179_4.toFinset :=
  node_ok cuts179 [] 0x30202420090800c08090800c080302024200818024200110320600212020600818008480818008480212020600a0202c448a0200c44890800c08090800c080818008480818008480131228080810328080a080 (by decide +kernel)

def state179_5 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_5 : Impossible true (goalAt 179) 4 state179_5.toFinset :=
  node_ok cuts179 [] 0x30202420090800c08090802820030202420011032420090800440c818024200110320600212020600818008880818028200222020600810320600818040018131228080a02004c48a02028200a08004c483212 (by decide +kernel)

def state179_6 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_6 : Impossible true (goalAt 179) 5 state179_6.toFinset :=
  node_ok cuts179 [⟨state179_0,exclude179_0⟩,⟨state179_4,exclude179_4⟩,⟨state179_5,exclude179_5⟩] 0x100070c84832122040ca08028202000228200a0802040c32120c84a00010c848311204c48a08028202000028200a08004c48321204c4832122420090802820030202820032120c08030202820090802420100020c08030202040c90802420100022420090802040c30200c08013120c08030204000890802420013122420090804000830200c08032122060081802820022202820032120888022202820081802060011032060081802420100062420011034000811032420081802060081030888022204001881802060081032060081804001822200888013120888021204000081802060013122060081804000022200888100034000ca020 (by decide +kernel)

def state179_7 : List Sig := [0x1111111111111111111111111111111111111111000000001111111100000000,input 5,input 7,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_7 : Impossible true (goalAt 179) 4 state179_7.toFinset :=
  node_ok cuts179 [] 0x30202420090800c080908028200302024200110324200131224200131228080810328080131228200210328200a02028200a0800c84882800440c908020a00818008880828020a00222020a002220282008280 (by decide +kernel)

def state179_8 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_8 : Impossible true (goalAt 179) 5 state179_8.toFinset :=
  node_ok cuts179 [⟨state179_0,exclude179_0⟩,⟨state179_2,exclude179_2⟩,⟨state179_5,exclude179_5⟩,⟨state179_7,exclude179_7⟩] 0xc080908024200302024200a0800c08090800440c90802420011030440c908004c4890802060013122808200022808013122820200012820013124000e000004c48828024200110320a00222020a00828008880828028200222020a02000320a00828040018921228080a0804001c3212 (by decide +kernel)

def state179_9 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_9 : Impossible true (goalAt 179) 6 state179_9.toFinset :=
  node_ok cuts179 [⟨state179_3,exclude179_3⟩,⟨state179_6,exclude179_6⟩,⟨state179_8,exclude179_8⟩] 0x4001ca0200c848a02040020921228200a08080008a02028200a0804001c92120c84832124000892120c080302040008a02024200908040008921224200908040008a0200c080302040008321224200908040008a0800c080a0804000832120c080302040008a0802420090804000c810304c4813124000ca0204000ca0204000c81038000481034000ca02004c48a0204000c210304c4813124000ca0804000ca0804000c21038000021034000ca08004c48a0804000c11034000811034000c908004c4890804000c110304c4813124000c90804000c908040001000040000818040018921208880222040018a02020a00828040018921220a00828040018a02008880222040018321220a00828040018a08008880a08040018321208880222040018a08020a00828040018110320a00828040018908040018908040018110340008110340018908020a008280 (by decide +kernel)

def state179_10 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 7,input 5,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_10 : Impossible true (goalAt 179) 4 state179_10.toFinset :=
  node_ok cuts179 [] 0x20600828004c48818020600a0800848081800848081802060021200440c818020601000620a00a08008880828008880828020a0022200440c828020a01000028080a08028200221208c0c8303 (by decide +kernel)

def state179_11 : List Sig := [0xffffffffffff0000ffffffffffff0000,input 7,input 5,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_11 : Impossible true (goalAt 179) 4 state179_11.toFinset :=
  node_ok cuts179 [] 0x818020a00131220600818028200212020600212020600818008480828028200222020a00222020a00828008880221228200a08008848212020600212020600222020a00222020a00221228200221228200a020 (by decide +kernel)

def state179_12 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_12 : Impossible true (goalAt 179) 4 state179_12.toFinset :=
  node_ok cuts179 [] 0x818020a00131220600818028200212020600212020600818008480131220600818004c48828024200222020a00222020a00828008880221220a00828040024a02028200a0800440c221228200a0800440c9012 (by decide +kernel)

def state179_13 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_13 : Impossible true (goalAt 179) 5 state179_13.toFinset :=
  node_ok cuts179 [⟨state179_10,exclude179_10⟩,⟨state179_11,exclude179_11⟩,⟨state179_12,exclude179_12⟩] 0x830308480212028080818020600830320600818028080212008481000220600818020a00131220a01000204c48131220a00818020601000220600818008848212008481000208480212008848818020600110320600818040018212008480110308480212040018818020600901208880222028080828020a00901220a00828028080222008880221220a00828040024222008880221208880222040024828020a00110320a00828040000222024200110308880222040000828020a00a02008848a02024049000824048a02080008a02024048221208849000140004a0802808011032808083038000483032808200002808083030440c8212 (by decide +kernel)

def state179_14 : List Sig := [0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,input 5,input 7,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_14 : Impossible true (goalAt 179) 4 state179_14.toFinset :=
  node_ok cuts179 [] 0x818020a00131220600212020600818008480818008480212020600222020a00828008880828008880222020a00a02020848a02020848818008480818008480828008880828008880821228080821228080a080 (by decide +kernel)

def state179_15 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_15 : Impossible true (goalAt 179) 4 state179_15.toFinset :=
  node_ok cuts179 [] 0x818020a00131220600212020600818008480818028200212020600131220600818004c48222020a00828008880828028200222020a00821220a00828040024821228080a0200440ca02028200a0800440c3012 (by decide +kernel)

def state179_16 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_16 : Impossible true (goalAt 179) 5 state179_16.toFinset :=
  node_ok cuts179 [⟨state179_10,exclude179_10⟩,⟨state179_14,exclude179_14⟩,⟨state179_15,exclude179_15⟩] 0x100070c048301220848a08028202000228200a0802084830120c04a000108c0c23030440ca08028202000028200a0800440c230308848230320600818028200212028200230308480212028200818020601000220600818020a00131220a01000204c48131220a00818020601000208480212020848818020601000220600818020848212008480110308480212040018818020600110320600818040018212008480301220a00828028200222028200301208880222028200828020a00821208880222040024828020a00821220a00828040024222008880110308880222040000828020a00110320a00828040000222008881000140004a020 (by decide +kernel)

def state179_17 : List Sig := [0x333300003333000033330000333300003333000000000000333300000000,input 5,input 7,input 4,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_17 : Impossible true (goalAt 179) 4 state179_17.toFinset :=
  node_ok cuts179 [] 0x818004c48131220600212020600818008480818028200212020600901228080821228080301228200221228200a02028200a0800c048818004c48818020a00908008880828020a00222020a002220282008280 (by decide +kernel)

def state179_18 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 4,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_18 : Impossible true (goalAt 179) 5 state179_18.toFinset :=
  node_ok cuts179 [⟨state179_10,exclude179_10⟩,⟨state179_12,exclude179_12⟩,⟨state179_15,exclude179_15⟩,⟨state179_17,exclude179_17⟩] 0x20600131204c48818020600828004c48818008480818020600212020600a08008480818004c4881802060013122420011032808200022808011032820200012820011034000600000440c222020a00828008880828028200222020a02000320a00828040024901228080a0804001c3012 (by decide +kernel)

def state179_19 : List Sig := [0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 4,input 0,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_19 : Impossible true (goalAt 179) 6 state179_19.toFinset :=
  node_ok cuts179 [⟨state179_13,exclude179_13⟩,⟨state179_16,exclude179_16⟩,⟨state179_18,exclude179_18⟩] 0x4001ca0200c048a02040020901228200a08080008a02028200a0804001c90120c048301240008830308480212040018a02020600818040008830320600818040018a02008480212040008230320600818040018a08008480a08040008230308480212040018a08020600818040004110320600818040005000604c48131240004110304c48131240005000120600818040009000220600818040018828004c48828040009000204c4813124001882802060081804000490120440c901240004a02040004a02040004901280004821240004a0200440ca0204000430120440c301240004a08040004a08040004301280000221240004a0800440ca08040001000040000908040024901208880222040024a02020a00828040024901220a00828040024a02008880222040024301220a00828040024a08008880a08040024301208880222040024a08020a008280 (by decide +kernel)

def state179_20 : List Sig := [0x3333333333333333333333333333333333333333222222223333333322222222,input 7,input 0,input 5,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_20 : Impossible true (goalAt 179) 4 state179_20.toFinset :=
  node_ok cuts179 [] 0x24200a0800c08090800c080908024200302028080a08028200321220600908004c48818020600a08008480818008480818020600212020a00110324200828020a00222028200828020600131220600828008880828020a002220 (by decide +kernel)

def state179_21 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000ffff0000aaaa,input 7,input 0,input 5,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_21 : Impossible true (goalAt 179) 4 state179_21.toFinset :=
  node_ok cuts179 [] 0x20a00a08008880828008880828020a00222028080a08028200321220600828004c48818020600a08008480818008480818020600212020a00110320a0090802420030202820090802060013122060090800c0809080242003020 (by decide +kernel)

def state179_22 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa,input 7,input 0,input 5,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_22 : Impossible true (goalAt 179) 5 state179_22.toFinset :=
  node_ok cuts179 [⟨state179_0,exclude179_0⟩,⟨state179_20,exclude179_20⟩,⟨state179_21,exclude179_21⟩] 0x90802820030202420030202420090800c082000224200908040004828024200110320a00828028200222020a00222020a00828008882000120a00828040000a02028200a08008c0c321220600908004c0c818020600828080000818020600a08008480818008480818020600212004c489212 (by decide +kernel)

def state179_23 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaa,input 7,input 0,input 5,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_23 : Impossible true (goalAt 179) 5 state179_23.toFinset :=
  node_ok cuts179 [⟨state179_1,exclude179_1⟩] 0x90802820030202420030202420090800c080828024200110320a00828028200222020a00222020a00828008880b21228200a08024848818024200130320600818020a02000020600818028200212020600212020600818008480302024200302024200222020a00222020a00321228200230328200212020600212020600a020 (by decide +kernel)

def state179_24 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_24 : Impossible true (goalAt 179) 4 state179_24.toFinset :=
  node_ok cuts179 [] 0x2420081800c08081800c080908024200212004c0c908024200130320a0090800440c828020a00818008880818008880828020a00212008c0c828020a0021030848081802060100040c8488180206008203248482120084802203 (by decide +kernel)

def state179_25 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 5,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_25 : Impossible true (goalAt 179) 5 state179_25.toFinset :=
  node_ok cuts179 [⟨state179_24,exclude179_24⟩] 0x2420030200c08090802420081800c08081800c08090802420030200c080908024200212020a0090800440c828020a00222008880828020a00818008880818008880828020a00222008880828020a00212028200230320c0e000008c0c212008c0c21200880c83032060081802080c212020600818040010a020 (by decide +kernel)

def state179_26 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_26 : Impossible true (goalAt 179) 5 state179_26.toFinset :=
  node_ok cuts179 [⟨state179_24,exclude179_24⟩,⟨state179_2,exclude179_2⟩] 0x24200a0800c08090800c080908024200302004c0c908024200130320a0090800440c828020a00a08008880828008880828020a00222008c0c828020a00210308480908004c0c90800848082808000482802060021202048200000848023030848021200880ca02028200a08040014321228200a0804000c9212 (by decide +kernel)

def state179_27 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 5,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_27 : Impossible true (goalAt 179) 6 state179_27.toFinset :=
  node_ok cuts179 [⟨state179_3,exclude179_3⟩,⟨state179_22,exclude179_22⟩,⟨state179_23,exclude179_23⟩,⟨state179_25,exclude179_25⟩,⟨state179_26,exclude179_26⟩] 0x92120c08030202808090802420092122420090802808030200c081000424200908008c0c30200c08100020c080302008c0c90802420100022420090804000430200c08100020c080302040004908024200921208880222028080828020a00921220a00828028080222008880130320a00828024201000624200130340008110324200828020a00230320a00828008404222008880230308880222008404828020a01000620a00828040000222008881000608880222040000828020a00a02008c0ca02024849000424848a02080010a0202484823032484900044000ca08020c0c212008480a0204000ca02020c0e000320c0ca02008480212004c0c21200848090804000c908004c0d000204c0c90800848090804000c21200848082804000c82804000d000680000828008480828008c0d000408c0d00030848021204001100040880d0004400108180280810005280809212800089212280820001280809212400149212 (by decide +kernel)

def state179_28 : List Sig := [0xffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa,input 5,input 0,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_28 : Impossible true (goalAt 179) 5 state179_28.toFinset :=
  node_ok cuts179 [⟨state179_4,exclude179_4⟩] 0x30202420090800c08090800c080302024200828024200110320a00222020a00828008880828008880222020a00818024200130320600818020a02000020600212020600818008480818008480212020600a0202c848a0200c84890800c08090800c080828008880828008880921228080830328080818008480818008480a080 (by decide +kernel)

def state179_29 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_29 : Impossible true (goalAt 179) 5 state179_29.toFinset :=
  node_ok cuts179 [⟨state179_24,exclude179_24⟩,⟨state179_5,exclude179_5⟩] 0xc080908024200302024200a0800c080908004c0c908024200130320a0090800440c828008880828020a00222020a00a08008880828020c0c828020a00810320600908004c0c81802060082808000481800848081802820200002060083032060081802080c921228080a02040010a02028200a080400103212 (by decide +kernel)

def state179_30 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_30 : Impossible true (goalAt 179) 6 state179_30.toFinset :=
  node_ok cuts179 [⟨state179_6,exclude179_6⟩,⟨state179_25,exclude179_25⟩,⟨state179_22,exclude179_22⟩,⟨state179_28,exclude179_28⟩,⟨state179_29,exclude179_29⟩] 0x100050c848321220c0ca08028202000428200a08020c0c32120c84a00030c848321240010a08028202000228200a0804001032120c84832122420090802820030202820032120c08030202820090802420100050c080302020c0c908024201000224200908020c0c30200c08100020c08030204000490802420100022420090804000430200c080321220a00828028200222028200321208880222028200828020a00130320a00828024201000624200130340008110324200828020a00830308880222020404828020a00830320a00828020404222008881000608880222040000828020a01000620a0082804000022200888100034000ca02008c0c818020600a0804000ca08008c0e000108c0ca08020600818004c0c81802060090804000c908004c0d000204c0c90802060081804000c81802060082804000c82804000d000680000828020600818020c0d000520c0d00032060081804000d00032080d0003400142120 (by decide +kernel)

def state179_31 : List Sig := [0x5555555555555555555555555555555555555555555500005555555555550000,input 7,input 4,input 5,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_31 : Impossible true (goalAt 179) 4 state179_31.toFinset :=
  node_ok cuts179 [] 0x20a00a08008880828020a0090800440c828008880828020a00222028080a08028200321224200a0800c08090800c080908024200302020600131220a008180206002120282008180206001312242008180084808180206002120 (by decide +kernel)

def state179_32 : List Sig := [0x3333333333333333333333333333333333333333333300003333333333330000,input 7,input 4,input 5,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_32 : Impossible true (goalAt 179) 4 state179_32.toFinset :=
  node_ok cuts179 [] 0x20600a08008480818020600908004c48818008480818020600212028080a08028200321224200a0800c08090800c080908024200302020600131220600828020a00222028200828020a00110324200828008880828020a002220 (by decide +kernel)

def state179_33 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_33 : Impossible true (goalAt 179) 5 state179_33.toFinset :=
  node_ok cuts179 [⟨state179_10,exclude179_10⟩,⟨state179_31,exclude179_31⟩,⟨state179_32,exclude179_32⟩] 0x828028200222020a00828024202000020a00222020a00828008882000220a00828040000818020a0013122060081802820021202060081802420013122060021202060081800848200012060081804000ca02028200a0800c848230324200a0800c08090800c080908024200302004c0c8303 (by decide +kernel)

def state179_34 : List Sig := [0xffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_34 : Impossible true (goalAt 179) 5 state179_34.toFinset :=
  node_ok cuts179 [⟨state179_11,exclude179_11⟩] 0x828028200222020a00828024202000020a00222020a00828008880818020a00131220600818028200212020600818024200131220600212020600818008480321228200a0800c84890802820030202420030202420090800c080222020a00222020a00212020600212020600321228200321228200302024200302024200a020 (by decide +kernel)

def state179_35 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_35 : Impossible true (goalAt 179) 4 state179_35.toFinset :=
  node_ok cuts179 [] 0x20a00908008880828008880828020a0022200c848828020a00301220600828004c48818020600908008480818008480818020600212004c4881802060013120c08090802420100040c84890802420082120c84830200c0802212 (by decide +kernel)

def state179_36 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_36 : Impossible true (goalAt 179) 5 state179_36.toFinset :=
  node_ok cuts179 [⟨state179_35,exclude179_35⟩] 0x20a00222008880828020a00908008880828008880828020a00222008880828020a00222020600828004c4881802060021200848081802060090800848081800848081802060021200848081802060021202820032122484a00000c84830200c848302008848921224200908020848302024200908040010a020 (by decide +kernel)

def state179_37 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_37 : Impossible true (goalAt 179) 5 state179_37.toFinset :=
  node_ok cuts179 [⟨state179_35,exclude179_35⟩,⟨state179_12,exclude179_12⟩] 0x20a00302080004828020a00a08008880828008880828020a0022200c848828020a00301220600828004c48818020600302004c48818020600a08008480818008480818020600212004c4881802060013122420030202408200000c08032120c080302008848a02028200a08040014321228200a080400049212 (by decide +kernel)

def state179_38 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_38 : Impossible true (goalAt 179) 6 state179_38.toFinset :=
  node_ok cuts179 [⟨state179_13,exclude179_13⟩,⟨state179_33,exclude179_33⟩,⟨state179_34,exclude179_34⟩,⟨state179_36,exclude179_36⟩,⟨state179_37,exclude179_37⟩] 0x921208880222028080828020a00921220a00828028080222008880321220a0082800c04022200888032120888022200c040828020a01000120a0082800c08100010c08100094000600000c080828020a01000920a00828040000222008881000908880222040000828020a00830308480212028080818020600830320600818028080212008481000220600818020a00131220a01000204c48131220a0081802060100042060081800c84821200848100020848021200c84881802060100012060081800c08013120c081000204c4813120c08081802060100022060081804000c21200848100020848021204000c818020600a0200c848a02024849000424848a02080010a0202484832120c849000140004a0802484830200c080a02040004a0202484a000324848a0200c08030200c84900040c84900010c0803020400050001088490001400109080280810005280808303800088303280820001280808303400148303 (by decide +kernel)

def state179_39 : List Sig := [0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,input 5,input 4,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_39 : Impossible true (goalAt 179) 5 state179_39.toFinset :=
  node_ok cuts179 [⟨state179_14,exclude179_14⟩] 0x222020a00828008880828024202000020a00828008880222020a00818020a0013122060021202060081800848081802420013122060081800848021202060030202420090800c08090800c080302024200a02024848a0202484882800888082800888081800848081800848092122808092122808090800c08090800c080a080 (by decide +kernel)

def state179_40 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_40 : Impossible true (goalAt 179) 5 state179_40.toFinset :=
  node_ok cuts179 [⟨state179_35,exclude179_35⟩,⟨state179_15,exclude179_15⟩] 0x20a00908080004828008880828020a00222020a00a08008880828024848828020a00901220600828004c48818020600908004c48818008480818020600212020600a08008480818004c4881802060013120c080908028202000024200921224200908020848921228080a02040004a02028200a080400103212 (by decide +kernel)

def state179_41 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_41 : Impossible true (goalAt 179) 6 state179_41.toFinset :=
  node_ok cuts179 [⟨state179_36,exclude179_36⟩,⟨state179_16,exclude179_16⟩,⟨state179_33,exclude179_33⟩,⟨state179_39,exclude179_39⟩,⟨state179_40,exclude179_40⟩] 0x100050c848321224848a08028202000428200a0802484832120c84a000308c0c230340010a08028202000228200a08040010230308c0c321220a00828028200222028200321208880222028200828020a00921208880222024040828020a00921220a00828024040222008881000120a00828024201000124201000940006000124200828020a01000908880222040000828020a01000920a00828040000222008880230320600818028200212028200230308480212028200818020601000220600818020a00131220a01000204c48131220a00818020601000508480212024848818020601000220600818024848212008481000120600818024200131224201000204c4813122420081802060100020848021204000c81802060100022060081804000c212008481000140004a0200c848908024200a08040004a0800c84a00000c848a080242009080248490005248490001242009080400050001208490001400143020 (by decide +kernel)

def state179_42 : List Sig := [0xbbbb0000bbbb0000bbbb0000bbbb0000bbbb0000aaaa0000bbbb0000aaaa,input 0,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_42 : Impossible true (goalAt 179) 3 state179_42.toFinset :=
  node_ok cuts179 [] 0x28080a08028200221208480818020600212020600a08008480818008880828020a00222020a002220282008280206001312206008280 (by decide +kernel)

def state179_43 : List Sig := [0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaaaaaabbbbbbbbaaaaaaaa,input 0,input 5,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_43 : Impossible true (goalAt 179) 4 state179_43.toFinset :=
  node_ok cuts179 [⟨state179_42,exclude179_42⟩] 0x30202420090800c080908028200302024200a02028200a0800c848818024200110320600212020600818008480818028200212020600131220a02000024200828008880828020a00222020a002220282008280 (by decide +kernel)

def state179_44 : List Sig := [0x5555111155551111555511115555111155551111555500005555111155550000,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_44 : Impossible true (goalAt 179) 3 state179_44.toFinset :=
  node_ok cuts179 [] 0x28080a0802820030120c080908024200302024200a0800c0809080084808180206002120206002120282008180206001312242008180 (by decide +kernel)

def state179_45 : List Sig := [0xffff3333ffff3333ffff3333ffff3333ffff3333ffff0000ffff3333ffff0000,input 4,input 5,input 7,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_45 : Impossible true (goalAt 179) 4 state179_45.toFinset :=
  node_ok cuts179 [⟨state179_44,exclude179_44⟩] 0x212020600818008480818028200212020600818024200131220602000020600818020a00a02028200a0800c04830202420090800c080908028200302024200110308880828020a00222020a002220282008280 (by decide +kernel)

def state179_46 : List Sig := [0x3333333333333333333333333333333333333333000000003333333300000000,input 5,input 7,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_46 : Impossible true (goalAt 179) 5 state179_46.toFinset :=
  node_ok cuts179 [⟨state179_7,exclude179_7⟩,⟨state179_17,exclude179_17⟩,⟨state179_43,exclude179_43⟩,⟨state179_45,exclude179_45⟩] 0x2484830200c080a02024200908024848908024200a0200c08030200c848908024200a0800c080a0800c84830200c080a0802420090800440c818020600908004c4890800440c131204c48908020600818020c0c212008480a02020600818020c0c818020600a02008480212008c0c818020600a08008480a08008c0c212008480a08020600818028080321228080921228200a08028080a0802820092120c848321224200828020a00110380004110324202000324200110320a00828020600828020600131280000131220602000220600131220a00828028080222008880921220a00828028080828020a00921208880222028200828020a00321208880222028200222028200321220a008280 (by decide +kernel)

def state179_47 : List Sig := [0x5555555555555555555555555555555555555555000000005555555500000000,input 0,input 5,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_47 : Impossible true (goalAt 179) 5 state179_47.toFinset :=
  node_ok cuts179 [⟨state179_7,exclude179_7⟩] 0x30202420090800c080908028200302024200828024200110320a00222020a00828008880828028200222020a00a02028200a08008c0c130324200131224200111020a00131220a00131228080830328080131228200230328200908004c0c908004c0c828080000828040000a02024848a02020c0ca0800c848a08008c0c8180 (by decide +kernel)

def state179_48 : List Sig := [0x3333333333333333333333333333333333333333000000003333333300000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_48 : Impossible true (goalAt 179) 5 state179_48.toFinset :=
  node_ok cuts179 [] 0xc080908024200302024200a0800c08090800440c908024200110320600908004c48818008480818020600212020600a08008480818004c48818020600131224848a0202820100070c84882800440c908020a00818004c48818020a00222020a00828008880828008880a08020a010000 (by decide +kernel)

def state179_49 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000,input 4,input 5,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_49 : Impossible true (goalAt 179) 5 state179_49.toFinset :=
  node_ok cuts179 [⟨state179_17,exclude179_17⟩] 0x222020a00828008880828028200222020a00828004404110320a00818020a00131220600212020600818008480818028200212020600818004c48131220600a02028200a0800c848921228080921228080321228200321228200828080000828040000818004c48818004c48a02024848a02024848a0800c848a0800c8489080 (by decide +kernel)

def state179_50 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_50 : Impossible true (goalAt 179) 6 state179_50.toFinset :=
  node_ok cuts179 [⟨state179_22,exclude179_22⟩,⟨state179_26,exclude179_26⟩,⟨state179_29,exclude179_29⟩,⟨state179_8,exclude179_8⟩,⟨state179_18,exclude179_18⟩,⟨state179_33,exclude179_33⟩,⟨state179_37,exclude179_37⟩,⟨state179_40,exclude179_40⟩,⟨state179_46,exclude179_46⟩,⟨state179_47,exclude179_47⟩,⟨state179_48,exclude179_48⟩,⟨state179_49,exclude179_49⟩] 0x100050c08030202808090802420200072420090802808030200c08100042420090802820030202820200060c080302028200908024202000b04c0c130340004908024202000524200908040004130304c0c130320a00828024201000724200130380010110324200828020a01000508880222028080828020a01000720a00828028080222008881000420a00828028200222028201000708880222028200828020a0100078002a000840000828020a01000720a00828040001000740000130320600818024200131224200130304c48131224200818020601000720600818020a00131220a02000304c48131220a00818020601000508480212028080818020602000220600818028080212008481000420600818028200212028202000108480212028200818020602000904c4813124000c81802060200002060081804000c131204c49000440010921228081000528081000428200a080400110004400110004400143212 (by decide +kernel)

def state179_51 : List Sig := roots 179
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_51 : Impossible true (goalAt 179) 7 state179_51.toFinset :=
  node_ok cuts179 [⟨state179_9,exclude179_9⟩,⟨state179_19,exclude179_19⟩,⟨state179_27,exclude179_27⟩,⟨state179_30,exclude179_30⟩,⟨state179_38,exclude179_38⟩,⟨state179_41,exclude179_41⟩,⟨state179_50,exclude179_50⟩] 0x40014a0200c848a02040010921228200a08080018a02028200a0804001092120c84832124001492120c080302040004a02024200908080014921224200908040004a0200c080302040010321224200908040004a0800c080a0808001032120c080302040004a08024200908040000921208880222040000a02020a00828040000921220a00828040000a02008880222040000321220a00828040000a08008880a08040000321208880222040000a08020a00828040000130320a00828040000908040000908040000130380004110340000908020a0082804001483030848021204000ca0202060081808000c83032060081804000ca0200848021204001023032060081804000ca08008480a08080008230308480212040010a0802060081804000413032060081804000c908004c48908040008130304c48131240004908020600818040001000020600818040000828004c48828040002000004c481312400008280206008180 (by decide +kernel)

theorem lower179 : Claim 179 8 :=
  fromSearch 84 (by decide +kernel) exclude179_51

theorem lower115 : Claim 115 7 :=
  fromLift 7 2 84 lower113 (by decide +kernel)

theorem lower211 : Claim 211 7 :=
  fromLift 7 2 116 lower209 (by decide +kernel)

def rule243_0 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower241 none (by decide +kernel)

def rule243_1 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower242 none (by decide +kernel)

def rule243_2 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower227 none (by decide +kernel)

def rule243_3 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower179 none (by decide +kernel)

def rule243_4 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower115 none (by decide +kernel)

def rule243_5 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower211 none (by decide +kernel)

def rule243_6 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower179 (some (1,input 5,input 7)) (by decide +kernel)

def rule243_7 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower210 none (by decide +kernel)

def rule243_8 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower242 (some (1,input 5,input 7)) (by decide +kernel)

def rule243_9 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower81 none (by decide +kernel)

def rule243_10 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower113 none (by decide +kernel)

def rule243_11 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower227 (some (1,input 5,input 7)) (by decide +kernel)

def rule243_12 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower195 none (by decide +kernel)

def rule243_13 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower51 none (by decide +kernel)

def rule243_14 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower208 none (by decide +kernel)

def rule243_15 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower97 none (by decide +kernel)

def rule243_16 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower209 none (by decide +kernel)

def rule243_17 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower145 none (by decide +kernel)

def cuts243 : Cuts (goalAt 243) := [rule243_0,rule243_1,rule243_2,rule243_3,rule243_4,rule243_5,rule243_6,rule243_7,rule243_8,rule243_9,rule243_10,rule243_11,rule243_12,rule243_13,rule243_14,rule243_15,rule243_16,rule243_17]

def state243_0 : List Sig := [0xffffbbbbffffbbbb0000000000000000ffffbbbbffffaaaa,input 4,input 0,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_0 : Impossible true (goalAt 243) 4 state243_0.toFinset :=
  node_ok cuts243 [] 0x18108a08028200604210d08818020600434220600a08008480818020600908004c48818014108908024200504224200a0800c080908008880828020a00824220a00604228200828020600434220600828020a005042242008280 (by decide +kernel)

def state243_1 : List Sig := [0xffffbbbbffffbbbbffffbbbbffffbbbbffffbbbbffffaaaaffffbbbbffffaaaa,input 4,input 0,input 5,input 7,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_1 : Impossible true (goalAt 243) 5 state243_1.toFinset :=
  node_ok cuts243 [⟨state243_0,exclude243_0⟩] 0x30908c08030200824228200c08018908a08018908a08028200624220600c0801040c818008480818020600c24220600a08008480818020600908004c48818010d08908030200501224200302024200908030908908028200302024200504220a02000030200828030108828020a00c24220a006042282008280 (by decide +kernel)

def state243_2 : List Sig := [0xbbbb0000bbbb0000bbbb0000bbbb0000bbbb0000aaaa0000bbbb0000aaaa,input 4,input 0,input 5,input 7,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_2 : Impossible true (goalAt 243) 5 state243_2.toFinset :=
  node_ok cuts243 [] 0xc24230200c08020908a08030200624228200624228200a08018908818030200410320600212020600818030908818028200212020600818014108131220600501230200504230200504230908821214108504228200221228200828014048c08020a00c04220a00828030908828018108a08020a00818010d08818020a009080 (by decide +kernel)

def state243_3 : List Sig := [0xffff0000ffff0000bbbb0000bbbb0000ffff0000ffff0000bbbb0000aaaa,input 6,input 0,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_3 : Impossible true (goalAt 243) 4 state243_3.toFinset :=
  node_ok cuts243 [] 0x18108a08028200604228200c08018108a08010d08818020600434220600a08008480818020600c08010d08818030108c08030200602014108828020a00504220a00222028200828020600131220600828020a005042302008280 (by decide +kernel)

def state243_4 : List Sig := [0xffffffffffffffffbbbbbbbbbbbbbbbbffffffffffffffffbbbbbbbbaaaaaaaa,input 6,input 0,input 5,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_4 : Impossible true (goalAt 243) 5 state243_4.toFinset :=
  node_ok cuts243 [⟨state243_3,exclude243_3⟩] 0x14108908024200504224200a0800c080908024200c08014108908080000828024200828018108a08028200604228200c08018108a0800888082802820082802060090800440c818010d08818020600434220600a08008480818020600c08010d08818004c48c04230200c08018080501230108828020a002220 (by decide +kernel)

def state243_5 : List Sig := [0xbbbbbbbbbbbbbbbb0000000000000000bbbbbbbbaaaaaaaa,input 6,input 0,input 5,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_5 : Impossible true (goalAt 243) 5 state243_5.toFinset :=
  node_ok cuts243 [] 0x504224200908014108908028200302024200908014108504224200604228200a08018108a08018108604228200818024200110320600434220600818010d08818028200212020600818010d08434220600c04228080824220908828014108908020a00222020a00828030108828018108a08020a00818010d08818020a00c080 (by decide +kernel)

def state243_6 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 4,0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaaaaaabbbbbbbbaaaaaaaa,input 5,input 7,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_6 : Impossible true (goalAt 243) 5 state243_6.toFinset :=
  node_ok cuts243 [] 0xc24230200c08020908a08030200624228200624228200a08018908828014048c08020a00c04220a00828030908828018108a08020a00828004c48131220a00818010d08818020a00501230200501230200921230908921230908321228200321228200908020600c08014048818008480818020600c24220600a080084808180 (by decide +kernel)

def state243_7 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 6,0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaaaaaabbbbbbbbaaaaaaaa,input 5,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_7 : Impossible true (goalAt 243) 5 state243_7.toFinset :=
  node_ok cuts243 [] 0x504224200908014108908028200302024200908014108504224200908020600504220600624228200a08018908a08018908624228200a08020600624220600828014108908020a00434220a00828010d08828018108a08020a00828010d08434220a00818010d08818020a00c24228080c24228080c080309088180206002120 (by decide +kernel)

def state243_8 : List Sig := [0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaaaaaabbbbbbbbaaaaaaaa,input 0,input 5,input 7,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_8 : Impossible true (goalAt 243) 6 state243_8.toFinset :=
  node_ok cuts243 [⟨state243_1,exclude243_1⟩,⟨state243_2,exclude243_2⟩,⟨state243_4,exclude243_4⟩,⟨state243_5,exclude243_5⟩,⟨state243_6,exclude243_6⟩,⟨state243_7,exclude243_7⟩] 0xc24218080c24228080c08030200c24230200c0802808060202090850122420090803020050423020050121410850423020090802420092121410850423090890802420092122420090803090850421410832122420090802820030202820032120c080302028200908024200602028200a08030200624230200602018908624230200a08028200a02018908624230908a08028200a02028200a08030908624218908410320600818030201000e30200410380014410330200818020600110320600818024201000e24200110380010110324200818020600810308480212030908818020600810320600818030908212030908210320600818028200212028200210308480212028200818020601000e40024434230200828020a0050128000c501230202000230200501220a00828024200828020a00504280004504224202000024200504220a00828028080222030108c24220a00828028080828020a00c24208880c24228200828020a00624208880604228200222028200624220a008280 (by decide +kernel)

def state243_9 : List Sig := [0x5555555555555555555511115555111155555555555555555555111155550000,input 6,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_9 : Impossible true (goalAt 243) 4 state243_9.toFinset :=
  node_ok cuts243 [] 0x18108a08028200604228200c08018108a08014108908024200504224200a0800c080908024200c08014108908030108c08030200602010d088180206004342206002120282008180206001312242008180206004342302008180 (by decide +kernel)

def state243_10 : List Sig := [0xffffffffffffffffffff3333ffff3333ffffffffffffffffffff3333ffff0000,input 6,input 4,input 5,input 7,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_10 : Impossible true (goalAt 243) 5 state243_10.toFinset :=
  node_ok cuts243 [⟨state243_9,exclude243_9⟩] 0x10d08818020600434220600a08008480818020600908004c48818020600c08010d08818080000818020600828018108a08028200604228200c08018108a08008880828028200828014108908024200504224200a0800c080908024200c0801410890800440cc04230200c08018080410330108828020a002220 (by decide +kernel)

def state243_11 : List Sig := [0xffff3333ffff33330000000000000000ffff3333ffff0000,input 6,input 4,input 5,input 7,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_11 : Impossible true (goalAt 243) 5 state243_11.toFinset :=
  node_ok cuts243 [] 0x434220600818010d08818028200212020600818024200131220600818010d08434220600604228200a08018108a08018108604228200504224200908014108908028200302024200908014108504224200c04228080824220908818010d08818020a00222020a00828030108828018108a08020a00828014108908020a00c080 (by decide +kernel)

def state243_12 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xffff3333ffff3333ffff3333ffff3333ffff3333ffff0000ffff3333ffff0000,input 5,input 7,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_12 : Impossible true (goalAt 243) 5 state243_12.toFinset :=
  node_ok cuts243 [] 0x434220600818010d08818028200212020600434220600818020a00818010d08434220600818024200434220600624228200a08018908a08018908624228200a08024200624224200504220a00828014108828018108a08020a00828014108504220a00828014108908020a00c24228080c24228080c080309089080242003020 (by decide +kernel)

def state243_13 : List Sig := [0x5555111155551111555511115555111155551111555500005555111155550000,input 0,input 4,input 5,input 7,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_13 : Impossible true (goalAt 243) 5 state243_13.toFinset :=
  node_ok cuts243 [] 0xc24230200c08020908a08030200624228200624228200a08018908908030200501224200302024200908030908908028200302024200410330200434230200434230508810310d0843422820021032820043422420011032420082801040cc08020a00c04220a00828030908828018108a08020a00828014108908020a008180 (by decide +kernel)

def state243_14 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 0,0xffff3333ffff3333ffff3333ffff3333ffff3333ffff0000ffff3333ffff0000,input 5,input 7,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_14 : Impossible true (goalAt 243) 5 state243_14.toFinset :=
  node_ok cuts243 [] 0xc24230200c08020908a08030200624228200624228200a0801890882801040cc08020a00c04220a00828030908828018108a08020a00828014108908020a00131230200410330200131230908830330908131228200230328200110320a00131220a00818024200c0801404890800c080908024200c24224200a0800c0809080 (by decide +kernel)

def state243_15 : List Sig := [0xffff3333ffff3333ffff3333ffff3333ffff3333ffff0000ffff3333ffff0000,input 4,input 5,input 7,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_15 : Impossible true (goalAt 243) 6 state243_15.toFinset :=
  node_ok cuts243 [⟨state243_1,exclude243_1⟩,⟨state243_10,exclude243_10⟩,⟨state243_11,exclude243_11⟩,⟨state243_12,exclude243_12⟩,⟨state243_13,exclude243_13⟩,⟨state243_14,exclude243_14⟩] 0xc24218080c24228080c08030200c24230200c08028080602020908410320600818030200434230200410310d08434230200818020600830310d08434230908818020600830320600818030908434210d08230320600818028200212028200230308480212028200818020601000f20600818024200131224202000504c48131224200818020602000410d08434220a00818020602000020600818020a00434220a00602028200a08030200624230200602018908624230200a08028200a02018908624230908a08028200a02028200a08030908624218908501224200908030201000f3020050128000c50123020090802420090120c08030203090890802420090122420090803090830203090830122420090802820030202820030120c080302028200908024201000f40024504230200828020a00410380008410330202000130200410320a00828028080222030108c24220a00828028080828020a00c24208880c24228200828020a00624208880604228200222028200624220a008280 (by decide +kernel)

def state243_16 : List Sig := [0x5555555555555555111111111111111155555555555555551111111100000000,input 0,input 6,input 5,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_16 : Impossible true (goalAt 243) 5 state243_16.toFinset :=
  node_ok cuts243 [] 0x504224200908014108908028200302024200908030200504224200604228200a08018108a08030200604228200c04230200c0801808011032420013122420013123010881033010813122820021032820013123020041033020082800440c908020a00c04220a00828008880828008880a08020a00828014048c08020a008180 (by decide +kernel)

def state243_17 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,0xffffffffffffffff3333333333333333ffffffffffffffff3333333300000000,input 5,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_17 : Impossible true (goalAt 243) 5 state243_17.toFinset :=
  node_ok cuts243 [] 0x504224200908014108908028200302024200110320a00908020a00908030200504224200604228200a08018108222020a00a08020a00a08030200604228200c04220a00828008880828014048c08020a00434224200110324200434220508830310d08434228200230328200410320a00434220a00818030108c080302006020 (by decide +kernel)

def state243_18 : List Sig := [0xffff0000ffff00003333000033330000ffff0000ffff0000333300000000,input 4,input 6,input 5,input 7,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_18 : Impossible true (goalAt 243) 5 state243_18.toFinset :=
  node_ok cuts243 [] 0x434220600818010d08818028200212020600818030200434220600818004c48131220600604228200a08018108a08030200604228200c04230200c08018080901230108821230108301228200221228200501230200501230200818004c48818020a00c04220a00828008880828008880a08020a00828014048c08020a009080 (by decide +kernel)

def state243_19 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,0xffffffffffffffff3333333333333333ffffffffffffffff3333333300000000,input 5,input 7,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_19 : Impossible true (goalAt 243) 5 state243_19.toFinset :=
  node_ok cuts243 [] 0x434220600818010d08818028200212020600131220600818020a00818014108131220600818030200434220600604228200a08018108222020a00a08020a00a08030200604228200c04220a00828008880828014048c08020a00504224108921214108504228200321228200501220a00504220a00908030108c080302006020 (by decide +kernel)

def state243_20 : List Sig := [0xffffffffffffffff3333333333333333ffffffffffffffff3333333300000000,input 6,input 5,input 7,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_20 : Impossible true (goalAt 243) 6 state243_20.toFinset :=
  node_ok cuts243 [⟨state243_4,exclude243_4⟩,⟨state243_10,exclude243_10⟩,⟨state243_16,exclude243_16⟩,⟨state243_17,exclude243_17⟩,⟨state243_18,exclude243_18⟩,⟨state243_19,exclude243_19⟩] 0x92121410850423010890802420092122420090803010850421410832122420090802820030202820032120c08030202820090802420100112420090803020050423020200051410850423020090802420200040440c110320a00908020a02000124200908020a00110320a00110320600818024200131224200110304c48131224200818020600830310d08434230108818020600830320600818030108434210d08230320600818028200212028200230308480212028200818020601001120600818030200434230202000310d08434230200818020602000204c48131220a00818020602000020600818020a00131220a00a02018108604230108a08028200a02028200a08030108604218108602028200a08030200604230200602018108604230200a0802820022200c848222020a00a08020a00222028200a08020a00321220a00c04218080c04228080c08030200c04230200c08028080602018081000940024501230108222030108921220a00828030108828020a009212088802220 (by decide +kernel)

def state243_21 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 0,input 4,0x3333333333333333333333333333333333333333000000003333333300000000,input 5,input 7,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_21 : Impossible true (goalAt 243) 6 state243_21.toFinset :=
  node_ok cuts243 [⟨state243_1,exclude243_1⟩,⟨state243_6,exclude243_6⟩,⟨state243_14,exclude243_14⟩] 0xc24230200c08020908a08030200624228200624228200a08018908828014048c08020a00c04220a00828030908828018108a08020a0082800440e000220a00828004c4a000120a00828040026000020a00501230200501230200921230908921230908321228200321228200908004c48c0801040cc08004c48c24220c0cc24204c48a08008c0ca0800440c131240038818014048c08014048c08024848c24224848c2420c848a0800c848a080 (by decide +kernel)

def state243_22 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 6,0x3333333333333333333333333333333333333333000000003333333300000000,input 5,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_22 : Impossible true (goalAt 243) 6 state243_22.toFinset :=
  node_ok cuts243 [⟨state243_4,exclude243_4⟩,⟨state243_7,exclude243_7⟩,⟨state243_17,exclude243_17⟩] 0x504224200908014108908028200302024200908014108504224200908014108504224200624228200a08018908a08018908624228200a08018908624228200828014108908020a00c04220a00828030908828018108a08020a0082801040e000220a00828010d0a000120a00828040026000020a00c24228080c24228080c08010d0890800440c908010d08c24220c0c434210d08a08008c0ca0801040c434240038818030908a02030908a020 (by decide +kernel)

def state243_23 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,0x3333333333333333333333333333333333333333000000003333333300000000,input 5,input 7,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_23 : Impossible true (goalAt 243) 6 state243_23.toFinset :=
  node_ok cuts243 [⟨state243_10,exclude243_10⟩,⟨state243_12,exclude243_12⟩,⟨state243_19,exclude243_19⟩] 0x434220600818010d08818028200212020600818010d08434220600818014108131220600818010d08434220600624228200a08018908a08018908624228200a08018908624228200818010d08818020a00c04220a00828030908828018108a08020a0082801404a000220a0082801410a000120a00828040026000020a00c24228080c24228080c08014108c24224848504214108a0800c848a0801404850424003c908030908a02030908a020 (by decide +kernel)

def state243_24 : List Sig := [0x3333333333333333333333333333333333333333000000003333333300000000,input 5,input 7,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_24 : Impossible true (goalAt 243) 7 state243_24.toFinset :=
  node_ok cuts243 [⟨state243_8,exclude243_8⟩,⟨state243_15,exclude243_15⟩,⟨state243_20,exclude243_20⟩,⟨state243_21,exclude243_21⟩,⟨state243_22,exclude243_22⟩,⟨state243_23,exclude243_23⟩] 0x40028c24218080c24240028a02030200c08040028c24230200c08040028a0201808082424004450122420090804003cc08014108c0808001450121410850424003cc08024200908040028921214108504240028c24224200908040028921224200908040028c24214108504240040321224200908040040a0800c080a0804004032120c080302040040a08024200908040044410320600818040038c08010d08c08080010410310d08434240038c0802060081804003c110320600818040038908004c4890808000c110304c48131240038908020600818040028830310d08434240028c24220600818040028830320600818040028c24210d08434240040230320600818040040a08008480a08040040230308480212040040a08020600818040040602028200a08040040c08018908c08040040602018908624240040c08028200a08040028a02018908624240028c24228200a08040028a02028200a08040028c24218908624240024c08020a00828040024501240024501240024c08080008c08040024501220a0082804003c908020a0082804002450424002450424002490808000490804003c504220a00828040038818020a00818040024434240024434240024818080000818040038434220a00828040028a02008880c04240028c24220a00828040028a02020a00828040028c24208880c24240028a08020a00828040028624208880604240028a08008880a08040028624220a008280 (by decide +kernel)

def state243_25 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_25 : Impossible true (goalAt 243) 8 state243_25.toFinset :=
  node_ok cuts243 [⟨state243_24,exclude243_24⟩] 0x40011000418080602040010a02030200c08040011000630200c08040010a02018080602040025000914848521240035000330200c08040025000630200c08040035000314848521240034521224200908040030c08014908c0804002c521214908524240030c08024200908040011000414908524240010a02024200908040011000b24200908040010a02014908524240015000524200908040014a0800c080a08040015000b0c080302040014a08024200908040025000914908524240031000224200908040025000b24200908040031000214908524240028521220a00828040028c08040028c08040028521240018501240028c08020a00828040028524220a0082804002890804002890804002852424002c504240028908020a00828040011000408880222040010a02020a00828040011000a20a00828040010a02008880222040015000520a00828040014a08008880a08040015000a08880222040014a08020a00828040029000a40026000040029000020a00828040029000a20a0082804002900004002900004003443032060081804001cc08010d08c08040020430310d0843424001cc0802060081804003013032060081804001c908004c4890804002c130304c4813124001c908020600818040029000a20600818040028828010d08828040029000810d08434240028828020600818040011000410d08434240010a02020600818040011000820600818040010a02010d08434240015000520600818040014a08008480a08040015000808480212040014a08020600818040025000910d0843424001d00012060081804002500082060081804001d000110d08434240011000440014c24240014602028200a08040014c08040014c08040014602040018602040014c08028200a08040010a02040010a02040011000528200a080400110004400110004400110004400106242 (by decide +kernel)

def state243_26 : List Sig := roots 243
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_26 : Impossible true (goalAt 243) 9 state243_26.toFinset :=
  node_ok cuts243 [⟨state243_25,exclude243_25⟩] 0x4000cc24218080c2424000ca02030200c0804000cc24230200c0804000ca02018080824240010a02018908624240014c24228200a08080000a02028200a08040010c2421890862424000c602028200a0804000cc08018908c0804000c60201890862424000cc08028200a08040008921214908524240008c24224200908040008921224200908040008c24214908524240008521224200908040008c08014908c08040008521214908524240008c08024200908040008321224200908040008a0800c080a0804000832120c080302040008a08024200908040000c24208880c24240000c04020a00828040000c24220a00828040000c04008880c04240000521220a00828040000c08040000c0804000052124000c501240000c08020a00828040000624220a00828040000a08008880a08040000624208880604240000a08020a00828040000524220a00828040000908040000908040000524240008504240000908020a00828040004830310d08434240004c24220600818040004830320600818040004c24210d08434240004430320600818040004c08010d08c08040004430310d08434240004c08020600818040004230320600818040004a08008480a08040004230308480212040004a08020600818040008130320600818040008908004c48908040008130304c48131240008908020600818040001000020600818040000828010d08828040001000110d084342400008280206008180 (by decide +kernel)

theorem lower243 : Claim 243 10 :=
  fromSearch 84 (by decide +kernel) exclude243_26


open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

def smallCircuit : Circuit := ⟨[⟨.or, [4, 6]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [12, 6]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [13, 7]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [19, 17]⟩], 20⟩

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


def lowRow (i : Fin 8) : Row := Fin.ofNat 256 (1 <<< ([4, 5, 6, 7, 0, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 256 ((1 <<< i.val) ||| (1 <<< ([4, 5, 6, 7, 0, 0, 0, 0] : List Nat).getD i.val 0))

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

end PEqualNP.Outside.L_meta_32347_aux

open PEqualNP.Outside.L_meta_32347_aux in
theorem PEqualNP.Outside.L_meta_32347 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true))  := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31165_aux


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
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)


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

theorem lower225 : Claim 225 5 :=
  fromLift 5 1 6291462 lower224 (by decide +kernel)

theorem lower240 : Claim 240 5 :=
  fromLift 5 16 1147535360 lower224 (by decide +kernel)

def cuts208 : Cuts (goalAt 208) := []

def state208_0 : List Sig := roots 208
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude208_0 : Impossible true (goalAt 208) 3 state208_0.toFinset :=
  node_ok cuts208 [] 0x30100501030100901030200c08030100c08030200901014040501024040504014100c04024200908024040908024200c04014100504014040908024200c08014100c08014040504014100c080242009080 (by decide +kernel)

theorem lower208 : Claim 208 4 :=
  fromSearch 1141243904 (by decide +kernel) exclude208_0

def cuts193 : Cuts (goalAt 193) := []

def state193_0 : List Sig := roots 193
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude193_0 : Impossible true (goalAt 193) 3 state193_0.toFinset :=
  node_ok cuts193 [] 0x30100410130100810130200c08030100c08030200810110404410120404414010500c04020600818020404818020600c04010500414010404818020600c08010500c08010404414010500c080206008180 (by decide +kernel)

theorem lower193 : Claim 193 4 :=
  fromSearch 6 (by decide +kernel) exclude193_0

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

theorem lower177 : Claim 177 5 :=
  fromLift 5 32 7340036 lower145 (by decide +kernel)

def cuts81 : Cuts (goalAt 81) := []

def state81_0 : List Sig := roots 81
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude81_0 : Impossible true (goalAt 81) 3 state81_0.toFinset :=
  node_ok cuts81 [] 0x140401101140404101141005040140405040141004101044041101104041110044405010105004140104044140105005010044401110044044140105005040044405040044041110044405040105004140 (by decide +kernel)

theorem lower81 : Claim 81 4 :=
  fromSearch 4 (by decide +kernel) exclude81_0

theorem lower113 : Claim 113 5 :=
  fromLift 5 32 6291460 lower81 (by decide +kernel)

def rule241_0 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower225 none (by decide +kernel)

def rule241_1 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower224 none (by decide +kernel)

def rule241_2 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower240 none (by decide +kernel)

def rule241_3 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower209 none (by decide +kernel)

def rule241_4 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower177 none (by decide +kernel)

def rule241_5 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower113 none (by decide +kernel)

def rule241_6 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower145 none (by decide +kernel)

def rule241_7 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower208 none (by decide +kernel)

def rule241_8 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower81 none (by decide +kernel)

def rule241_9 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower193 none (by decide +kernel)

def cuts241 : Cuts (goalAt 241) := [rule241_0,rule241_1,rule241_2,rule241_3,rule241_4,rule241_5,rule241_6,rule241_7,rule241_8,rule241_9]

def state241_0 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 6,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_0 : Impossible true (goalAt 241) 4 state241_0.toFinset :=
  node_ok cuts241 [] 0x2420081800c484818024200c0801410090801410090802420050400c4c0908024201000920600c0801050081801050081802060041400c4c0818020601000330100c080302004121144c09130 (by decide +kernel)

def state241_1 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 6,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_1 : Impossible true (goalAt 241) 4 state241_1.toFinset :=
  node_ok cuts241 [] 0x908020600312120600908030200504024200504024200908014100818030200414020600414020600818010500d13030200c080244c0504024200504024200414020600414020600313030200412130200c040 (by decide +kernel)

def state241_2 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_2 : Impossible true (goalAt 241) 4 state241_2.toFinset :=
  node_ok cuts241 [] 0x90802820031212420090803020050402420050402420090801410031212420090800c484818020600414028200414028200a08010500412128200a0804001cc04030200c0800c4c0313030200c0800c4c0b030 (by decide +kernel)

def state241_3 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 6,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_3 : Impossible true (goalAt 241) 5 state241_3.toFinset :=
  node_ok cuts241 [⟨state241_0,exclude241_0⟩,⟨state241_1,exclude241_1⟩,⟨state241_2,exclude241_2⟩] 0xb03014100504030100908024200b0302420090803010050401410100072420090802820031212820100010c484312128200908024201000624200908010484504014101000114100504010484908024200313024200908040024504014100313014100504040024908024200b03010500414030100a08028200b03028200a08030100414010500412128200a0804001c414010500412110500414040018a0802820031302820081804000c41402060031301050041404000ca08028200c04010484c0402c0c100062c0c0c04080008c0402c0c041212c0c1000240008c08030100313030100b03080004913030102000030100b0300c4c03130 (by decide +kernel)

def state241_4 : List Sig := [0xffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa,input 6,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_4 : Impossible true (goalAt 241) 4 state241_4.toFinset :=
  node_ok cuts241 [] 0x908020600312120600504024200908014100908014100504024200414020600818010500818010500414020600c040344c0c040144c0908014100908014100818010500818010500313030100812130100c080 (by decide +kernel)

def state241_5 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_5 : Impossible true (goalAt 241) 4 state241_5.toFinset :=
  node_ok cuts241 [] 0x90802060031212060050402420090801410090803020050402420031212420090800c48441402060081801810081803020060402060081212060081804001c313030100c0400c4c0c04030200c0800c4c07030 (by decide +kernel)

def state241_6 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_6 : Impossible true (goalAt 241) 5 state241_6.toFinset :=
  node_ok cuts241 [⟨state241_0,exclude241_0⟩,⟨state241_4,exclude241_4⟩,⟨state241_5,exclude241_5⟩] 0x100081c0c0703020484c08030202000230200c0802048470301c0c200011c0c051300c4c0c08030202000030200c0800c4c070300c4c070302420090803020050403020070301410050403020090802420100072420090802060031212060100010c48431212060090802060100081410050402048490802420100012420090802048450401410031301410050404002490802420031302420090804002450401410070302060081803020060403020070301810060403020081802060081211810060404001c81802060081212060081804002060401810031301810041404000c81802060031302060081804000c604018101000240008c040 (by decide +kernel)

def state241_7 : List Sig := [0x55555555000000005555555500000000555555550000000000000000,input 6,input 7,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_7 : Impossible true (goalAt 241) 4 state241_7.toFinset :=
  node_ok cuts241 [] 0x504024200908014100908030200504024200312124200313024200313030100812130100313030200412130200c04030200c0801c0c090800c484908028200818018100a08028200604028200604030200a080 (by decide +kernel)

def state241_8 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_8 : Impossible true (goalAt 241) 5 state241_8.toFinset :=
  node_ok cuts241 [⟨state241_0,exclude241_0⟩,⟨state241_2,exclude241_2⟩,⟨state241_5,exclude241_5⟩,⟨state241_7,exclude241_7⟩] 0x24200a0800c484908014100908024200504024200c0801410090800c48490802420031210c48490800c4c090802060031303010200023010031303020200013020031304000a00000c4c0604028200a08018100a08030200604028202000328200a0804001cb03030100c080400187030 (by decide +kernel)

def state241_9 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_9 : Impossible true (goalAt 241) 6 state241_9.toFinset :=
  node_ok cuts241 [⟨state241_3,exclude241_3⟩,⟨state241_6,exclude241_6⟩,⟨state241_8,exclude241_8⟩] 0x40020c0401c0c0c04040018b03030200c08080008c04030200c08040018b0301c0c0703040020b03014100504040024c04024200908040004b03024200908040020c04014100504040018703024200908040024c08014100c08040004703014100504040018c0802420090804001d000724200908040024a0800c484a0804001d00010c484312140024a0802420090804000881210c4c0313040008c04040008c04040008812180004812140008c0400c4c0c0404000841210c4c0313040008c08040008c08040008412180000412140008c0800c4c0c0804000831214002431214000890800c4c090804000831210c4c031304000890804000890804000d00034000c818040020b0301810060404001cc04028200a0804001cb03028200a08040020c04018100604040018703028200a0804001cc08018100c0804001c703018100604040018c08028200a080 (by decide +kernel)

def state241_10 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,input 7,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_10 : Impossible true (goalAt 241) 4 state241_10.toFinset :=
  node_ok cuts241 [] 0x2060090800c4c0818020600c0801050081801050081802060041400c484818020601000724200c0801410090801410090802420050400c484908024201000330100c080302005030144849121 (by decide +kernel)

def state241_11 : List Sig := [0xffffffffffffffffffff0000ffff0000,input 7,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_11 : Impossible true (goalAt 241) 4 state241_11.toFinset :=
  node_ok cuts241 [] 0x818024200313020600818030200414020600414020600818010500908030200504024200504024200908014100503030200c080140c0414020600414020600504024200504024200503030200503030200c040 (by decide +kernel)

def state241_12 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_12 : Impossible true (goalAt 241) 4 state241_12.toFinset :=
  node_ok cuts241 [] 0x81802820031302060081803020041402060041402060081801050031302060081800c4c0908024200504028200504028200a08014100503028200a08040024c04030200c0800c484503030200c0800c4849030 (by decide +kernel)

def state241_13 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_13 : Impossible true (goalAt 241) 5 state241_13.toFinset :=
  node_ok cuts241 [⟨state241_10,exclude241_10⟩,⟨state241_11,exclude241_11⟩,⟨state241_12,exclude241_12⟩] 0xa12110500414030100818020600a1212060081803010041401050100092060081802820031302820100010c4c03130282008180206010006206008180140c04140105010001105004140140c081802060031212060081804001c41401050031211050041404001c818020600903014100504030100a08028200903028200a08030100504014100503028200a08040024504014100503014100504040018a0802820031212820090804000c50402420031211410050404000ca08028200c040140c0c040240c10006240c0c04080008c040240c05030140c1000040000c08030100312130100a12180004912130102000030100a1210c484a030 (by decide +kernel)

def state241_14 : List Sig := [0xffffffffffffffff0000000000000000ffff0000ffff0000,input 6,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_14 : Impossible true (goalAt 241) 4 state241_14.toFinset :=
  node_ok cuts241 [] 0x818024200313020600414020600818010500818010500414020600504024200908014100908014100504024200c040240c0c040240c0818010500818010500908014100908014100903030100903030100c080 (by decide +kernel)

def state241_15 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_15 : Impossible true (goalAt 241) 4 state241_15.toFinset :=
  node_ok cuts241 [] 0x81802420031302060041402060081801050081803020041402060031302060081800c4c0504024200908018100908030200604024200903024200908040024903030100c0400c484c04030200c0800c4845030 (by decide +kernel)

def state241_16 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_16 : Impossible true (goalAt 241) 5 state241_16.toFinset :=
  node_ok cuts241 [⟨state241_10,exclude241_10⟩,⟨state241_14,exclude241_14⟩,⟨state241_15,exclude241_15⟩] 0x10008140c05030240c0c08030202000230200c080240c05030140c200011848451210c484c08030202000030200c0800c4846121180c061212060081803020041403020061211050041403020081802060100092060081802420031302420100010c4c03130242008180206010008105004140240c08180206010001206008180240c041401050031211050041404001c81802060031212060081804001c41401050050302420090803020060403020050301810060403020090802420090301810060404002490802420090302420090804002060401810031211810050404000c90802420031212420090804000c604018101000040000c040 (by decide +kernel)

def state241_17 : List Sig := [0xffff000000000000ffff000000000000ffff0000000000000000,input 6,input 7,input 4,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_17 : Impossible true (goalAt 241) 4 state241_17.toFinset :=
  node_ok cuts241 [] 0x81800c4c0313020600414020600818010500818030200414020600903030100903030100503030200503030200c04030200c080140c081800c4c0818028200908018100a08028200604028200604030200a080 (by decide +kernel)

def state241_18 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_18 : Impossible true (goalAt 241) 5 state241_18.toFinset :=
  node_ok cuts241 [⟨state241_10,exclude241_10⟩,⟨state241_12,exclude241_12⟩,⟨state241_15,exclude241_15⟩,⟨state241_17,exclude241_17⟩] 0x2060031300c4c0818020600a0800c4c0818010500818020600414020600c0801050081800c4c081802060031302420031213010200023010031213020200013020031214000200000c484604028200a08018100a08030200604028202000328200a08040024903030100c080400185030 (by decide +kernel)

def state241_19 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_19 : Impossible true (goalAt 241) 6 state241_19.toFinset :=
  node_ok cuts241 [⟨state241_13,exclude241_13⟩,⟨state241_16,exclude241_16⟩,⟨state241_18,exclude241_18⟩] 0x40020c040140c0c04040018903030200c08080008c04030200c080400189030140c0503040020a1211050041404001cc04020600818040004a12120600818040020c0401050041404001861212060081804001cc08010500c08040004612110500414040018c0802060081804000031212060081804000100070c4c031304000031210c4c0313040001000020600818040025000920600818040024a0800c4c0a0804002500010c4c0313040024a0802060081804000090300c484903040000c04040000c04040000903080004903040000c0400c484c0404000050300c484503040000c08040000c08040000503080000503040000c0800c484c0804000d00034000c908040020903018100604040024c04028200a08040024903028200a08040020c04018100604040018503028200a08040024c08018100c08040024503018100604040018c08028200a080 (by decide +kernel)

def state241_20 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaa,input 7,input 0,input 6,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_20 : Impossible true (goalAt 241) 4 state241_20.toFinset :=
  node_ok cuts241 [] 0x28200c08018100a08018100a08028200604030100c08030200703020600a0800c4c0818020600c080105008180105008180206004140242003121282009080242005040302009080206003130206009080141009080242005040 (by decide +kernel)

def state241_21 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff00000000aaaaaaaa,input 7,input 0,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_21 : Impossible true (goalAt 241) 4 state241_21.toFinset :=
  node_ok cuts241 [] 0x24200c08014100908014100908024200504030100c0803020070302060090800c4c0818020600c08010500818010500818020600414024200312124200a08028200604030200a08020600313020600a08018100a080282006040 (by decide +kernel)

def state241_22 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 0,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_22 : Impossible true (goalAt 241) 5 state241_22.toFinset :=
  node_ok cuts241 [⟨state241_0,exclude241_0⟩,⟨state241_20,exclude241_20⟩,⟨state241_21,exclude241_21⟩] 0xa08030200604028200604028200a08018102000228200a0804000c908028200312124200908030200504024200504024200908014102000124200908040000c04030200c08018484703020600a0808000081802060090800c484818020600c0801050081801050081802060041400c4c0b030 (by decide +kernel)

def state241_23 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 0,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_23 : Impossible true (goalAt 241) 5 state241_23.toFinset :=
  node_ok cuts241 [⟨state241_1,exclude241_1⟩] 0xa08030200604028200604028200a08018100908028200312124200908030200504024200504024200908014100f03030200c0802c0c0818028202000020600818024200312120600818030200414020600414020600818010500604028200604028200504024200504024200703030200612130200414020600414020600c040 (by decide +kernel)

def state241_24 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_24 : Impossible true (goalAt 241) 4 state241_24.toFinset :=
  node_ok cuts241 [] 0x28200818018100818018100a08028200414018484a08028200412124200a0800c48490802420081801410081801410090802420041400c48490802420031211050081802060100051c0c0818020600a0212c0c04140105006021 (by decide +kernel)

def state241_25 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_25 : Impossible true (goalAt 241) 5 state241_25.toFinset :=
  node_ok cuts241 [⟨state241_24,exclude241_24⟩] 0x28200604018100a08028200818018100818018100a08028200604018100a08028200414024200a0800c484908024200504014100908024200818014100818014100908024200504014100908024200414030200612128486000018484414018484414018084a12120600818028084414020600818040014c040 (by decide +kernel)

def state241_26 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_26 : Impossible true (goalAt 241) 5 state241_26.toFinset :=
  node_ok cuts241 [⟨state241_24,exclude241_24⟩,⟨state241_2,exclude241_2⟩] 0x28200c08018100a08018100a08028200604018484a08028200412124200a0800c484908024200c0801410090801410090802420050400c484908024200312110500a08080004a0801050090800c484908020600414020502000010500612110500414018084c04030200c08040014703030200c08040014b030 (by decide +kernel)

def state241_27 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 6,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_27 : Impossible true (goalAt 241) 6 state241_27.toFinset :=
  node_ok cuts241 [⟨state241_3,exclude241_3⟩,⟨state241_22,exclude241_22⟩,⟨state241_23,exclude241_23⟩,⟨state241_25,exclude241_25⟩,⟨state241_26,exclude241_26⟩] 0xb03018100604030100a08028200b03028200a08030100604018100612128200a08010404604018100612118100604010404a08028201000628200a0804000c60401810100061810060404000ca08028200b03014100504030100908024200b0302420090803010050401410100062420090802820031212820100010c484312128200908024201000424200908018484504014101000114100504018484908024201000124200908040000504014101000114100504040000908024200c04018484c0402c0c100042c0c0c04080010c0402c0c061212c0c1000240008c08028484414010500c04040008c04028486000328484c04010500414040008414010500a08040008a08040009000680000a08010500a0800c48441401050090804000890800c48500010c484908010500908018485000418485000210500414040009000218085000240010818030101000530100b03080008b03030102000130100b03040014b030 (by decide +kernel)

def state241_28 : List Sig := [0xffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa,input 6,input 0,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_28 : Impossible true (goalAt 241) 5 state241_28.toFinset :=
  node_ok cuts241 [⟨state241_4,exclude241_4⟩] 0x604028200a08018100a08018100604028200908028200312124200504024200908014100908014100504024200818028202000020600818024200312120600414020600818010500818010500414020600c0403c0c0c0401c0c0a08018100a08018100908014100908014100b03030100a12130100818010500818010500c080 (by decide +kernel)

def state241_29 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_29 : Impossible true (goalAt 241) 5 state241_29.toFinset :=
  node_ok cuts241 [⟨state241_24,exclude241_24⟩,⟨state241_5,exclude241_5⟩] 0x18100a08028200604028200c08018100a08028484a08028200812124200a0800c484908014100908024200504024200c0801410090800c484908024200312120600a0808000481802060090800c484818010500818030202000020600a12120600818028084b03030100c04040008c04030200c080400107030 (by decide +kernel)

def state241_30 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_30 : Impossible true (goalAt 241) 6 state241_30.toFinset :=
  node_ok cuts241 [⟨state241_6,exclude241_6⟩,⟨state241_25,exclude241_25⟩,⟨state241_22,exclude241_22⟩,⟨state241_28,exclude241_28⟩,⟨state241_29,exclude241_29⟩] 0x100051c0c0703028484c08030202000430200c0802848470301c0c200031c0c0703040010c08030202000230200c0804001070301c0c0703028200a08030200604030200703018100604030200a08028200a12118100604020404a08028200a12128200a0802040460401810100081810060404000ca08028201000828200a0804000c60401810070302420090803020050403020070301410050403020090802420100082420090802820031212820100010c484312128200908024201000514100504028484908024201000124200908028484504014101000114100504040000908024201000124200908040000504014101000540008c04018484818020600c08040008c08018486000118484c08020600818040008818020600a08040008a08040009000880000a0802060081800c48481802060090804000890800c48500010c4849080206008180284850005284850002206008180400150005280850005400144140 (by decide +kernel)

def state241_31 : List Sig := [0x5555555555555555555555555555555555555555555555555555000055550000,input 7,input 4,input 6,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_31 : Impossible true (goalAt 241) 4 state241_31.toFinset :=
  node_ok cuts241 [] 0x28200c08018100a08018100a08028200604030100c08030200703024200a0800c484908024200c080141009080141009080242005040206003130282008180206004140302008180206003130242008180105008180206004140 (by decide +kernel)

def state241_32 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff00000000ffff0000,input 7,input 4,input 6,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_32 : Impossible true (goalAt 241) 4 state241_32.toFinset :=
  node_ok cuts241 [] 0x20600c0801050081802060090800c4c0818010500818020600414030100c08030200703024200c08014100908014100908024200504020600313020600a08028200604030200a08024200312124200a08018100a080282006040 (by decide +kernel)

def state241_33 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,input 7,input 4,input 6,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_33 : Impossible true (goalAt 241) 5 state241_33.toFinset :=
  node_ok cuts241 [⟨state241_10,exclude241_10⟩,⟨state241_31,exclude241_31⟩,⟨state241_32,exclude241_32⟩] 0xa08030200604028200604028200a08018102000228200a0804000c818028200313020600818030200414020600818024200313020600414020600818010502000120600818040008c04030200c0801c0c0612124200a08080000908024200c0801410090801410090802420050400c484a121 (by decide +kernel)

def state241_34 : List Sig := [0xffffffffffffffffffff0000ffff0000,input 7,input 4,input 6,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_34 : Impossible true (goalAt 241) 5 state241_34.toFinset :=
  node_ok cuts241 [⟨state241_11,exclude241_11⟩] 0xa08030200604028200604028200a08018100818028200313020600818030200414020600818024200313020600414020600818010500703030200c0801c0c0908028202000024200908030200504024200504024200908014100604028200604028200414020600414020600703030200703030200504024200504024200c040 (by decide +kernel)

def state241_35 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_35 : Impossible true (goalAt 241) 4 state241_35.toFinset :=
  node_ok cuts241 [] 0x28200908018100908018100a0802820050401c0c0a08028200503020600a0800c4c081802060090801050081801050081802060041400c4c081802060031301410090802420100051c0c0908024200a0301c0c05040141006030 (by decide +kernel)

def state241_36 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_36 : Impossible true (goalAt 241) 5 state241_36.toFinset :=
  node_ok cuts241 [⟨state241_35,exclude241_35⟩] 0x28200604018100a08028200908018100908018100a08028200604018100a08028200504020600a0800c4c081802060041401050081802060090801050081801050081802060041401050081802060041403020070302c0c200001c0c050401c0c05040180c0b030242009080280c0504024200908040014c040 (by decide +kernel)

def state241_37 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_37 : Impossible true (goalAt 241) 5 state241_37.toFinset :=
  node_ok cuts241 [⟨state241_35,exclude241_35⟩,⟨state241_12,exclude241_12⟩] 0x28200c08018100a08018100a0802820060401c0c0a08028200503020600a0800c4c081802060050400c4c0818020600c0801050081801050081802060041400c4c0818020600313014100a08080004a080242005040241020000141007030141005040180c0c04030200c08040014703030200c08040000b030 (by decide +kernel)

def state241_38 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 0,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_38 : Impossible true (goalAt 241) 6 state241_38.toFinset :=
  node_ok cuts241 [⟨state241_13,exclude241_13⟩,⟨state241_33,exclude241_33⟩,⟨state241_34,exclude241_34⟩,⟨state241_36,exclude241_36⟩,⟨state241_37,exclude241_37⟩] 0xb03018100604030100a08028200b03028200a08030100604018100703028200a08014040604018100703018100604014040a08028201000628200a0804000c60401810100061810060404000ca08028200a12110500414030100818020600a1212060081803010041401050100062060081802820031302820100010c4c031302820081802060100042060081801c0c041401050100011050041401c0c081802060100002060081801410031301410100010c4c0313014100818020601000120600818040008414010501000110500414040008818020600c0401c0c0c0402c0c100042c0c0c04080010c0402c0c070301c0c1000040000c0802c0c0504014100c04040000c0402c0c200032c0c0c04014100504040000504014100a08040000a08040001000680000a08014100a0801c0c100041c0c10000141005040400010000180c1000040010908030101000530100a12180008a12130102000130100a12140014a121 (by decide +kernel)

def state241_39 : List Sig := [0xffffffffffffffff0000000000000000ffff0000ffff0000,input 6,input 4,input 7,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_39 : Impossible true (goalAt 241) 5 state241_39.toFinset :=
  node_ok cuts241 [⟨state241_14,exclude241_14⟩] 0x604028200a08018100a08018100604028200818028200313020600414020600818010500818024200313020600818010500414020600908028202000024200504024200908014100908014100504024200c0402c0c0c0402c0c0a08018100a08018100818010500818010500b03030100b03030100908014100908014100c080 (by decide +kernel)

def state241_40 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_40 : Impossible true (goalAt 241) 5 state241_40.toFinset :=
  node_ok cuts241 [⟨state241_35,exclude241_35⟩,⟨state241_15,exclude241_15⟩] 0x18100a08028200604028200c08018100a0802c0c0a08028200903020600a0800c4c081802060090800c4c0818010500818020600414020600c0801050081800c4c0818020600313024200a08080004908014100908030202000024200b030242009080280c0b03030100c04040000c04030200c080400107030 (by decide +kernel)

def state241_41 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_41 : Impossible true (goalAt 241) 6 state241_41.toFinset :=
  node_ok cuts241 [⟨state241_16,exclude241_16⟩,⟨state241_36,exclude241_36⟩,⟨state241_33,exclude241_33⟩,⟨state241_39,exclude241_39⟩,⟨state241_40,exclude241_40⟩] 0x100051c0c070302c0c0c08030202000430200c0802c0c070301c0c2000318484612140010c08030202000230200c08040010612118484703028200a08030200604030200703018100604030200a08028200b03018100604024040a08028200b03028200a0802404060401810100081810060404000ca08028201000828200a0804000c60401810061212060081803020041403020061211050041403020081802060100082060081802820031302820100010c4c031302820081802060100051050041402c0c081802060100012060081802c0c041401050100002060081802420031302420100010c4c0313024200818020601000110500414040008818020601000120600818040008414010501000040000c0401c0c0908024200c08040000c0801c0c200011c0c0c08024200908040000908024200a08040000a08040001000880000a0802420090802c0c100052c0c10000242009080400010000280c10000400145040 (by decide +kernel)

def state241_42 : List Sig := [0xaaaa0000ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa0000aaaa,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_42 : Impossible true (goalAt 241) 3 state241_42.toFinset :=
  node_ok cuts241 [] 0x30100c08030200503010500818020600414020600c080105008180141009080242005040242005040302009080206003130206009080 (by decide +kernel)

def state241_43 : List Sig := [0xaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa,input 0,input 6,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_43 : Impossible true (goalAt 241) 4 state241_43.toFinset :=
  node_ok cuts241 [⟨state241_42,exclude241_42⟩] 0x504024200908014100908030200504024200c04030200c0801c0c0818024200312120600414020600818010500818030200414020600313024202000024200a08018100a08028200604028200604030200a080 (by decide +kernel)

def state241_44 : List Sig := [0x5555000055555555555500005555555555550000555555555555000055550000,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_44 : Impossible true (goalAt 241) 3 state241_44.toFinset :=
  node_ok cuts241 [] 0x30100c08030200503014100908024200504024200c080141009080105008180206004140206004140302008180206003130242008180 (by decide +kernel)

def state241_45 : List Sig := [0xffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffff0000,input 4,input 6,input 7,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_45 : Impossible true (goalAt 241) 4 state241_45.toFinset :=
  node_ok cuts241 [⟨state241_44,exclude241_44⟩] 0x414020600818010500818030200414020600818024200313020602000020600818028200c04030200c080140c0504024200908014100908030200504024200312118100a08028200604028200604030200a080 (by decide +kernel)

def state241_46 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff0000000000000000,input 6,input 7,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_46 : Impossible true (goalAt 241) 5 state241_46.toFinset :=
  node_ok cuts241 [⟨state241_7,exclude241_7⟩,⟨state241_17,exclude241_17⟩,⟨state241_43,exclude241_43⟩,⟨state241_45,exclude241_45⟩] 0x2c0c0504014100c0402420090802c0c0908024200c0401410050401c0c0908024200c08014100c0801c0c0504014100c0802420090800c48481802060090800c4c090800c48431300c4c0908020600818028484414010500c04020600818028484818020600c04010500414018484818020600c08010500c08018484414010500c08020600818030100703030100b03030200c08030100c08030200b0301c0c0703024200a08024200312180004312124202000324200312128200a08020600a08020600313080000313020602000220600313028200a08030100604018100b03028200a08030100a08028200b03018100604030200a08028200703018100604030200604030200703028200a080 (by decide +kernel)

def state241_47 : List Sig := [0x5555555555555555555555555555555555555555555555550000000000000000,input 0,input 6,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_47 : Impossible true (goalAt 241) 5 state241_47.toFinset :=
  node_ok cuts241 [⟨state241_7,exclude241_7⟩] 0x604028200a08018100a08030200604028200908028200312124200504024200908014100908030200504024200c04030200c08018484111028200313028200312124200313024200313030100a12130100313030200612130200a08080000a0804000c90800c48490800c484c0402c0c0c04028484c0801c0c0c080184848180 (by decide +kernel)

def state241_48 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000,input 4,input 6,input 7,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_48 : Impossible true (goalAt 241) 5 state241_48.toFinset :=
  node_ok cuts241 [⟨state241_17,exclude241_17⟩] 0x604028200a08018100a0803020060402820081802820031302060041402060081801050081803020041402060081800c4c0313020600c04030200c0801c0c0110128200312128200b03030100b03030100703030200703030200a08080000a0804000c81800c4c081800c4c0c0402c0c0c0402c0c0c0801c0c0c0801c0c09080 (by decide +kernel)

def state241_49 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_49 : Impossible true (goalAt 241) 5 state241_49.toFinset :=
  node_ok cuts241 [] 0x14100908024200504024200c0801410090800c48490802420031212060090800c4c0818010500818020600414020600c0801050081800c4c081802060031302c0c0c0403020100061c0c090800c48490802820081800c4c0818028200604028200a08018100a08018100c080282010003 (by decide +kernel)

def state241_50 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_50 : Impossible true (goalAt 241) 6 state241_50.toFinset :=
  node_ok cuts241 [⟨state241_22,exclude241_22⟩,⟨state241_26,exclude241_26⟩,⟨state241_29,exclude241_29⟩,⟨state241_8,exclude241_8⟩,⟨state241_33,exclude241_33⟩,⟨state241_37,exclude241_37⟩,⟨state241_40,exclude241_40⟩,⟨state241_18,exclude241_18⟩,⟨state241_46,exclude241_46⟩,⟨state241_47,exclude241_47⟩,⟨state241_48,exclude241_48⟩,⟨state241_49,exclude241_49⟩] 0x1000518100604030100a08028201000628200a08030100604018101000428200a08030200604030201000618100604030200a0802820100068002e00084000ca08028201000628200a0804000d00064000d00062420090802820031212820200070c484312128200908024201000514100504030100908024202000624200908030100504014101000424200908030200504030202000514100504030200908024202000a0c48431214000090802420200042420090804000031210c48500062060081802820031302820200030c4c031302820081802060031212060081802420031302420031210c4c031302420081802060100051050041403010081802060200022060081803010041401050100042060081803020041403020200011050041403020081802060200090c4c031304000881802060200002060081804000831300c4c1000540010b03030101000530101000430200c080400150005400150005400147030 (by decide +kernel)

def state241_51 : List Sig := roots 241
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_51 : Impossible true (goalAt 241) 7 state241_51.toFinset :=
  node_ok cuts241 [⟨state241_9,exclude241_9⟩,⟨state241_19,exclude241_19⟩,⟨state241_27,exclude241_27⟩,⟨state241_30,exclude241_30⟩,⟨state241_38,exclude241_38⟩,⟨state241_41,exclude241_41⟩,⟨state241_50,exclude241_50⟩] 0x40014c0401c0c0c04040010b03030200c08080018c04030200c08040014b0301c0c070304000cb0301810060404000cc04028200a0804000cb03028200a0804000cc0401810060404000c703028200a0804000cc08018100c0804000c70301810060404000cc08028200a08040014b03014100504040000c04024200908080014b03024200908040000c04014100504040010703024200908040000c08014100c08080010703014100504040000c0802420090804000d00032420090804000ca0800c484a0804000e00010c48431214000ca08024200908040014a12110500414040008c0402060081808000ca12120600818040014c04010500414040010612120600818040008c08010500c08080008612110500414040008c0802060081804000d00032060081804000ca0800c4c0a0804000e00000c4c031304000ca0802060081804000031212060081804000890800c4c090804000431210c4c03130400009080206008180 (by decide +kernel)

theorem lower241 : Claim 241 8 :=
  fromSearch 6291460 (by decide +kernel) exclude241_51

def cuts194 : Cuts (goalAt 194) := []

def state194_0 : List Sig := roots 194
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude194_0 : Impossible true (goalAt 194) 3 state194_0.toFinset :=
  node_ok cuts194 [] 0x30100420230100820230200c08030100c08030200820210808420220808424010900c04020a00828020808828020a00c04010900424010808828020a00c08010900c08010808424010900c08020a008280 (by decide +kernel)

theorem lower194 : Claim 194 4 :=
  fromSearch 285212768 (by decide +kernel) exclude194_0

def cuts162 : Cuts (goalAt 162) := []

def state162_0 : List Sig := roots 162
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude162_0 : Impossible true (goalAt 162) 3 state162_0.toFinset :=
  node_ok cuts162 [] 0x28080220228080820228200a08028080a08028200820208808220220808222008880a02020a00828020808828020a00a02008880222008808828020a00a08008880a08008808222008880a08020a008280 (by decide +kernel)

theorem lower162 : Claim 162 4 :=
  fromSearch 269484112 (by decide +kernel) exclude162_0

def rule226_0 : {c : Cut // CutGood (goalAt 226) c} :=
  ruleFor 226 lower224 none (by decide +kernel)

def rule226_1 : {c : Cut // CutGood (goalAt 226) c} :=
  ruleFor 226 lower194 none (by decide +kernel)

def rule226_2 : {c : Cut // CutGood (goalAt 226) c} :=
  ruleFor 226 lower162 none (by decide +kernel)

def cuts226 : Cuts (goalAt 226) := [rule226_0,rule226_1,rule226_2]

def state226_0 : List Sig := roots 226
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude226_0 : Impossible true (goalAt 226) 5 state226_0.toFinset :=
  node_ok cuts226 [] 0x40008c04018080c04040008a02030200c08040008c04030200c08040008a02018080602040004a02018100604040004c04028200a08040004a02028200a08040004c04018100604040004602028200a08040004c08018100c08040004602018100604040004c08028200a08040000820210900424040000c04020a00828040000820220a00828040000c04010900424040000420220a00828040000c08010900c08040000420210900424040000c08020a00828040000220220a00828040000a08008880a08040000220208880222040000a08020a008280 (by decide +kernel)

theorem lower226 : Claim 226 6 :=
  fromSearch 286261328 (by decide +kernel) exclude226_0

theorem lower195 : Claim 195 5 :=
  fromLift 5 1 102 lower194 (by decide +kernel)

theorem lower163 : Claim 163 5 :=
  fromLift 5 1 1048663 lower162 (by decide +kernel)

def cuts98 : Cuts (goalAt 98) := []

def state98_0 : List Sig := roots 98
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude98_0 : Impossible true (goalAt 98) 3 state98_0.toFinset :=
  node_ok cuts98 [] 0x180802202180804202181006040180806040181004202088082202108082220088806020109004240108084240109006020088802220088084240109006040088806040088082220088806040109004240 (by decide +kernel)

theorem lower98 : Claim 98 4 :=
  fromSearch 17825872 (by decide +kernel) exclude98_0

theorem lower99 : Claim 99 5 :=
  fromLift 5 1 1048662 lower98 (by decide +kernel)

def rule227_0 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower226 none (by decide +kernel)

def rule227_1 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower225 none (by decide +kernel)

def rule227_2 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower193 none (by decide +kernel)

def rule227_3 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower195 none (by decide +kernel)

def rule227_4 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower163 none (by decide +kernel)

def rule227_5 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower99 none (by decide +kernel)

def rule227_6 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower224 none (by decide +kernel)

def rule227_7 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower194 none (by decide +kernel)

def rule227_8 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower162 none (by decide +kernel)

def rule227_9 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower98 none (by decide +kernel)

def cuts227 : Cuts (goalAt 227) := [rule227_0,rule227_1,rule227_2,rule227_3,rule227_4,rule227_5,rule227_6,rule227_7,rule227_8,rule227_9]

def state227_0 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc,input 7,input 6,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_0 : Impossible true (goalAt 227) 4 state227_0.toFinset :=
  node_ok cuts227 [] 0x28200c08018100a08018100a08028200604008884a08028201000720600a0800880c818020600c08010500818010500818020600414008884818020601000030100c08030200410318484a121 (by decide +kernel)

def state227_1 : List Sig := [0xffffffffffffffffcccccccccccccccc,input 7,input 6,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_1 : Impossible true (goalAt 227) 4 state227_1.toFinset :=
  node_ok cuts227 [] 0xa08030200604028200604028200a08018100818028200220320600818030200414020600414020600818010500e12130200c08028484604028200604028200414020600414020600222130200410330200c040 (by decide +kernel)

def state227_2 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_2 : Impossible true (goalAt 227) 4 state227_2.toFinset :=
  node_ok cuts227 [] 0xa08030200604028200604028200a08018100220328200a0800880c818028200220320600818020a00414020600414020600818010500410320600818040018c04030200c08008884222130200c08008884a121 (by decide +kernel)

def state227_3 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_3 : Impossible true (goalAt 227) 5 state227_3.toFinset :=
  node_ok cuts227 [⟨state227_0,exclude227_0⟩,⟨state227_1,exclude227_1⟩,⟨state227_2,exclude227_2⟩] 0xa12118100604030100a08028200a12128200a08030100604018101000228200a0801040c60401810100021810060401040ca08028200222128200a0804001c60401810022211810060404001ca08028200a12110500414030100818020600a12120600818030100414010500220320600818028201000628200220340008220328200818020600410320600818040018414010500410310500414040018818020600222120600818040000414020a00222110500414040000818020600c0401040cc04028485000828484c04080008c04028484410328485000140004c08030100222130100a12180004a12130102000030100a121088842221 (by decide +kernel)

def state227_4 : List Sig := [0xffffffffffffffff0000000000000000cccccccccccccccc,input 6,input 7,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_4 : Impossible true (goalAt 227) 4 state227_4.toFinset :=
  node_ok cuts227 [] 0x604028200a08018100a08018100604028200818028200220320600414020600818010500818010500414020600c04038484c04018484a08018100a08018100818010500818010500222130100810330100c080 (by decide +kernel)

def state227_5 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_5 : Impossible true (goalAt 227) 4 state227_5.toFinset :=
  node_ok cuts227 [] 0x604028200a08018100a08030200604028200220328200a0800880c818028200220320600414020600818010500818030200414020600810320600818040018222130100c04008884c04030200c080088846121 (by decide +kernel)

def state227_6 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_6 : Impossible true (goalAt 227) 5 state227_6.toFinset :=
  node_ok cuts227 [⟨state227_0,exclude227_0⟩,⟨state227_4,exclude227_4⟩,⟨state227_5,exclude227_5⟩] 0x100091848461212040cc08030202000230200c0802040c612118486000118484612108884c08030202000030200c08008884612108884612128200a08030200604030200612118100604030200a0802820100021810060402040ca08028201000228200a0802040c60401810022211810060404001ca08028200222128200a0804001c604018100612120600818030200414030200612110500414030200818020600220320600818028201000628200220340008220328200818020600810310500414040018818020600810320600818040018414010500222110500414040000818020600222120600818040000414010501000140004c040 (by decide +kernel)

def state227_7 : List Sig := [0x1111111111111111111111111111111111111111111111110000000000000000,input 6,input 7,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_7 : Impossible true (goalAt 227) 4 state227_7.toFinset :=
  node_ok cuts227 [] 0x604028200a08018100a08030200604028200220328200222128200222130100810330100222130200410330200c04030200c0801848481800880ca080206008280105008180206004140206004140302008180 (by decide +kernel)

def state227_8 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_8 : Impossible true (goalAt 227) 5 state227_8.toFinset :=
  node_ok cuts227 [⟨state227_0,exclude227_0⟩,⟨state227_2,exclude227_2⟩,⟨state227_5,exclude227_5⟩,⟨state227_7,exclude227_7⟩] 0x18100a08028200604028200c08018100a0800880ca0802820022030880ca08008884a08020a00222130102000230100222130202000130200222140006000008884818028200220320600414020600818010500818030200414020602000320600818040018a12130100c080400206121 (by decide +kernel)

def state227_9 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 1,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_9 : Impossible true (goalAt 227) 6 state227_9.toFinset :=
  node_ok cuts227 [⟨state227_3,exclude227_3⟩,⟨state227_6,exclude227_6⟩,⟨state227_8,exclude227_8⟩] 0x40024c04018484c04040020a12130200c08080008c04030200c08040020a12118484612140008a1211810060404001cc04028200a08040008a12128200a0804001cc04018100604040008612128200a0804001cc08018100c0804000861211810060404001cc08028200a08040004820308884222140004c04040004c04040004820380004810340004c04008884c04040004420308884222140004c08040004c08040004420380000410340004c08008884c0804000422034001c220340004a08008884a08040004220308884222140004a08040004a08040001000040000828040018a12110500414040018c04020600818040018a12120600818040018c04010500414040018612120600818040018c08010500c08040018612110500414040018c08020600818040018220320600818040018a08040018a08040018220340008220340018a080206008180 (by decide +kernel)

def state227_10 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 7,input 6,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_10 : Impossible true (goalAt 227) 4 state227_10.toFinset :=
  node_ok cuts227 [] 0x20a00818008884818020a00c08010900828010900828020a0042400880c828020a01000620600c0801050081801050081802060041400880c818020601000030100c08030200412110c0c8303 (by decide +kernel)

def state227_11 : List Sig := [0xffffffffffffffffffffffff00000000,input 7,input 6,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_11 : Impossible true (goalAt 227) 4 state227_11.toFinset :=
  node_ok cuts227 [] 0x828020600222120600828030200424020a00424020a00828010900818030200414020600414020600818010500412130200c08010484424020a00424020a00414020600414020600412130200412130200c040 (by decide +kernel)

def state227_12 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_12 : Impossible true (goalAt 227) 4 state227_12.toFinset :=
  node_ok cuts227 [] 0x828020600222120600828030200424020a00424020a00828010900222120a0082800888481802820041402060041402060081801050041212060081804001cc04030200c0800880c412130200c0800880ca021 (by decide +kernel)

def state227_13 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_13 : Impossible true (goalAt 227) 5 state227_13.toFinset :=
  node_ok cuts227 [⟨state227_10,exclude227_10⟩,⟨state227_11,exclude227_11⟩,⟨state227_12,exclude227_12⟩] 0x830310900424030100828020a00830320a00828030100424010901000720a00828020600222120601000208884222120600828020601000220a00828010484424010901000210900424010484828020a00220320a00828040018424010900220310900424040018828020a00a02110500414030100818020600a0212060081803010041401050041212060081804001c41401050041211050041404001c818020600220320600818040000414028200220310500414040000818020600c04010484c04028085000828084c04080008c0402808441211048500034000cc0803010022033010083038000483033010200003010083030880c8121 (by decide +kernel)

def state227_14 : List Sig := [0xffffffffffffffff0000000000000000ffffffff00000000,input 6,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_14 : Impossible true (goalAt 227) 4 state227_14.toFinset :=
  node_ok cuts227 [] 0x828020600222120600424020a00828010900828010900424020a00414020600818010500818010500414020600c04020484c04020484828010900828010900818010500818010500812130100812130100c080 (by decide +kernel)

def state227_15 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_15 : Impossible true (goalAt 227) 4 state227_15.toFinset :=
  node_ok cuts227 [] 0x828020600222120600424020a00828010900828030200424020a00222120a0082800888441402060081801050081803020041402060081212060081804001c812130100c0400880cc04030200c0800880c6021 (by decide +kernel)

def state227_16 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_16 : Impossible true (goalAt 227) 5 state227_16.toFinset :=
  node_ok cuts227 [⟨state227_10,exclude227_10⟩,⟨state227_14,exclude227_14⟩,⟨state227_15,exclude227_15⟩] 0x1000918084602120484c08030202000230200c08020484602118086000110c0c43030880cc08030202000030200c0800880c430310484430320a00828030200424030200430310900424030200828020a01000720a00828020600222120601000208884222120600828020601000210900424020484828020a01000220a00828020484424010900220310900424040018828020a00220320a0082804001842401090060212060081803020041403020060211050041403020081802060081211050041404001c81802060081212060081804001c41401050022031050041404000081802060022032060081804000041401050100034000cc040 (by decide +kernel)

def state227_17 : List Sig := [0x55555555000000005555555500000000555555550000000000000000,input 6,input 7,input 5,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_17 : Impossible true (goalAt 227) 4 state227_17.toFinset :=
  node_ok cuts227 [] 0x828008884222120a00424020a00828010900828030200424020a00a02130100812130100602130200412130200c04030200c08018084818008884828020600a080105008180206004140206004140302008180 (by decide +kernel)

def state227_18 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 5,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_18 : Impossible true (goalAt 227) 5 state227_18.toFinset :=
  node_ok cuts227 [⟨state227_10,exclude227_10⟩,⟨state227_12,exclude227_12⟩,⟨state227_15,exclude227_15⟩,⟨state227_17,exclude227_17⟩] 0x20a00222108884828020a00818008884818010900828020a00424020a00c08010900828008884828020a0022212820022033010200023010022033020200013020022034000e00000880c41402060081801050081803020041402060200032060081804001ca02130100c080400206021 (by decide +kernel)

def state227_19 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 5,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_19 : Impossible true (goalAt 227) 6 state227_19.toFinset :=
  node_ok cuts227 [⟨state227_13,exclude227_13⟩,⟨state227_16,exclude227_16⟩,⟨state227_18,exclude227_18⟩] 0x40024c04018084c04040020a02130200c08080008c04030200c08040020a02118084602140008830310900424040018c04020a00828040008830320a00828040018c04010900424040008430320a00828040018c08010900c08040008430310900424040018c08020a0082804000c220320a0082804000d00060888422214000c22030888422214000d000320a0082804001d000720a0082804001881800888481804001d000208884222140018818020a0081804000ca0210880ca0214000cc0404000cc0404000ca0218000481214000cc0400880cc0404000c60210880c60214000cc0804000cc0804000c60218000041214000cc0800880cc08040001000040000a0804001ca0211050041404001cc0402060081804001ca0212060081804001cc0401050041404001c60212060081804001cc08010500c0804001c60211050041404001cc080206008180 (by decide +kernel)

def state227_20 : List Sig := [0x5555555555555555555555555555555555555555555555554444444444444444,input 7,input 1,input 6,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_20 : Impossible true (goalAt 227) 4 state227_20.toFinset :=
  node_ok cuts227 [] 0x28200c08018100a08018100a08028200604030100c08030200612120a00a08008c84828020a00c08010900828010900828020a00424020600220328200818020600414030200818020600222120a008180105008180206004140 (by decide +kernel)

def state227_21 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff00000000cccccccc,input 7,input 1,input 6,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_21 : Impossible true (goalAt 227) 4 state227_21.toFinset :=
  node_ok cuts227 [] 0x20600c08010500818020600828008884818010500818020600414030100c08030200612120a00c08010900828010900828020a00424020600220320600a08028200604030200a08020a00232120a00a08018100a080282006040 (by decide +kernel)

def state227_22 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc,input 7,input 1,input 6,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_22 : Impossible true (goalAt 227) 5 state227_22.toFinset :=
  node_ok cuts227 [⟨state227_0,exclude227_0⟩,⟨state227_20,exclude227_20⟩,⟨state227_21,exclude227_21⟩] 0xa08030200604028200604028200a08018102000228200a0804000c818028200220320600818030200414020600818020a02000020600414020600818010502000120600818040000c04030200c08010c0c612120a00a08008c0c828020a00c08010900828010900828020a00424008c84a121 (by decide +kernel)

def state227_23 : List Sig := [0xffffffffffffffffcccccccccccccccc,input 7,input 1,input 6,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_23 : Impossible true (goalAt 227) 5 state227_23.toFinset :=
  node_ok cuts227 [⟨state227_1,exclude227_1⟩] 0xa08030200604028200604028200a08018100818028200220320600818030200414020600818020a02000020600414020600818010500e12130200c08028484828028200230320a00828030200424020a00424020a00828010900604028200604028200414020600414020600612130200430330200424020a00424020a00c040 (by decide +kernel)

def state227_24 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_24 : Impossible true (goalAt 227) 4 state227_24.toFinset :=
  node_ok cuts227 [] 0x28200828018100828018100a08028200424008c0ca08028200230320600a0800880c818020600828010500818010500818020600414010c0c818020600420310900828020a01000418484828020a008103284844240109004103 (by decide +kernel)

def state227_25 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_25 : Impossible true (goalAt 227) 5 state227_25.toFinset :=
  node_ok cuts227 [⟨state227_24,exclude227_24⟩] 0x28200604018100a08028200828018100828018100a08028200604018100a08028200424020600a0800880c818020600414010500818020600828010500818010500818020600414010500818020600414030200430320c0e000010c0c424010c0c42401040c830320a0082802040c424020a00828040010c040 (by decide +kernel)

def state227_26 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 1,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_26 : Impossible true (goalAt 227) 5 state227_26.toFinset :=
  node_ok cuts227 [⟨state227_24,exclude227_24⟩,⟨state227_2,exclude227_2⟩] 0x28200c08018100a08018100a08028200604008c0ca08028200230320600a0800880c818020600424080004818020600c08010500818010500818020600414010c0c818020600420310900a08008c0ca08020a0042402090200001090043031090042401040cc04030200c08040014612130200c08040004a121 (by decide +kernel)

def state227_27 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 1,input 6,input 0,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_27 : Impossible true (goalAt 227) 6 state227_27.toFinset :=
  node_ok cuts227 [⟨state227_3,exclude227_3⟩,⟨state227_22,exclude227_22⟩,⟨state227_23,exclude227_23⟩,⟨state227_25,exclude227_25⟩,⟨state227_26,exclude227_26⟩] 0xa12118100604030100a08028200a12128200a08030100604018101000428200a08010c0c604018101000218100604010c0ca08028201000228200a0804000c60401810100021810060404000ca08028200a12110500414030100818020600a12120600818030100414010500230320600818028201000628200230340008220328200818020600430320600818010808414010500430310500414010808818020601000120600818010901000110901000640006000010900818020601000620600818040000414010501000610500414040000818020600c04010c0cc04028485000428484c04080010c04028484430328485000140004c08020c0c424010900c04040004c04020c0e000320c0cc04010900424008c0c424010900a08040004a08008c0d000208c0ca08010900a08010c0d000410c0d00011090042404000500011040d000140010828030101000530100a12180008a12130102000130100a12140014a121 (by decide +kernel)

def state227_28 : List Sig := [0xffffffffffffffff0000000000000000cccccccccccccccc,input 6,input 1,input 7,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_28 : Impossible true (goalAt 227) 5 state227_28.toFinset :=
  node_ok cuts227 [⟨state227_4,exclude227_4⟩] 0x604028200a08018100a08018100604028200818028200220320600414020600818010500818020a02000020600818010500414020600828028200230320a00424020a00828010900828010900424020a00c04038484c04018484a08018100a08018100818010500818010500a12130100830330100828010900828010900c080 (by decide +kernel)

def state227_29 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 1,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_29 : Impossible true (goalAt 227) 5 state227_29.toFinset :=
  node_ok cuts227 [⟨state227_24,exclude227_24⟩,⟨state227_5,exclude227_5⟩] 0x18100a08028200604028200c08018100a08008c0ca08028200230320600a0800880c818020600828080004818010500818020600414020600c08010500818020c0c818020600820320a00a08008c0c828010900828030202000020a00830320a0082802040ca12130100c04040004c04030200c080400106121 (by decide +kernel)

def state227_30 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 1,input 7,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_30 : Impossible true (goalAt 227) 6 state227_30.toFinset :=
  node_ok cuts227 [⟨state227_25,exclude227_25⟩,⟨state227_6,exclude227_6⟩,⟨state227_22,exclude227_22⟩,⟨state227_28,exclude227_28⟩,⟨state227_29,exclude227_29⟩] 0x1000518484612120c0cc08030202000430200c08020c0c612118486000318484612140010c08030202000230200c08040010612118484612128200a08030200604030200612118100604030200a08028201000518100604020c0ca08028201000228200a08020c0c60401810100021810060404000ca08028201000228200a0804000c604018100612120600818030200414030200612110500414030200818020600230320600818028201000628200230340008220328200818020600830310500414020808818020600830320600818020808414010501000120600818020a01000120a01000640006000120a00818020601000610500414040000818020601000620600818040000414010501000140004c04010c0c828020a00c08040004c08010c0e000010c0cc08020a00828008c0c828020a00a08040004a08008c0d000208c0ca08020a00828020c0d000520c0d000120a0082804000500012040d0001400144240 (by decide +kernel)

def state227_31 : List Sig := [0x5555555555555555555555555555555555555555555555555555555500000000,input 7,input 5,input 6,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_31 : Impossible true (goalAt 227) 4 state227_31.toFinset :=
  node_ok cuts227 [] 0x20a00c08010900828020a00a08008c84828010900828020a00424030100c08030200612128200c08018100a08018100a08028200604020600222120a008180206004140302008180206002203282008180105008180206004140 (by decide +kernel)

def state227_32 : List Sig := [0x3333333333333333333333333333333333333333333333333333333300000000,input 7,input 5,input 6,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_32 : Impossible true (goalAt 227) 4 state227_32.toFinset :=
  node_ok cuts227 [] 0x20600c08010500818020600a0800880c818010500818020600414030100c08030200612128200c08018100a08018100a08028200604020600222120600828020a00424030200828020a00232128200828010900828020a004240 (by decide +kernel)

def state227_33 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 7,input 5,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_33 : Impossible true (goalAt 227) 5 state227_33.toFinset :=
  node_ok cuts227 [⟨state227_10,exclude227_10⟩,⟨state227_31,exclude227_31⟩,⟨state227_32,exclude227_32⟩] 0x828030200424020a00828028200232120a00424020a00828010902000220a00828040004818020a00222120600818030200414020600818028202000020600414020600818010502000120600818040000c04030200c08018484430328200c08018100a08018100a08028200604008c0c8303 (by decide +kernel)

def state227_34 : List Sig := [0xffffffffffffffffffffffff00000000,input 7,input 5,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_34 : Impossible true (goalAt 227) 5 state227_34.toFinset :=
  node_ok cuts227 [⟨state227_11,exclude227_11⟩] 0x828030200424020a00828028200232120a00424020a00828010900818020a00222120600818030200414020600818028202000020600414020600818010500612130200c08018484a08030200604028200604028200a08018100424020a00424020a00414020600414020600612130200612130200604028200604028200c040 (by decide +kernel)

def state227_35 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_35 : Impossible true (goalAt 227) 4 state227_35.toFinset :=
  node_ok cuts227 [] 0x20a00a08010900828010900828020a00424008c84828020a00232120600828008884818020600a08010500818010500818020600414018484818020600602118100a08028201000418484a080282008121184846040181004121 (by decide +kernel)

def state227_36 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_36 : Impossible true (goalAt 227) 5 state227_36.toFinset :=
  node_ok cuts227 [⟨state227_35,exclude227_35⟩] 0x20a00424010900828020a00a08010900828010900828020a00424010900828020a00424020600828008884818020600414010500818020600a08010500818010500818020600414010500818020600414030200612128486000018484604018484604010484a12128200a08020484604028200a08040010c040 (by decide +kernel)

def state227_37 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_37 : Impossible true (goalAt 227) 5 state227_37.toFinset :=
  node_ok cuts227 [⟨state227_35,exclude227_35⟩,⟨state227_12,exclude227_12⟩] 0x20a00604008c84828020a00c08010900828010900828020a00424008c84828020a00232120600828008884818020600604080004818020600c08010500818010500818020600414018484818020600602128200604028102000018100612118100604010484c04030200c08040014612130200c0804000ca121 (by decide +kernel)

def state227_38 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_38 : Impossible true (goalAt 227) 6 state227_38.toFinset :=
  node_ok cuts227 [⟨state227_13,exclude227_13⟩,⟨state227_33,exclude227_33⟩,⟨state227_34,exclude227_34⟩,⟨state227_36,exclude227_36⟩,⟨state227_37,exclude227_37⟩] 0x830310900424030100828020a00830320a00828030100424010901000420a00828018484424010901000210900424018484828020a01000320a00828018100232118101000208c84232118100828020a01000220a00828040004424010901000210900424040004828020a00a12110500414030100818020600a12120600818030100414010500232120600818020a01000720a00232140008222120a0081802060061212060081801808041401050061211050041401808081802060100032060081801810100031810100074000e000018100818020601000720600818040000414010501000710500414040000818020600c04018484c04028485000428484c04080010c0402848461211848500034000cc08028484604018100c0404000cc04028486000328484c0401810060401848500041848500031810060404000d000310485000340010a080301010005301008303800088303301020001301008303400148303 (by decide +kernel)

def state227_39 : List Sig := [0xffffffffffffffff0000000000000000ffffffff00000000,input 6,input 5,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_39 : Impossible true (goalAt 227) 5 state227_39.toFinset :=
  node_ok cuts227 [⟨state227_14,exclude227_14⟩] 0x424020a00828010900828028200232120a00828010900424020a00818020a00222120600414020600818010500818028202000020600818010500414020600604028200a08018100a08018100604028200c04028484c04028484828010900828010900818010500818010500a12130100a12130100a08018100a08018100c080 (by decide +kernel)

def state227_40 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_40 : Impossible true (goalAt 227) 5 state227_40.toFinset :=
  node_ok cuts227 [⟨state227_35,exclude227_35⟩,⟨state227_15,exclude227_15⟩] 0x20a00a08008c84828010900828020a00424020a00c08010900828008c84828020a00232120600828008884818020600a08080004818010500818020600414020600c08010500818028484818020600a02118100a08030202000028200a12128200a08020484a12130100c0404000cc04030200c080400106121 (by decide +kernel)

def state227_41 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_41 : Impossible true (goalAt 227) 6 state227_41.toFinset :=
  node_ok cuts227 [⟨state227_36,exclude227_36⟩,⟨state227_16,exclude227_16⟩,⟨state227_33,exclude227_33⟩,⟨state227_39,exclude227_39⟩,⟨state227_40,exclude227_40⟩] 0x1000518484612128484c08030202000430200c08028484612118486000310c0c430340010c08030202000230200c08040010430310c0c430320a00828030200424030200430310900424030200828020a01000510900424028484828020a01000220a00828028484424010901000320a00828028200232128201000208c84232128200828020a01000210900424040004828020a01000220a00828040004424010900612120600818030200414030200612110500414030200818020600232120600818020a01000720a00232140008222120a00818020600a12110500414028080818020600a1212060081802808041401050100032060081802820100032820100074000e00012820081802060100071050041404000081802060100072060081804000041401050100034000cc04018484a08028200c0804000cc08018486000018484c08028200a08028485000528485000328200a0804000d0003204850003400146040 (by decide +kernel)

def state227_42 : List Sig := [0xdddddddd00000000dddddddd00000000dddddddd00000000cccccccc,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_42 : Impossible true (goalAt 227) 3 state227_42.toFinset :=
  node_ok cuts227 [] 0x30100c08030200412110900828020a00424020a00c08010900828010500818020600414020600414030200818020600222120a008180 (by decide +kernel)

def state227_43 : List Sig := [0xddddddddddddddddddddddddddddddddddddddddddddddddcccccccccccccccc,input 1,input 6,input 7,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_43 : Impossible true (goalAt 227) 4 state227_43.toFinset :=
  node_ok cuts227 [⟨state227_42,exclude227_42⟩] 0x604028200a08018100a08030200604028200c04030200c08018484828028200220320a00424020a00828010900828030200424020a002221206020000282008180105008180206004140206004140302008180 (by decide +kernel)

def state227_44 : List Sig := [0x3333333311111111333333331111111133333333111111113333333300000000,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_44 : Impossible true (goalAt 227) 3 state227_44.toFinset :=
  node_ok cuts227 [] 0x30100c08030200602118100a08028200604028200c08018100a080105008180206004140206004140302008180206002221282008180 (by decide +kernel)

def state227_45 : List Sig := [0xffffffff55555555ffffffff55555555ffffffff55555555ffffffff00000000,input 5,input 6,input 7,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_45 : Impossible true (goalAt 227) 4 state227_45.toFinset :=
  node_ok cuts227 [⟨state227_44,exclude227_44⟩] 0x424020a00828010900828030200424020a00828028200222120a02000020600828020600c04030200c08018084604028200a08018100a080302006040282002203105008180206004140206004140302008180 (by decide +kernel)

def state227_46 : List Sig := [0x5555555555555555555555555555555555555555555555550000000000000000,input 6,input 7,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_46 : Impossible true (goalAt 227) 5 state227_46.toFinset :=
  node_ok cuts227 [⟨state227_7,exclude227_7⟩,⟨state227_17,exclude227_17⟩,⟨state227_43,exclude227_43⟩,⟨state227_45,exclude227_45⟩] 0x28484604018100c04028200a08028484a08028200c04018100604018484a08028200c08018100c08018484604018100c08028200a0800880c828020a00a08008884a0800880c222108884a08020a00828020c0c424010900c04020a00828020c0c828020a00c04010900424010c0c828020a00c08010900c08010c0c424010900c08020a00828030100612130100a12130200c08030100c08030200a12118484612128200818020600220380004220328202000328200220320600818020a00818020600222180000222120a02000220a00222120600818030100414010500a12120600818030100818020600a121105004140302008180206006121105004140302004140302006121206008180 (by decide +kernel)

def state227_47 : List Sig := [0x5555555555555555555555555555555555555555555555550000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_47 : Impossible true (goalAt 227) 5 state227_47.toFinset :=
  node_ok cuts227 [] 0x18100a08028200604028200c08018100a0800880ca08028200220320a00a08008884828010900828020a00424020a00c08010900828008884828020a00222128484c0403020100081848481800880ca08020600818008884828020600414020600818010500818010500c080206010000 (by decide +kernel)

def state227_48 : List Sig := [0x3333333333333333333333333333333333333333333333330000000000000000,input 1,input 6,input 7,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_48 : Impossible true (goalAt 227) 5 state227_48.toFinset :=
  node_ok cuts227 [⟨state227_7,exclude227_7⟩] 0x604028200a08018100a08030200604028200818028200220320600414020600818010500818030200414020600818008880222120600c04030200c08010c0c230328200232128200232130100830330100232130200430330200a08008c0ca08008c0c818080000818040000c04028484c04020c0cc08018484c08010c0c8280 (by decide +kernel)

def state227_49 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff0000000000000000,input 5,input 6,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_49 : Impossible true (goalAt 227) 5 state227_49.toFinset :=
  node_ok cuts227 [⟨state227_17,exclude227_17⟩] 0x424020a00828010900828030200424020a00828008c84232120a00818020a00222120600414020600818010500818030200414020600818008808220320600c04030200c08018484a12130100a12130100612130200612130200828008c84828008c84818080000818040000c04028484c04028484c08018484c08018484a080 (by decide +kernel)

def state227_50 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_50 : Impossible true (goalAt 227) 6 state227_50.toFinset :=
  node_ok cuts227 [⟨state227_8,exclude227_8⟩,⟨state227_18,exclude227_18⟩,⟨state227_22,exclude227_22⟩,⟨state227_26,exclude227_26⟩,⟨state227_29,exclude227_29⟩,⟨state227_33,exclude227_33⟩,⟨state227_37,exclude227_37⟩,⟨state227_40,exclude227_40⟩,⟨state227_46,exclude227_46⟩,⟨state227_47,exclude227_47⟩,⟨state227_48,exclude227_48⟩,⟨state227_49,exclude227_49⟩] 0x1000518100604030100a08028202000728200a08030100604018101000428200a08030200604030202000618100604030200a08028202000b08c0c23034000ca08028202000528200a0804000c230308c0c230320a00828028200232128200230308c84232128200828020a01000510900424030100828020a02000420a00828030100424010901000420a00828030200424030202000310900424030200828020a02000a08c84232140004828020a02000220a00828040004232108c84230320600818028201000828200230380004220328200818020600232120600818020a01000820a00232180000222120a00818020601000510500414030100818020601000820600818030100414010501000420600818030200414030201000810500414030200818020601000880026000840000818020601000820600818040001000840001000440010a12130101000530101000430200c080400110004400110004400146121 (by decide +kernel)

def state227_51 : List Sig := roots 227
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_51 : Impossible true (goalAt 227) 7 state227_51.toFinset :=
  node_ok cuts227 [⟨state227_9,exclude227_9⟩,⟨state227_19,exclude227_19⟩,⟨state227_27,exclude227_27⟩,⟨state227_30,exclude227_30⟩,⟨state227_38,exclude227_38⟩,⟨state227_41,exclude227_41⟩,⟨state227_50,exclude227_50⟩] 0x40014c04018484c04040010a12130200c08080018c04030200c08040010a12118484612140014a1211810060404000cc04028200a08080014a12128200a0804000cc04018100604040010612128200a0804000cc08018100c0808001061211810060404000cc08028200a08040014830310900424040004c04020a0082808000c830320a00828040004c04010900424040010430320a00828040004c08010900c08080008430310900424040004c08020a0082804000c230320a00828040004a08008c84a08040008230308c84232140004a08020a00828040000a12110500414040000c04020600818040000a12120600818040000c04010500414040000612120600818040000c08010500c08040000612110500414040000c08020600818040000230320600818040000a08040000a08040000230380004220340000a080206008180400002321206008180400008280400008280400002321800002221400008280206008180 (by decide +kernel)

theorem lower227 : Claim 227 8 :=
  fromSearch 1048662 (by decide +kernel) exclude227_51

theorem lower210 : Claim 210 5 :=
  fromLift 5 2 285605984 lower208 (by decide +kernel)

theorem lower147 : Claim 147 5 :=
  fromLift 5 2 116 lower145 (by decide +kernel)

theorem lower83 : Claim 83 5 :=
  fromLift 5 2 100 lower81 (by decide +kernel)

def rule211_0 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower209 none (by decide +kernel)

def rule211_1 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower195 none (by decide +kernel)

def rule211_2 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower194 none (by decide +kernel)

def rule211_3 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower210 none (by decide +kernel)

def rule211_4 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower147 none (by decide +kernel)

def rule211_5 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower83 none (by decide +kernel)

def rule211_6 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower208 none (by decide +kernel)

def rule211_7 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower81 none (by decide +kernel)

def rule211_8 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower145 none (by decide +kernel)

def rule211_9 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower193 none (by decide +kernel)

def cuts211 : Cuts (goalAt 211) := [rule211_0,rule211_1,rule211_2,rule211_3,rule211_4,rule211_5,rule211_6,rule211_7,rule211_8,rule211_9]

def state211_0 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 6,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_0 : Impossible true (goalAt 211) 4 state211_0.toFinset :=
  node_ok cuts211 [] 0x24200c08014100908014100908024200504004c4890802420100022060090800440c818020600c08010500818010500818020600414004c48818020601000030100c080302004103144489112 (by decide +kernel)

def state211_1 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 6,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_1 : Impossible true (goalAt 211) 4 state211_1.toFinset :=
  node_ok cuts211 [] 0x908030200504024200504024200908014100818024200110320600818030200414020600414020600818010500d11230200c08024448504024200504024200414020600414020600131230200410330200c040 (by decide +kernel)

def state211_2 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_2 : Impossible true (goalAt 211) 4 state211_2.toFinset :=
  node_ok cuts211 [] 0x90803020050402420050402420090801410011032420090800440c828024200110320a00818020600414020a00414020a00828010500410320a00828040018c04030200c08004c48131230200c08004c489212 (by decide +kernel)

def state211_3 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 6,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_3 : Impossible true (goalAt 211) 5 state211_3.toFinset :=
  node_ok cuts211 [⟨state211_0,exclude211_0⟩,⟨state211_1,exclude211_1⟩,⟨state211_2,exclude211_2⟩] 0x92121410050403010090802420092122420090803010050401410100022420090801040c50401410100021410050401040c908024200131224200908040008504014100131214100504040008908024200921210500414030100828020a00921220a00828030100414010500110320a00828024201000624200110340008110324200828020a00410320a00828040018414010500410310500414040018828020a00131220a00818040000414020600131210500414040000828020a00c0401040cc04024849000824848c04080008c0402484841032484900034000cc08030100131230100921280004911230102000030100921204c481312 (by decide +kernel)

def state211_4 : List Sig := [0xffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa,input 6,input 7,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_4 : Impossible true (goalAt 211) 4 state211_4.toFinset :=
  node_ok cuts211 [] 0x504024200908014100908014100504024200818024200110320600414020600818010500818010500414020600c04034448c04014448908014100908014100818010500818010500131230100810330100c080 (by decide +kernel)

def state211_5 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_5 : Impossible true (goalAt 211) 4 state211_5.toFinset :=
  node_ok cuts211 [] 0x50402420090801410090803020050402420011032420090800440c818024200110320600414020600818010900818030200424020600810320600818040018131230100c04004c48c04030200c08004c485212 (by decide +kernel)

def state211_6 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_6 : Impossible true (goalAt 211) 5 state211_6.toFinset :=
  node_ok cuts211 [⟨state211_0,exclude211_0⟩,⟨state211_4,exclude211_4⟩,⟨state211_5,exclude211_5⟩] 0x100071484852122040cc08030202000230200c0802040c52121484a000114848511204c48c08030202000030200c08004c48521204c4852122420090803020050403020052121410050403020090802420100021410050402040c90802420100022420090802040c50401410013121410050404000890802420013122420090804000850401410052122060081803020042403020052121090042403020081802060011032060081802420100062420011034000811032420081802060081031090042404001881802060081032060081804001842401090013121090041404000081802060013122060081804000042401090100034000cc040 (by decide +kernel)

def state211_7 : List Sig := [0x1111111111111111111111111111111111111111111111110000000000000000,input 6,input 7,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_7 : Impossible true (goalAt 211) 4 state211_7.toFinset :=
  node_ok cuts211 [] 0x504024200908014100908030200504024200110324200131224200131230100810330100131230200410330200c04030200c0801484882800440c908020a00818010900828020a00424020a004240302008280 (by decide +kernel)

def state211_8 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_8 : Impossible true (goalAt 211) 5 state211_8.toFinset :=
  node_ok cuts211 [⟨state211_0,exclude211_0⟩,⟨state211_2,exclude211_2⟩,⟨state211_5,exclude211_5⟩,⟨state211_7,exclude211_7⟩] 0x14100908024200504024200c0801410090800440c90802420011030440c908004c4890802060013123010200023010013123020200013020013124000e000004c48828024200110320a00424020a00828010900828030200424020a02000320a00828040018921230100c0804001c5212 (by decide +kernel)

def state211_9 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_9 : Impossible true (goalAt 211) 6 state211_9.toFinset :=
  node_ok cuts211 [⟨state211_3,exclude211_3⟩,⟨state211_6,exclude211_6⟩,⟨state211_8,exclude211_8⟩] 0x4001cc04014848c04040020921230200c08080008c04030200c0804001c921214848521240008921214100504040008c04024200908040008921224200908040008c04014100504040008521224200908040008c08014100c08040008521214100504040008c0802420090804000c810304c4813124000cc0404000cc0404000c81038000481034000cc04004c48c0404000c410304c4813124000cc0804000cc0804000c41038000041034000cc08004c48c0804000c11034000811034000c908004c4890804000c110304c4813124000c90804000c908040001000040000818040018921210900424040018c04020a00828040018921220a00828040018c04010900424040018521220a00828040018c08010900c08040018521210900424040018c08020a00828040018110320a00828040018908040018908040018110340008110340018908020a008280 (by decide +kernel)

def state211_10 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,input 7,input 6,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_10 : Impossible true (goalAt 211) 4 state211_10.toFinset :=
  node_ok cuts211 [] 0x20600828004c48818020600c0801050081801050081802060041400440c818020601000620a00c08010900828010900828020a0042400440c828020a01000030100c08030200421210c0c8303 (by decide +kernel)

def state211_11 : List Sig := [0xffffffffffffffffffff0000ffff0000,input 7,input 6,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_11 : Impossible true (goalAt 211) 4 state211_11.toFinset :=
  node_ok cuts211 [] 0x818020a00131220600818030200414020600414020600818010500828030200424020a00424020a00828010900421230200c08010848414020600414020600424020a00424020a00421230200421230200c040 (by decide +kernel)

def state211_12 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_12 : Impossible true (goalAt 211) 4 state211_12.toFinset :=
  node_ok cuts211 [] 0x818020a00131220600818030200414020600414020600818010500131220600818004c48828024200424020a00424020a00828010900421220a00828040024c04030200c0800440c421230200c0800440c9012 (by decide +kernel)

def state211_13 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_13 : Impossible true (goalAt 211) 5 state211_13.toFinset :=
  node_ok cuts211 [⟨state211_10,exclude211_10⟩,⟨state211_11,exclude211_11⟩,⟨state211_12,exclude211_12⟩] 0x830310500414030100818020600830320600818030100414010501000220600818020a00131220a01000204c48131220a00818020601000220600818010848414010501000210500414010848818020600110320600818040018414010500110310500414040018818020600901210900424030100828020a00901220a00828030100424010900421220a00828040024424010900421210900424040024828020a00110320a00828040000424024200110310900424040000828020a00c04010848c04024049000824048c04080008c04024048421210849000140004c0803010011033010083038000483033010200003010083030440c8212 (by decide +kernel)

def state211_14 : List Sig := [0xffffffffffffffff0000000000000000ffff0000ffff0000,input 6,input 7,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_14 : Impossible true (goalAt 211) 4 state211_14.toFinset :=
  node_ok cuts211 [] 0x818020a00131220600414020600818010500818010500414020600424020a00828010900828010900424020a00c04020848c04020848818010500818010500828010900828010900821230100821230100c080 (by decide +kernel)

def state211_15 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_15 : Impossible true (goalAt 211) 4 state211_15.toFinset :=
  node_ok cuts211 [] 0x818020a00131220600414020600818010500818030200414020600131220600818004c48424020a00828010900828030200424020a00821220a00828040024821230100c0400440cc04030200c0800440c5012 (by decide +kernel)

def state211_16 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_16 : Impossible true (goalAt 211) 5 state211_16.toFinset :=
  node_ok cuts211 [⟨state211_10,exclude211_10⟩,⟨state211_14,exclude211_14⟩,⟨state211_15,exclude211_15⟩] 0x1000714048501220848c08030202000230200c0802084850121404a000110c0c43030440cc08030202000030200c0800440c430310848430320600818030200414030200430310500414030200818020601000220600818020a00131220a01000204c48131220a00818020601000210500414020848818020601000220600818020848414010500110310500414040018818020600110320600818040018414010500501220a00828030200424030200501210900424030200828020a00821210900424040024828020a00821220a00828040024424010900110310900424040000828020a00110320a00828040000424010901000140004c040 (by decide +kernel)

def state211_17 : List Sig := [0x333300003333000033330000333300003333000033330000000000000000,input 6,input 7,input 4,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_17 : Impossible true (goalAt 211) 4 state211_17.toFinset :=
  node_ok cuts211 [] 0x818004c48131220600414020600818010500818030200414020600901230100821230100501230200421230200c04030200c08014048818004c48818020a00908010900828020a00424020a004240302008280 (by decide +kernel)

def state211_18 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 4,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_18 : Impossible true (goalAt 211) 5 state211_18.toFinset :=
  node_ok cuts211 [⟨state211_10,exclude211_10⟩,⟨state211_12,exclude211_12⟩,⟨state211_15,exclude211_15⟩,⟨state211_17,exclude211_17⟩] 0x20600131204c48818020600828004c48818010500818020600414020600c08010500818004c4881802060013122420011033010200023010011033020200013020011034000600000440c424020a00828010900828030200424020a02000320a00828040024901230100c0804001c5012 (by decide +kernel)

def state211_19 : List Sig := [0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 4,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_19 : Impossible true (goalAt 211) 6 state211_19.toFinset :=
  node_ok cuts211 [⟨state211_13,exclude211_13⟩,⟨state211_16,exclude211_16⟩,⟨state211_18,exclude211_18⟩] 0x4001cc04014048c04040020901230200c08080008c04030200c0804001c901214048501240008830310500414040018c04020600818040008830320600818040018c04010500414040008430320600818040018c08010500c08040008430310500414040018c08020600818040004110320600818040005000604c48131240004110304c48131240005000120600818040009000220600818040018828004c48828040009000204c4813124001882802060081804000490120440c901240004c04040004c04040004901280004821240004c0400440cc0404000450120440c501240004c08040004c08040004501280000421240004c0800440cc08040001000040000908040024901210900424040024c04020a00828040024901220a00828040024c04010900424040024501220a00828040024c08010900c08040024501210900424040024c08020a008280 (by decide +kernel)

def state211_20 : List Sig := [0x3333333333333333333333333333333333333333333333332222222222222222,input 7,input 0,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_20 : Impossible true (goalAt 211) 4 state211_20.toFinset :=
  node_ok cuts211 [] 0x24200c08014100908014100908024200504030100c08030200521220600908004c48818020600c08010500818010500818020600414020a00110324200828020a00424030200828020600131220600828010900828020a004240 (by decide +kernel)

def state211_21 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaa,input 7,input 0,input 6,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_21 : Impossible true (goalAt 211) 4 state211_21.toFinset :=
  node_ok cuts211 [] 0x20a00c08010900828010900828020a00424030100c08030200521220600828004c48818020600c08010500818010500818020600414020a00110320a009080242005040302009080206001312206009080141009080242005040 (by decide +kernel)

def state211_22 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 0,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_22 : Impossible true (goalAt 211) 5 state211_22.toFinset :=
  node_ok cuts211 [⟨state211_0,exclude211_0⟩,⟨state211_20,exclude211_20⟩,⟨state211_21,exclude211_21⟩] 0x908030200504024200504024200908014102000224200908040004828024200110320a00828030200424020a00424020a00828010902000120a00828040000c04030200c08010c0c521220600908004c0c818020600828080000818020600c08010500818010500818020600414004c489212 (by decide +kernel)

def state211_23 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 0,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_23 : Impossible true (goalAt 211) 5 state211_23.toFinset :=
  node_ok cuts211 [⟨state211_1,exclude211_1⟩] 0x908030200504024200504024200908014100828024200110320a00828030200424020a00424020a00828010900d21230200c08024848818024200130320600818020a02000020600818030200414020600414020600818010500504024200504024200424020a00424020a00521230200430330200414020600414020600c040 (by decide +kernel)

def state211_24 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_24 : Impossible true (goalAt 211) 4 state211_24.toFinset :=
  node_ok cuts211 [] 0x24200818014100818014100908024200414004c0c908024200130320a0090800440c828020a00818010900818010900828020a00414010c0c828020a004103105008180206010004148488180206008203248484140105004203 (by decide +kernel)

def state211_25 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_25 : Impossible true (goalAt 211) 5 state211_25.toFinset :=
  node_ok cuts211 [⟨state211_24,exclude211_24⟩] 0x24200504014100908024200818014100818014100908024200504014100908024200414020a0090800440c828020a00424010900828020a00818010900818010900828020a00424010900828020a00414030200430320c0e000010c0c414010c0c41401080c83032060081802080c414020600818040010c040 (by decide +kernel)

def state211_26 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_26 : Impossible true (goalAt 211) 5 state211_26.toFinset :=
  node_ok cuts211 [⟨state211_24,exclude211_24⟩,⟨state211_2,exclude211_2⟩] 0x24200c08014100908014100908024200504004c0c908024200130320a0090800440c828020a00c08010900828010900828020a00424010c0c828020a00410310500908004c0c90801050082808000482802060041402050200001050043031050041401080cc04030200c08040014521230200c0804000c9212 (by decide +kernel)

def state211_27 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 6,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_27 : Impossible true (goalAt 211) 6 state211_27.toFinset :=
  node_ok cuts211 [⟨state211_3,exclude211_3⟩,⟨state211_22,exclude211_22⟩,⟨state211_23,exclude211_23⟩,⟨state211_25,exclude211_25⟩,⟨state211_26,exclude211_26⟩] 0x921214100504030100908024200921224200908030100504014101000424200908010c0c504014101000214100504010c0c908024201000224200908040004504014101000214100504040004908024200921210900424030100828020a00921220a00828030100424010900130320a00828024201000624200130340008110324200828020a00430320a00828010404424010900430310900424010404828020a01000620a00828040000424010901000610900424040000828020a00c04010c0cc04024849000424848c04080010c0402484843032484900044000cc08020c0c414010500c0404000cc04020c0e000320c0cc04010500414004c0c41401050090804000c908004c0d000204c0c90801050090804000c41401050082804000c82804000d000680000828010500828010c0d000410c0d00031050041404001100041080d0004400108180301010005301009212800089212301020001301009212400149212 (by decide +kernel)

def state211_28 : List Sig := [0xffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa,input 6,input 0,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_28 : Impossible true (goalAt 211) 5 state211_28.toFinset :=
  node_ok cuts211 [⟨state211_4,exclude211_4⟩] 0x504024200908014100908014100504024200828024200110320a00424020a00828010900828010900424020a00818024200130320600818020a02000020600414020600818010500818010500414020600c04034848c04014848908014100908014100828010900828010900921230100830330100818010500818010500c080 (by decide +kernel)

def state211_29 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_29 : Impossible true (goalAt 211) 5 state211_29.toFinset :=
  node_ok cuts211 [⟨state211_24,exclude211_24⟩,⟨state211_5,exclude211_5⟩] 0x14100908024200504024200c08014100908004c0c908024200130320a0090800440c828010900828020a00424020a00c08010900828020c0c828020a00810320600908004c0c81802060082808000481801050081803020200002060083032060081802080c921230100c04040010c04030200c080400105212 (by decide +kernel)

def state211_30 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_30 : Impossible true (goalAt 211) 6 state211_30.toFinset :=
  node_ok cuts211 [⟨state211_6,exclude211_6⟩,⟨state211_25,exclude211_25⟩,⟨state211_22,exclude211_22⟩,⟨state211_28,exclude211_28⟩,⟨state211_29,exclude211_29⟩] 0x1000514848521220c0cc08030202000430200c08020c0c52121484a000314848521240010c08030202000230200c08040010521214848521224200908030200504030200521214100504030200908024201000514100504020c0c908024201000224200908020c0c504014101000214100504040004908024201000224200908040004504014100521220a00828030200424030200521210900424030200828020a00130320a00828024201000624200130340008110324200828020a00830310900424020404828020a00830320a00828020404424010901000610900424040000828020a01000620a0082804000042401090100034000cc04010c0c818020600c0804000cc08010c0e000110c0cc08020600818004c0c81802060090804000c908004c0d000204c0c90802060081804000c81802060082804000c82804000d000680000828020600818020c0d000520c0d00032060081804000d00032080d0003400144140 (by decide +kernel)

def state211_31 : List Sig := [0x5555555555555555555555555555555555555555555555555555000055550000,input 7,input 4,input 6,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_31 : Impossible true (goalAt 211) 4 state211_31.toFinset :=
  node_ok cuts211 [] 0x20a00c08010900828020a0090800440c828010900828020a00424030100c08030200521224200c08014100908014100908024200504020600131220a008180206004140302008180206001312242008180105008180206004140 (by decide +kernel)

def state211_32 : List Sig := [0x3333333333333333333333333333333333333333333333333333000033330000,input 7,input 4,input 6,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_32 : Impossible true (goalAt 211) 4 state211_32.toFinset :=
  node_ok cuts211 [] 0x20600c08010500818020600908004c48818010500818020600414030100c08030200521224200c08014100908014100908024200504020600131220600828020a00424030200828020a00110324200828010900828020a004240 (by decide +kernel)

def state211_33 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,input 7,input 4,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_33 : Impossible true (goalAt 211) 5 state211_33.toFinset :=
  node_ok cuts211 [⟨state211_10,exclude211_10⟩,⟨state211_31,exclude211_31⟩,⟨state211_32,exclude211_32⟩] 0x828030200424020a00828024202000020a00424020a00828010902000220a00828040000818020a0013122060081803020041402060081802420013122060041402060081801050200012060081804000cc04030200c08014848430324200c08014100908014100908024200504004c0c8303 (by decide +kernel)

def state211_34 : List Sig := [0xffffffffffffffffffff0000ffff0000,input 7,input 4,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_34 : Impossible true (goalAt 211) 5 state211_34.toFinset :=
  node_ok cuts211 [⟨state211_11,exclude211_11⟩] 0x828030200424020a00828024202000020a00424020a00828010900818020a00131220600818030200414020600818024200131220600414020600818010500521230200c08014848908030200504024200504024200908014100424020a00424020a00414020600414020600521230200521230200504024200504024200c040 (by decide +kernel)

def state211_35 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_35 : Impossible true (goalAt 211) 4 state211_35.toFinset :=
  node_ok cuts211 [] 0x20a00908010900828010900828020a00424014848828020a00501220600828004c48818020600908010500818010500818020600414004c488180206001312141009080242010004148489080242008212148485040141004212 (by decide +kernel)

def state211_36 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_36 : Impossible true (goalAt 211) 5 state211_36.toFinset :=
  node_ok cuts211 [⟨state211_35,exclude211_35⟩] 0x20a00424010900828020a00908010900828010900828020a00424010900828020a00424020600828004c4881802060041401050081802060090801050081801050081802060041401050081802060041403020052122484a000014848504014848504010848921224200908020848504024200908040010c040 (by decide +kernel)

def state211_37 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_37 : Impossible true (goalAt 211) 5 state211_37.toFinset :=
  node_ok cuts211 [⟨state211_35,exclude211_35⟩,⟨state211_12,exclude211_12⟩] 0x20a00504080004828020a00c08010900828010900828020a00424014848828020a00501220600828004c48818020600504004c48818020600c08010500818010500818020600414004c48818020600131224200504024102000014100521214100504010848c04030200c08040014521230200c080400049212 (by decide +kernel)

def state211_38 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_38 : Impossible true (goalAt 211) 6 state211_38.toFinset :=
  node_ok cuts211 [⟨state211_13,exclude211_13⟩,⟨state211_33,exclude211_33⟩,⟨state211_34,exclude211_34⟩,⟨state211_36,exclude211_36⟩,⟨state211_37,exclude211_37⟩] 0x921210900424030100828020a00921220a00828030100424010900521220a00828014040424010900521210900424014040828020a01000120a00828014101000114101000940006000014100828020a01000920a00828040000424010901000910900424040000828020a00830310500414030100818020600830320600818030100414010501000220600818020a00131220a01000204c48131220a00818020601000420600818014848414010501000210500414014848818020601000120600818014100131214101000204c4813121410081802060100022060081804000c41401050100021050041404000c818020600c04014848c04024849000424848c04080010c04024848521214849000140004c08024848504014100c04040004c0402484a000324848c040141005040148490004148490001141005040400050001108490001400109080301010005301008303800088303301020001301008303400148303 (by decide +kernel)

def state211_39 : List Sig := [0xffffffffffffffff0000000000000000ffff0000ffff0000,input 6,input 4,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_39 : Impossible true (goalAt 211) 5 state211_39.toFinset :=
  node_ok cuts211 [⟨state211_14,exclude211_14⟩] 0x424020a00828010900828024202000020a00828010900424020a00818020a00131220600414020600818010500818024200131220600818010500414020600504024200908014100908014100504024200c04024848c04024848828010900828010900818010500818010500921230100921230100908014100908014100c080 (by decide +kernel)

def state211_40 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_40 : Impossible true (goalAt 211) 5 state211_40.toFinset :=
  node_ok cuts211 [⟨state211_35,exclude211_35⟩,⟨state211_15,exclude211_15⟩] 0x20a00908080004828010900828020a00424020a00c08010900828024848828020a00901220600828004c48818020600908004c48818010500818020600414020600c08010500818004c48818020600131214100908030202000024200921224200908020848921230100c04040004c04030200c080400105212 (by decide +kernel)

def state211_41 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_41 : Impossible true (goalAt 211) 6 state211_41.toFinset :=
  node_ok cuts211 [⟨state211_36,exclude211_36⟩,⟨state211_16,exclude211_16⟩,⟨state211_33,exclude211_33⟩,⟨state211_39,exclude211_39⟩,⟨state211_40,exclude211_40⟩] 0x1000514848521224848c08030202000430200c0802484852121484a000310c0c430340010c08030202000230200c08040010430310c0c521220a00828030200424030200521210900424030200828020a00921210900424024040828020a00921220a00828024040424010901000120a00828024201000124201000940006000124200828020a01000910900424040000828020a01000920a00828040000424010900430320600818030200414030200430310500414030200818020601000220600818020a00131220a01000204c48131220a00818020601000510500414024848818020601000220600818024848414010501000120600818024200131224201000204c4813122420081802060100021050041404000c81802060100022060081804000c414010501000140004c04014848908024200c08040004c0801484a000014848c080242009080248490005248490001242009080400050001208490001400145040 (by decide +kernel)

def state211_42 : List Sig := [0xbbbb0000bbbb0000bbbb0000bbbb0000bbbb0000bbbb0000aaaa0000aaaa,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_42 : Impossible true (goalAt 211) 3 state211_42.toFinset :=
  node_ok cuts211 [] 0x30100c08030200421210500818020600414020600c08010500818010900828020a00424020a004240302008280206001312206008280 (by decide +kernel)

def state211_43 : List Sig := [0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaaaaaaaaaaaaaa,input 0,input 6,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_43 : Impossible true (goalAt 211) 4 state211_43.toFinset :=
  node_ok cuts211 [⟨state211_42,exclude211_42⟩] 0x504024200908014100908030200504024200c04030200c08014848818024200110320600414020600818010500818030200414020600131220a02000024200828010900828020a00424020a004240302008280 (by decide +kernel)

def state211_44 : List Sig := [0x5555111155551111555511115555111155551111555511115555000055550000,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_44 : Impossible true (goalAt 211) 3 state211_44.toFinset :=
  node_ok cuts211 [] 0x30100c08030200501214100908024200504024200c080141009080105008180206004140206004140302008180206001312242008180 (by decide +kernel)

def state211_45 : List Sig := [0xffff3333ffff3333ffff3333ffff3333ffff3333ffff3333ffff0000ffff0000,input 4,input 6,input 7,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_45 : Impossible true (goalAt 211) 4 state211_45.toFinset :=
  node_ok cuts211 [⟨state211_44,exclude211_44⟩] 0x414020600818010500818030200414020600818024200131220602000020600818020a00c04030200c08014048504024200908014100908030200504024200110310900828020a00424020a004240302008280 (by decide +kernel)

def state211_46 : List Sig := [0x3333333333333333333333333333333333333333333333330000000000000000,input 6,input 7,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_46 : Impossible true (goalAt 211) 5 state211_46.toFinset :=
  node_ok cuts211 [⟨state211_7,exclude211_7⟩,⟨state211_17,exclude211_17⟩,⟨state211_43,exclude211_43⟩,⟨state211_45,exclude211_45⟩] 0x24848504014100c04024200908024848908024200c04014100504014848908024200c08014100c08014848504014100c0802420090800440c818020600908004c4890800440c131204c48908020600818020c0c414010500c04020600818020c0c818020600c04010500414010c0c818020600c08010500c08010c0c414010500c08020600818030100521230100921230200c08030100c08030200921214848521224200828020a00110380004110324202000324200110320a00828020600828020600131280000131220602000220600131220a00828030100424010900921220a00828030100828020a00921210900424030200828020a00521210900424030200424030200521220a008280 (by decide +kernel)

def state211_47 : List Sig := [0x5555555555555555555555555555555555555555555555550000000000000000,input 0,input 6,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_47 : Impossible true (goalAt 211) 5 state211_47.toFinset :=
  node_ok cuts211 [⟨state211_7,exclude211_7⟩] 0x504024200908014100908030200504024200828024200110320a00424020a00828010900828030200424020a00c04030200c08010c0c130324200131224200111020a00131220a00131230100830330100131230200430330200908004c0c908004c0c828080000828040000c04024848c04020c0cc08014848c08010c0c8180 (by decide +kernel)

def state211_48 : List Sig := [0x3333333333333333333333333333333333333333333333330000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_48 : Impossible true (goalAt 211) 5 state211_48.toFinset :=
  node_ok cuts211 [] 0x14100908024200504024200c0801410090800440c908024200110320600908004c48818010500818020600414020600c08010500818004c48818020600131224848c0403020100071484882800440c908020a00818004c48818020a00424020a00828010900828010900c08020a010000 (by decide +kernel)

def state211_49 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000,input 4,input 6,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_49 : Impossible true (goalAt 211) 5 state211_49.toFinset :=
  node_ok cuts211 [⟨state211_17,exclude211_17⟩] 0x424020a00828010900828030200424020a00828004404110320a00818020a00131220600414020600818010500818030200414020600818004c48131220600c04030200c08014848921230100921230100521230200521230200828080000828040000818004c48818004c48c04024848c04024848c08014848c080148489080 (by decide +kernel)

def state211_50 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_50 : Impossible true (goalAt 211) 6 state211_50.toFinset :=
  node_ok cuts211 [⟨state211_22,exclude211_22⟩,⟨state211_26,exclude211_26⟩,⟨state211_29,exclude211_29⟩,⟨state211_8,exclude211_8⟩,⟨state211_18,exclude211_18⟩,⟨state211_33,exclude211_33⟩,⟨state211_37,exclude211_37⟩,⟨state211_40,exclude211_40⟩,⟨state211_46,exclude211_46⟩,⟨state211_47,exclude211_47⟩,⟨state211_48,exclude211_48⟩,⟨state211_49,exclude211_49⟩] 0x1000514100504030100908024202000724200908030100504014101000424200908030200504030202000614100504030200908024202000b04c0c130340004908024202000524200908040004130304c0c130320a00828024201000724200130380010110324200828020a01000510900424030100828020a01000720a00828030100424010901000420a00828030200424030201000710900424030200828020a0100078002a000840000828020a01000720a00828040001000740000130320600818024200131224200130304c48131224200818020601000720600818020a00131220a02000304c48131220a00818020601000510500414030100818020602000220600818030100414010501000420600818030200414030202000110500414030200818020602000904c4813124000c81802060200002060081804000c131204c49000440010921230101000530101000430200c080400110004400110004400145212 (by decide +kernel)

def state211_51 : List Sig := roots 211
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_51 : Impossible true (goalAt 211) 7 state211_51.toFinset :=
  node_ok cuts211 [⟨state211_9,exclude211_9⟩,⟨state211_19,exclude211_19⟩,⟨state211_27,exclude211_27⟩,⟨state211_30,exclude211_30⟩,⟨state211_38,exclude211_38⟩,⟨state211_41,exclude211_41⟩,⟨state211_50,exclude211_50⟩] 0x40014c04014848c04040010921230200c08080018c04030200c08040010921214848521240014921214100504040004c04024200908080014921224200908040004c04014100504040010521224200908040004c08014100c08080010521214100504040004c08024200908040000921210900424040000c04020a00828040000921220a00828040000c04010900424040000521220a00828040000c08010900c08040000521210900424040000c08020a00828040000130320a00828040000908040000908040000130380004110340000908020a0082804001483031050041404000cc0402060081808000c83032060081804000cc0401050041404001043032060081804000cc08010500c08080008430310500414040010c0802060081804000413032060081804000c908004c48908040008130304c48131240004908020600818040001000020600818040000828004c48828040002000004c481312400008280206008180 (by decide +kernel)

theorem lower211 : Claim 211 8 :=
  fromSearch 100 (by decide +kernel) exclude211_51

theorem lower178 : Claim 178 5 :=
  fromLift 5 16 269942864 lower162 (by decide +kernel)

theorem lower114 : Claim 114 5 :=
  fromLift 5 16 18219088 lower98 (by decide +kernel)

def rule242_0 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower226 none (by decide +kernel)

def rule242_1 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower210 none (by decide +kernel)

def rule242_2 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower208 none (by decide +kernel)

def rule242_3 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower240 none (by decide +kernel)

def rule242_4 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower178 none (by decide +kernel)

def rule242_5 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower114 none (by decide +kernel)

def rule242_6 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower224 none (by decide +kernel)

def rule242_7 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower98 none (by decide +kernel)

def rule242_8 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower162 none (by decide +kernel)

def rule242_9 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower194 none (by decide +kernel)

def cuts242 : Cuts (goalAt 242) := [rule242_0,rule242_1,rule242_2,rule242_3,rule242_4,rule242_5,rule242_6,rule242_7,rule242_8,rule242_9]

def state242_0 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc,input 7,input 6,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_0 : Impossible true (goalAt 242) 4 state242_0.toFinset :=
  node_ok cuts242 [] 0x28200c08018100a08018100a0802820060400c8c0a08028201000220a00a08008848828020a00c08010900828010900828020a0042400c8c0828020a01000030100c080302004212188c0a230 (by decide +kernel)

def state242_1 : List Sig := [0xffffffffffffffffcccccccccccccccc,input 7,input 6,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_1 : Impossible true (goalAt 242) 4 state242_1.toFinset :=
  node_ok cuts242 [] 0xa08030200604028200604028200a08018100828028200221220a00828030200424020a00424020a00828010900e23030200c080288c0604028200604028200424020a00424020a00323030200421230200c040 (by decide +kernel)

def state242_2 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_2 : Impossible true (goalAt 242) 4 state242_2.toFinset :=
  node_ok cuts242 [] 0xa08030200604028200604028200a08018100221228200a08008848908028200221224200828020a00424024200424024200908010900421224200908040018c04030200c0800c8c0323030200c0800c8c0b030 (by decide +kernel)

def state242_3 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_3 : Impossible true (goalAt 242) 5 state242_3.toFinset :=
  node_ok cuts242 [⟨state242_0,exclude242_0⟩,⟨state242_1,exclude242_1⟩,⟨state242_2,exclude242_2⟩] 0xb03018100604030100a08028200b03028200a08030100604018101000228200a08010848604018101000218100604010848a08028200323028200a08040008604018100323018100604040008a08028200b03010900424030100908024200b03024200908030100424010900221224200908028201000628200221240008221228200908024200421224200908040018424010900421210900424040018908024200323024200828040000424020a00323010900424040000908024200c04010848c0402c0c100082c0c0c04080008c0402c0c042122c0c100034000cc08030100323030100b03080004a23030102000030100b0300c8c03230 (by decide +kernel)

def state242_4 : List Sig := [0xffffffffffffffff0000000000000000cccccccccccccccc,input 6,input 7,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_4 : Impossible true (goalAt 242) 4 state242_4.toFinset :=
  node_ok cuts242 [] 0x604028200a08018100a08018100604028200828028200221220a00424020a00828010900828010900424020a00c040388c0c040188c0a08018100a08018100828010900828010900323030100821230100c080 (by decide +kernel)

def state242_5 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_5 : Impossible true (goalAt 242) 4 state242_5.toFinset :=
  node_ok cuts242 [] 0x604028200a08018100a08030200604028200221228200a08008848828028200221220a00424020a00828014100828030200504020a00821220a00828040018323030100c0400c8c0c04030200c0800c8c07030 (by decide +kernel)

def state242_6 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_6 : Impossible true (goalAt 242) 5 state242_6.toFinset :=
  node_ok cuts242 [⟨state242_0,exclude242_0⟩,⟨state242_4,exclude242_4⟩,⟨state242_5,exclude242_5⟩] 0x100071c0c0703020848c08030202000230200c0802084870301c0c200011c0c062300c8c0c08030202000030200c0800c8c070300c8c0703028200a08030200604030200703018100604030200a08028201000218100604020848a08028201000228200a08020848604018100323018100604040008a08028200323028200a08040008604018100703020a00828030200504030200703014100504030200828020a00221220a00828028201000628200221240008221228200828020a00821214100504040018828020a00821220a00828040018504014100323014100424040000828020a00323020a0082804000050401410100034000cc040 (by decide +kernel)

def state242_7 : List Sig := [0x333300003333000033330000333300003333000033330000000000000000,input 6,input 7,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_7 : Impossible true (goalAt 242) 4 state242_7.toFinset :=
  node_ok cuts242 [] 0x604028200a08018100a08030200604028200221228200323028200323030100821230100323030200421230200c04030200c0801c0c0908008848a080242008280141009080242005040242005040302009080 (by decide +kernel)

def state242_8 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_8 : Impossible true (goalAt 242) 5 state242_8.toFinset :=
  node_ok cuts242 [⟨state242_0,exclude242_0⟩,⟨state242_2,exclude242_2⟩,⟨state242_5,exclude242_5⟩,⟨state242_7,exclude242_7⟩] 0x18100a08028200604028200c08018100a08008848a08028200221208848a0800c8c0a08020a0032303010200023010032303020200013020032304000e00000c8c0908028200221224200504024200908014100908030200504024202000324200908040018b03030100c0804001c7030 (by decide +kernel)

def state242_9 : List Sig := [0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 1,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_9 : Impossible true (goalAt 242) 6 state242_9.toFinset :=
  node_ok cuts242 [⟨state242_3,exclude242_3⟩,⟨state242_6,exclude242_6⟩,⟨state242_8,exclude242_8⟩] 0x4001cc0401c0c0c04040020b03030200c08080008c04030200c0804001cb0301c0c0703040008b03018100604040008c04028200a08040008b03028200a08040008c04018100604040008703028200a08040008c08018100c08040008703018100604040008c08028200a0804000c82120c8c032304000cc0404000cc0404000c82128000482124000cc0400c8c0c0404000c42120c8c032304000cc0804000cc0804000c42128000042124000cc0800c8c0c0804000c22124000822124000ca0800c8c0a0804000c22120c8c032304000ca0804000ca08040001000040000828040018b03014100504040018c04024200908040018b03024200908040018c04014100504040018703024200908040018c08014100c08040018703014100504040018c08024200908040018221224200908040018a08040018a08040018221240008221240018a080242009080 (by decide +kernel)

def state242_10 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 7,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_10 : Impossible true (goalAt 242) 4 state242_10.toFinset :=
  node_ok cuts242 [] 0x20a0090800c8c0828020a00c08010900828010900828020a00424008848828020a01000624200c08014100908014100908024200504008848908024201000030100c080302005030148489212 (by decide +kernel)

def state242_11 : List Sig := [0xffffffffffffffffffffffff00000000,input 7,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_11 : Impossible true (goalAt 242) 4 state242_11.toFinset :=
  node_ok cuts242 [] 0x828024200323020a00828030200424020a00424020a00828010900908030200504024200504024200908014100503030200c080140c0424020a00424020a00504024200504024200503030200503030200c040 (by decide +kernel)

def state242_12 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_12 : Impossible true (goalAt 242) 4 state242_12.toFinset :=
  node_ok cuts242 [] 0x828024200323020a00828030200424020a00424020a00828010900323020a0082800c8c0908028200504024200504024200908014100503024200908040024c04030200c08008848503030200c08008848a030 (by decide +kernel)

def state242_13 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_13 : Impossible true (goalAt 242) 5 state242_13.toFinset :=
  node_ok cuts242 [⟨state242_10,exclude242_10⟩,⟨state242_11,exclude242_11⟩,⟨state242_12,exclude242_12⟩] 0x921210900424030100828020a00921220a00828030100424010901000220a0082802420032302420100020c8c0323024200828020a01000220a008280140c04240109010002109004240140c0828020a00221220a00828040018424010900221210900424040018828020a00a03014100504030100908024200a03024200908030100504014100503024200908040024504014100503014100504040024908024200221224200908040000504028200221214100504040000908024200c040140c0c040280c10008280c0c04080008c040280c05030140c1000140004c080301002212301009212800049212301020000301009212088489030 (by decide +kernel)

def state242_14 : List Sig := [0xffffffffffffffff0000000000000000ffffffff00000000,input 6,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_14 : Impossible true (goalAt 242) 4 state242_14.toFinset :=
  node_ok cuts242 [] 0x828024200323020a00424020a00828010900828010900424020a00504024200908014100908014100504024200c040240c0c040240c0828010900828010900908014100908014100903030100903030100c080 (by decide +kernel)

def state242_15 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_15 : Impossible true (goalAt 242) 4 state242_15.toFinset :=
  node_ok cuts242 [] 0x828024200323020a00424020a00828010900828030200424020a00323020a0082800c8c0504024200908014100908030200504024200903024200908040024903030100c04008848c04030200c080088486030 (by decide +kernel)

def state242_16 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_16 : Impossible true (goalAt 242) 5 state242_16.toFinset :=
  node_ok cuts242 [⟨state242_10,exclude242_10⟩,⟨state242_14,exclude242_14⟩,⟨state242_15,exclude242_15⟩] 0x10007180c06030240c0c08030202000230200c080240c06030180c2000114848521208848c08030202000030200c080088485212140c0521220a00828030200424030200521210900424030200828020a01000220a0082802420032302420100020c8c0323024200828020a010002109004240240c0828020a01000220a008280240c0424010900221210900424040018828020a00221220a00828040018424010900603024200908030200504030200603014100504030200908024200903014100504040024908024200903024200908040024504014100221214100504040000908024200221224200908040000504014101000140004c040 (by decide +kernel)

def state242_17 : List Sig := [0xffff000000000000ffff000000000000ffff0000000000000000,input 6,input 7,input 5,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_17 : Impossible true (goalAt 242) 4 state242_17.toFinset :=
  node_ok cuts242 [] 0x82800c8c0323020a00424020a00828010900828030200424020a00a03030100903030100603030200503030200c04030200c080180c082800c8c0828024200a080141009080242005040242005040302009080 (by decide +kernel)

def state242_18 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_18 : Impossible true (goalAt 242) 5 state242_18.toFinset :=
  node_ok cuts242 [⟨state242_10,exclude242_10⟩,⟨state242_12,exclude242_12⟩,⟨state242_15,exclude242_15⟩,⟨state242_17,exclude242_17⟩] 0x20a0032300c8c0828020a0090800c8c0828010900828020a00424020a00c0801090082800c8c0828020a00323028200221230102000230100221230202000130200221240006000008848504024200908014100908030200504024202000324200908040024a03030100c0804001c6030 (by decide +kernel)

def state242_19 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_19 : Impossible true (goalAt 242) 6 state242_19.toFinset :=
  node_ok cuts242 [⟨state242_13,exclude242_13⟩,⟨state242_16,exclude242_16⟩,⟨state242_18,exclude242_18⟩] 0x4001cc040180c0c04040020a03030200c08080008c04030200c0804001ca030180c0603040008921210900424040018c04020a00828040008921220a00828040018c04010900424040008521220a00828040018c08010900c08040008521210900424040018c08020a00828040004221220a0082804000500060c8c032304000422120c8c0323040005000120a00828040009000220a0082804001890800c8c090804000900020c8c0323040018908020a00828040004a03008848a03040004c04040004c04040004a03080004903040004c04008848c04040004603008848603040004c08040004c08040004603080000503040004c08008848c08040001000040000a08040024a03014100504040024c04024200908040024a03024200908040024c04014100504040024603024200908040024c08014100c08040024603014100504040024c080242009080 (by decide +kernel)

def state242_20 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc,input 7,input 1,input 6,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_20 : Impossible true (goalAt 242) 4 state242_20.toFinset :=
  node_ok cuts242 [] 0x28200c08018100a08018100a08028200604030100c08030200703020a00a0800c8c0828020a00c08010900828010900828020a00424024200221228200908024200504030200908020a00323020a009080141009080242005040 (by decide +kernel)

def state242_21 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff00000000cccccccc,input 7,input 1,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_21 : Impossible true (goalAt 242) 4 state242_21.toFinset :=
  node_ok cuts242 [] 0x24200c08014100908014100908024200504030100c08030200703020a0090800c8c0828020a00c08010900828010900828020a00424024200221224200a08028200604030200a08020a00323020a00a08018100a080282006040 (by decide +kernel)

def state242_22 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc,input 7,input 1,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_22 : Impossible true (goalAt 242) 5 state242_22.toFinset :=
  node_ok cuts242 [⟨state242_0,exclude242_0⟩,⟨state242_20,exclude242_20⟩,⟨state242_21,exclude242_21⟩] 0xa08030200604028200604028200a08018102000228200a08040004908028200221224200908030200504024200504024200908014102000124200908040000c04030200c08014848703020a00a0800c848828020a00908080000828020a00c08010900828010900828020a0042400c8c0b030 (by decide +kernel)

def state242_23 : List Sig := [0xffffffffffffffffcccccccccccccccc,input 7,input 1,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_23 : Impossible true (goalAt 242) 5 state242_23.toFinset :=
  node_ok cuts242 [⟨state242_1,exclude242_1⟩] 0xa08030200604028200604028200a08018100908028200221224200908030200504024200504024200908014100f03030200c0802c0c0828028200321220a00828024202000020a00828030200424020a00424020a00828010900604028200604028200504024200504024200703030200521230200424020a00424020a00c040 (by decide +kernel)

def state242_24 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_24 : Impossible true (goalAt 242) 4 state242_24.toFinset :=
  node_ok cuts242 [] 0x28200828018100828018100a0802820042400c848a08028200321224200a08008848908024200828014100828014100908024200424014848908024200421210900828020a0100041c0c0828020a0090122c0c04240109005012 (by decide +kernel)

def state242_25 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_25 : Impossible true (goalAt 242) 5 state242_25.toFinset :=
  node_ok cuts242 [⟨state242_24,exclude242_24⟩] 0x28200604018100a08028200828018100828018100a08028200604018100a08028200424024200a0800884890802420050401410090802420082801410082801410090802420050401410090802420042403020052122484a000014848424014848424014048921220a00828024048424020a00828040010c040 (by decide +kernel)

def state242_26 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_26 : Impossible true (goalAt 242) 5 state242_26.toFinset :=
  node_ok cuts242 [⟨state242_24,exclude242_24⟩,⟨state242_2,exclude242_2⟩] 0x28200c08018100a08018100a0802820060400c848a08028200321224200a08008848908024200c08014100908014100908024200504014848908024200421210900a0800c848a08010900908080004908020a00424020902000010900521210900424014048c04030200c08040014703030200c0804000cb030 (by decide +kernel)

def state242_27 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 1,input 6,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_27 : Impossible true (goalAt 242) 6 state242_27.toFinset :=
  node_ok cuts242 [⟨state242_3,exclude242_3⟩,⟨state242_22,exclude242_22⟩,⟨state242_23,exclude242_23⟩,⟨state242_25,exclude242_25⟩,⟨state242_26,exclude242_26⟩] 0xb03018100604030100a08028200b03028200a08030100604018101000428200a08014848604018101000218100604014848a08028201000228200a08040004604018101000218100604040004a08028200b03014100504030100908024200b03024200908030100504014100321224200908028201000628200321240008221228200908024200521224200908010808504014100521214100504010808908024201000624200908040000504014101000614100504040000908024200c04014848c0402c0c100042c0c0c04080010c0402c0c052122c0c100044000cc08024848424010900c0404000cc0402484a000324848c0401090042400c848424010900a0804000ca0800c84900020c848a08010900a0804000c42401090090804000c90804000d000680000908010900908014849000414849000310900424040011000414049000440010828030101000530100b03080008b03030102000130100b03040014b030 (by decide +kernel)

def state242_28 : List Sig := [0xffffffffffffffff0000000000000000cccccccccccccccc,input 6,input 1,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_28 : Impossible true (goalAt 242) 5 state242_28.toFinset :=
  node_ok cuts242 [⟨state242_4,exclude242_4⟩] 0x604028200a08018100a08018100604028200908028200221224200504024200908014100908014100504024200828028200321220a00828024202000020a00424020a00828010900828010900424020a00c0403c0c0c0401c0c0a08018100a08018100908014100908014100b03030100921230100828010900828010900c080 (by decide +kernel)

def state242_29 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_29 : Impossible true (goalAt 242) 5 state242_29.toFinset :=
  node_ok cuts242 [⟨state242_24,exclude242_24⟩,⟨state242_5,exclude242_5⟩] 0x18100a08028200604028200c08018100a0800c848a08028200321224200a08008848908014100908024200504024200c08014100908024848908024200821220a00a0800c848828020a00908080004828010900828030202000020a00921220a00828024048b03030100c04040010c04030200c080400107030 (by decide +kernel)

def state242_30 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 1,input 7,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_30 : Impossible true (goalAt 242) 6 state242_30.toFinset :=
  node_ok cuts242 [⟨state242_6,exclude242_6⟩,⟨state242_25,exclude242_25⟩,⟨state242_22,exclude242_22⟩,⟨state242_28,exclude242_28⟩,⟨state242_29,exclude242_29⟩] 0x100051c0c0703024848c08030202000430200c0802484870301c0c200031c0c0703040010c08030202000230200c0804001070301c0c0703028200a08030200604030200703018100604030200a08028201000518100604024848a08028201000228200a08024848604018101000218100604040004a08028201000228200a0804000460401810070302420090803020050403020070301410050403020090802420032122420090802820100062820032124000822122820090802420092121410050402080890802420092122420090802080850401410100061410050404000090802420100062420090804000050401410100034000cc04014848828020a00c0804000cc0801484a000114848c08020a0082800c848828020a00a0804000ca0800c84900020c848a08020a0082804000c828020a0090804000c90804000d000680000908020a00828024849000524849000320a0082804000d0003240490003400144240 (by decide +kernel)

def state242_31 : List Sig := [0x3333333333333333333333333333333333333333333333333333333300000000,input 7,input 5,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_31 : Impossible true (goalAt 242) 4 state242_31.toFinset :=
  node_ok cuts242 [] 0x24200c08014100908024200a08008848908014100908024200504030100c08030200703028200c08018100a08018100a08028200604020a00323024200828020a00424030200828020a00323028200828010900828020a004240 (by decide +kernel)

def state242_32 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000,input 7,input 5,input 6,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_32 : Impossible true (goalAt 242) 4 state242_32.toFinset :=
  node_ok cuts242 [] 0x20a00c08010900828020a00a0800c8c0828010900828020a00424030100c08030200703028200c08018100a08018100a08028200604020a00323020a009080242005040302009080242002212282009080141009080242005040 (by decide +kernel)

def state242_33 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 7,input 5,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_33 : Impossible true (goalAt 242) 5 state242_33.toFinset :=
  node_ok cuts242 [⟨state242_10,exclude242_10⟩,⟨state242_31,exclude242_31⟩,⟨state242_32,exclude242_32⟩] 0x908030200504024200908028202000024200504024200908014102000224200908040000828024200323020a00828030200424020a00828028200323020a00424020a00828010902000120a0082804000cc04030200c0801c0c0521228200c08018100a08018100a0802820060400c8489212 (by decide +kernel)

def state242_34 : List Sig := [0xffffffffffffffffffffffff00000000,input 7,input 5,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_34 : Impossible true (goalAt 242) 5 state242_34.toFinset :=
  node_ok cuts242 [⟨state242_11,exclude242_11⟩] 0x908030200504024200908028202000024200504024200908014100828024200323020a00828030200424020a00828028200323020a00424020a00828010900703030200c0801c0c0a08030200604028200604028200a08018100504024200504024200424020a00424020a00703030200703030200604028200604028200c040 (by decide +kernel)

def state242_35 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_35 : Impossible true (goalAt 242) 4 state242_35.toFinset :=
  node_ok cuts242 [] 0x24200a0801410090801410090802420050401c0c0908024200603020a0090800c8c0828020a00a08010900828010900828020a0042400c8c0828020a00323018100a0802820100041c0c0a0802820090301c0c06040181005030 (by decide +kernel)

def state242_36 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_36 : Impossible true (goalAt 242) 5 state242_36.toFinset :=
  node_ok cuts242 [⟨state242_35,exclude242_35⟩] 0x24200504014100908024200a08014100908014100908024200504014100908024200504020a0090800c8c0828020a00424010900828020a00a08010900828010900828020a00424010900828020a0042403020070302c0c200001c0c060401c0c06040140c0b03028200a080240c0604028200a08040010c040 (by decide +kernel)

def state242_37 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_37 : Impossible true (goalAt 242) 5 state242_37.toFinset :=
  node_ok cuts242 [⟨state242_35,exclude242_35⟩,⟨state242_12,exclude242_12⟩] 0x24200604080004908024200c0801410090801410090802420050401c0c0908024200603020a0090800c8c0828020a0060400c8c0828020a00c08010900828010900828020a0042400c8c0828020a003230282006040281020000181007030181006040140c0c04030200c08040014703030200c08040004b030 (by decide +kernel)

def state242_38 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_38 : Impossible true (goalAt 242) 6 state242_38.toFinset :=
  node_ok cuts242 [⟨state242_13,exclude242_13⟩,⟨state242_33,exclude242_33⟩,⟨state242_34,exclude242_34⟩,⟨state242_36,exclude242_36⟩,⟨state242_37,exclude242_37⟩] 0xb03014100504030100908024200b03024200908030100504014100703024200908018080504014100703014100504018080908024201000124200908018101000118101000940006000018100908024201000924200908040000504014101000914100504040000908024200921210900424030100828020a00921220a00828030100424010901000220a0082802420032302420100020c8c0323024200828020a01000420a0082801c0c042401090100021090042401c0c0828020a01000120a0082801810032301810100020c8c0323018100828020a01000220a0082804000c42401090100021090042404000c828020a00c0401c0c0c0402c0c100042c0c0c04080010c0402c0c070301c0c1000140004c0802c0c0604018100c04040004c0402c0c200032c0c0c0401810060401c0c100041c0c10001181006040400050001140c1000140010a080301010005301009212800089212301020001301009212400149212 (by decide +kernel)

def state242_39 : List Sig := [0xffffffffffffffff0000000000000000ffffffff00000000,input 6,input 5,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_39 : Impossible true (goalAt 242) 5 state242_39.toFinset :=
  node_ok cuts242 [⟨state242_14,exclude242_14⟩] 0x504024200908014100908028202000024200908014100504024200828024200323020a00424020a00828010900828028200323020a00828010900424020a00604028200a08018100a08018100604028200c0402c0c0c0402c0c0908014100908014100828010900828010900b03030100b03030100a08018100a08018100c080 (by decide +kernel)

def state242_40 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_40 : Impossible true (goalAt 242) 5 state242_40.toFinset :=
  node_ok cuts242 [⟨state242_35,exclude242_35⟩,⟨state242_15,exclude242_15⟩] 0x24200a08080004908014100908024200504024200c0801410090802c0c0908024200a03020a0090800c8c0828020a00a0800c8c0828010900828020a00424020a00c0801090082800c8c0828020a00323018100a08030202000028200b03028200a080240c0b03030100c04040004c04030200c080400107030 (by decide +kernel)

def state242_41 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_41 : Impossible true (goalAt 242) 6 state242_41.toFinset :=
  node_ok cuts242 [⟨state242_36,exclude242_36⟩,⟨state242_16,exclude242_16⟩,⟨state242_33,exclude242_33⟩,⟨state242_39,exclude242_39⟩,⟨state242_40,exclude242_40⟩] 0x100051c0c070302c0c0c08030202000430200c0802c0c070301c0c2000314848521240010c08030202000230200c08040010521214848703024200908030200504030200703014100504030200908024200b03014100504028080908024200b03024200908028080504014101000124200908028201000128201000940006000128200908024201000914100504040000908024201000924200908040000504014100521220a00828030200424030200521210900424030200828020a01000220a0082802420032302420100020c8c0323024200828020a0100051090042402c0c0828020a01000220a0082802c0c0424010901000120a0082802820032302820100020c8c0323028200828020a0100021090042404000c828020a01000220a0082804000c424010901000140004c0401c0c0a08028200c08040004c0801c0c200001c0c0c08028200a0802c0c100052c0c1000128200a080400050001240c10001400146040 (by decide +kernel)

def state242_42 : List Sig := [0xccccffff00000000ccccffff00000000ccccffff00000000cccccccc,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_42 : Impossible true (goalAt 242) 3 state242_42.toFinset :=
  node_ok cuts242 [] 0x30100c08030200503010900828020a00424020a00c08010900828014100908024200504024200504030200908020a00323020a009080 (by decide +kernel)

def state242_43 : List Sig := [0xccccffffccccffffccccffffccccffffccccffffccccffffcccccccccccccccc,input 1,input 6,input 7,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_43 : Impossible true (goalAt 242) 4 state242_43.toFinset :=
  node_ok cuts242 [⟨state242_42,exclude242_42⟩] 0x604028200a08018100a08030200604028200c04030200c0801c0c0828028200221220a00424020a00828010900828030200424020a003230242020000282009080141009080242005040242005040302009080 (by decide +kernel)

def state242_44 : List Sig := [0x3333333300003333333333330000333333333333000033333333333300000000,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_44 : Impossible true (goalAt 242) 3 state242_44.toFinset :=
  node_ok cuts242 [] 0x30100c08030200603018100a08028200604028200c08018100a08010900828020a00424020a00424030200828020a003230282008280 (by decide +kernel)

def state242_45 : List Sig := [0xffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff00000000,input 5,input 6,input 7,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_45 : Impossible true (goalAt 242) 4 state242_45.toFinset :=
  node_ok cuts242 [⟨state242_44,exclude242_44⟩] 0x424020a00828010900828030200424020a00828028200323020a02000020a00828024200c04030200c080180c0604028200a08018100a080302006040282002212141009080242005040242005040302009080 (by decide +kernel)

def state242_46 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000,input 6,input 7,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_46 : Impossible true (goalAt 242) 5 state242_46.toFinset :=
  node_ok cuts242 [⟨state242_7,exclude242_7⟩,⟨state242_17,exclude242_17⟩,⟨state242_43,exclude242_43⟩,⟨state242_45,exclude242_45⟩] 0x2c0c0604018100c04028200a0802c0c0a08028200c0401810060401c0c0a08028200c08018100c0801c0c0604018100c08028200a08008848828020a00a0800c8c0a0800884832300c8c0a08020a00828024848424010900c04020a00828024848828020a00c04010900424014848828020a00c08010900c08014848424010900c08020a00828030100703030100b03030200c08030100c08030200b0301c0c0703028200908024200221280004221228202000328200221224200908020a00908020a00323080000323020a02000220a00323024200908030100504014100b03024200908030100908024200b030141005040302009080242007030141005040302005040302007030242009080 (by decide +kernel)

def state242_47 : List Sig := [0x3333333333333333333333333333333333333333333333330000000000000000,input 1,input 6,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_47 : Impossible true (goalAt 242) 5 state242_47.toFinset :=
  node_ok cuts242 [⟨state242_7,exclude242_7⟩] 0x604028200a08018100a08030200604028200908028200221224200504024200908014100908030200504024200c04030200c08014848321228200323028200222024200323024200323030100921230100323030200521230200a0800c848a0800c848908080000908040000c0402c0c0c04024848c0801c0c0c080148488280 (by decide +kernel)

def state242_48 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_48 : Impossible true (goalAt 242) 5 state242_48.toFinset :=
  node_ok cuts242 [] 0x18100a08028200604028200c08018100a08008848a08028200221220a00a0800c8c0828010900828020a00424020a00c0801090082800c8c0828020a0032302c0c0c0403020100071c0c0908008848a0802420082800c8c0828024200504024200908014100908014100c080242010000 (by decide +kernel)

def state242_49 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff0000000000000000,input 5,input 6,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_49 : Impossible true (goalAt 242) 5 state242_49.toFinset :=
  node_ok cuts242 [⟨state242_17,exclude242_17⟩] 0x504024200908014100908030200504024200908008808221224200828024200323020a00424020a00828010900828030200424020a0082800c8c0323020a00c04030200c0801c0c0b03030100b0303010070303020070303020090808000090804000082800c8c082800c8c0c0402c0c0c0402c0c0c0801c0c0c0801c0c0a080 (by decide +kernel)

def state242_50 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_50 : Impossible true (goalAt 242) 6 state242_50.toFinset :=
  node_ok cuts242 [⟨state242_22,exclude242_22⟩,⟨state242_26,exclude242_26⟩,⟨state242_29,exclude242_29⟩,⟨state242_8,exclude242_8⟩,⟨state242_18,exclude242_18⟩,⟨state242_33,exclude242_33⟩,⟨state242_37,exclude242_37⟩,⟨state242_40,exclude242_40⟩,⟨state242_46,exclude242_46⟩,⟨state242_47,exclude242_47⟩,⟨state242_48,exclude242_48⟩,⟨state242_49,exclude242_49⟩] 0x1000518100604030100a08028202000728200a08030100604018101000428200a08030200604030202000618100604030200a08028202000b0c848321240004a08028202000528200a0804000432120c84832122420090802820100072820032128001022122820090802420100051410050403010090802420100072420090803010050401410100042420090803020050403020100071410050403020090802420100078002a000840000908024201000724200908040001000740000321220a0082802820032302820032120c8c0323028200828020a01000720a0082802420032302420200030c8c0323024200828020a01000510900424030100828020a02000220a00828030100424010901000420a00828030200424030202000110900424030200828020a0200090c8c032304000c828020a02000020a0082804000c32300c8c1000440010b03030101000530101000430200c080400110004400110004400147030 (by decide +kernel)

def state242_51 : List Sig := roots 242
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_51 : Impossible true (goalAt 242) 7 state242_51.toFinset :=
  node_ok cuts242 [⟨state242_9,exclude242_9⟩,⟨state242_19,exclude242_19⟩,⟨state242_27,exclude242_27⟩,⟨state242_30,exclude242_30⟩,⟨state242_38,exclude242_38⟩,⟨state242_41,exclude242_41⟩,⟨state242_50,exclude242_50⟩] 0x40014c0401c0c0c04040010b03030200c08080018c04030200c08040010b0301c0c0703040014b03018100604040004c04028200a08080014b03028200a08040004c04018100604040010703028200a08040004c08018100c08080010703018100604040004c08028200a08040000b03014100504040000c04024200908040000b03024200908040000c04014100504040000703024200908040000c08014100c08040000703014100504040000c08024200908040000321224200908040000a08040000a08040000321280004221240000a0802420090804001492121090042404000cc04020a0082808000c921220a0082804000cc04010900424040010521220a0082804000cc08010900c08080008521210900424040010c08020a00828040004321220a0082804000ca0800c8c0a0804000832120c8c0323040004a08020a00828040001000020a0082804000090800c8c090804000200000c8c0323040000908020a008280 (by decide +kernel)

theorem lower242 : Claim 242 8 :=
  fromSearch 286654544 (by decide +kernel) exclude242_51

def rule115_0 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower113 none (by decide +kernel)

def rule115_1 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower99 none (by decide +kernel)

def rule115_2 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower83 none (by decide +kernel)

def rule115_3 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower114 none (by decide +kernel)

def cuts115 : Cuts (goalAt 115) := [rule115_0,rule115_1,rule115_2,rule115_3]

def state115_0 : List Sig := roots 115
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_0 : Impossible true (goalAt 115) 6 state115_0.toFinset :=
  node_ok cuts115 [] 0x4000870300c84870304000852121810060404000870301810060404000852120c84850304000470300c48470304000461211410050404000470301410050404000461210c48460304000432121410050404000460400c48460404000432120c48431214000460401410050404000052120c8c032304000070301090042404000052121090042404000070300c8c032304000032121090042404000060400c8c060404000032120c8c032304000060401090042404000013031090042404000050400c8c050404000013030c8c032304000050401090042404000c61210c4c031304000c70301050041404000c61211050041404000c70300c4c031304000823031050041404000860400c4c060404000823030c4c031304000860401050041404000431211050041404000450400c4c050404000431210c4c0313040004504010500414040000232110500414040000424004c48424040000232104c482221400004240105004140 (by decide +kernel)

theorem lower115 : Claim 115 7 :=
  fromSearch 1048660 (by decide +kernel) exclude115_0

def rule179_0 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower177 none (by decide +kernel)

def rule179_1 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower163 none (by decide +kernel)

def rule179_2 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower147 none (by decide +kernel)

def rule179_3 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower178 none (by decide +kernel)

def cuts179 : Cuts (goalAt 179) := [rule179_0,rule179_1,rule179_2,rule179_3]

def state179_0 : List Sig := roots 179
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_0 : Impossible true (goalAt 179) 6 state179_0.toFinset :=
  node_ok cuts179 [] 0x40008b0300c848b03040008921228200a08040008b03028200a0804000892120c848903040004b0300c484b03040004a12124200908040004b03024200908040004a1210c484a03040004321224200908040004a0800c484a0804000432120c484312140004a0802420090804000092120c8c0323040000b03020a00828040000921220a00828040000b0300c8c0323040000321220a00828040000a0800c8c0a0804000032120c8c0323040000a08020a00828040000130320a0082804000090800c8c090804000013030c8c0323040000908020a0082804000ca1210c4c031304000cb0302060081804000ca1212060081804000cb0300c4c0313040008230320600818040008a0800c4c0a0804000823030c4c0313040008a0802060081804000431212060081804000490800c4c090804000431210c4c0313040004908020600818040000232120600818040000828004c48828040000232104c482221400008280206008180 (by decide +kernel)

theorem lower179 : Claim 179 7 :=
  fromSearch 1048660 (by decide +kernel) exclude179_0

def rule243_0 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower241 none (by decide +kernel)

def rule243_1 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower227 none (by decide +kernel)

def rule243_2 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower211 none (by decide +kernel)

def rule243_3 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower242 none (by decide +kernel)

def rule243_4 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower115 none (by decide +kernel)

def rule243_5 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower179 none (by decide +kernel)

def rule243_6 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower114 none (by decide +kernel)

def rule243_7 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower242 (some (1,input 6,input 7)) (by decide +kernel)

def rule243_8 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower113 none (by decide +kernel)

def rule243_9 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower241 (some (1,input 6,input 7)) (by decide +kernel)

def rule243_10 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower98 none (by decide +kernel)

def rule243_11 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower99 none (by decide +kernel)

def rule243_12 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower211 (some (1,input 6,input 7)) (by decide +kernel)

def rule243_13 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower83 none (by decide +kernel)

def rule243_14 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower145 none (by decide +kernel)

def rule243_15 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower227 (some (1,input 6,input 7)) (by decide +kernel)

def cuts243 : Cuts (goalAt 243) := [rule243_0,rule243_1,rule243_2,rule243_3,rule243_4,rule243_5,rule243_6,rule243_7,rule243_8,rule243_9,rule243_10,rule243_11,rule243_12,rule243_13,rule243_14,rule243_15]

def state243_0 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_0 : Impossible true (goalAt 243) 8 state243_0.toFinset :=
  node_ok cuts243 [] 0x40011000418100604040010c04028200a08040011000c28200a08040010c04018100604040015000528200a08040014c08018100c08040015000c18100604040014c08028200a08040031000c0c848321240035000228200a08040031000c28200a0804003500020c84832124003432122420090804002ca0800c484a0804003c32120c48431214002ca08024200908040011000414100504040010c04024200908040011000f24200908040010c04014100504040015000524200908040014c08014100c08040015000f14100504040014c0802420090804003d000f0c48431214002d00012420090804003d000f2420090804002d00010c484312140034321220a00828040020a0800c8c0a0804003832120c8c0323040020a08020a0082804002c130320a0082804002090800c8c090804002413030c8c0323040020908020a00828040011000410900424040010c04020a00828040011000920a00828040010c04010900424040015000520a00828040014c08010900c08040015000910900424040014c08020a0082804002500090c8c0323040021000020a00828040025000920a0082804002100000c8c0323040034230320600818040018a0800c4c0a0804003023030c4c0313040018a0802060081804002c31212060081804001890800c4c090804002831210c4c0313040018908020600818040020232120600818040018828004c48828040024232104c48222140020828020600818040011000410500414040010c04020600818040011000720600818040010c04010500414040015000520600818040014c08010500c08040015000710500414040014c0802060081804001d00070c4c031304001900032060081804001d00072060081804001900030c4c0313040011000440014b03040010c04040010c04040011000530200c080400110004400110004400110004400107030 (by decide +kernel)

def state243_1 : List Sig := roots 243
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_1 : Impossible true (goalAt 243) 9 state243_1.toFinset :=
  node_ok cuts243 [⟨state243_0,exclude243_0⟩] 0x40010c0401c0c0c04040014b03030200c08080000c04030200c08040010b0301c0c0703040008b03018100604040008c04028200a08040008b03028200a08040008c04018100604040008703028200a08040008c08018100c08040008703018100604040008c08028200a08040004b03014100504040004c04024200908040004b03024200908040004c04014100504040004703024200908040004c08014100c08040004703014100504040004c08024200908040004321224200908040004a0800c484a0804000432120c484312140004a08024200908040000921210900424040000c04020a00828040000921220a00828040000c04010900424040000521220a00828040000c08010900c08040000521210900424040000c08020a00828040000321220a00828040000a0800c8c0a0804000032120c8c0323040000a08020a00828040000130320a0082804000090800c8c090804000013030c8c0323040000908020a0082804000ca1211050041404000cc0402060081804000ca1212060081804000cc0401050041404000c61212060081804000cc08010500c0804000c61211050041404000cc08020600818040008230320600818040008a0800c4c0a0804000823030c4c0313040008a0802060081804000431212060081804000490800c4c090804000431210c4c0313040004908020600818040000232120600818040000828004c48828040000232104c482221400008280206008180 (by decide +kernel)

theorem lower243 : Claim 243 10 :=
  fromSearch 1048660 (by decide +kernel) exclude243_1


open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

def smallCircuit : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [5, 13]⟩, ⟨.and, [4, 0]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [19, 17]⟩], 20⟩

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


def lowRow (i : Fin 8) : Row := Fin.ofNat 256 (1 <<< ([4, 5, 5, 6, 0, 1, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 256 ((1 <<< i.val) ||| (1 <<< ([4, 5, 5, 6, 0, 1, 0, 0] : List Nat).getD i.val 0))

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

end PEqualNP.Outside.L_meta_31165_aux

open PEqualNP.Outside.L_meta_31165_aux in
theorem PEqualNP.Outside.L_meta_31165 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true))  := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct

import PEqualNP.Defs





namespace PEqualNP.Outside.L_meta_33557_aux.Base
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

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a

theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _

theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r

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

def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none

def vars (m : Nat) := (selected m).map Prod.snd

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

abbrev Bits := BitVec 152

abbrev Signals := Bits × Bits

abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn

theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)

def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false

theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩

def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1

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

def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
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

theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
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
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)

def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)

def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)

def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))

def Forest.mask (g : Forest) : Nat := g.1

def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)

def Forest.cap (g : Forest) : Nat := g.2.1

def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1

def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1

def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1

def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws

theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

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

def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,_,_,_,_,word) := tab
  let width := 10*d+raw+d
  packedAt word (i*width) width

def storedDepth (_g : Forest) (depth : Nat) := depth

def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := forestRecord (g.levels k) raw.length i
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)

def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,_,_,ow,_,data) := tab
  let start := num*(10*d+raw+d)
  let pos := start+num*ow+packedAt data (start+i*ow) ow
  getPairs data cw d (packedAt data pos 6) (pos+6)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws

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

def sevenInputs : List Sig := vars 127

def sampleSeven (r : Row) (i : Fin 7) : Bool := bit r (sevenInputs.getD i.val zero)

theorem sevenList : List.ofFn (fun i : Fin 7 => sevenInputs.getD i.val zero) = sevenInputs := rfl

theorem sevenSampled (r : Row) : List.ofFn (sampleSeven r) = sevenInputs.map (bit r) := by
  rw [←sevenList,List.map_ofFn]
  rfl

theorem sevenEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sevenInputs).getD i zero) =
      (C.wires (List.ofFn (sampleSeven r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sevenSampled]
  rfl
end PEqualNP.Outside.L_meta_33557_aux.Base

namespace PEqualNP.Outside.L_meta_33557_aux.Cert
open PEqualNP.Outside.L_meta_33557_aux.Base


def rulePool (raw : List Sig) (c : ColumnInfo) : BoundPool :=
  (subcube c.1 c.2.1, c.2.2.2.2, 0, raw)

def Matches (g : Forest) (T : Sig) : Prop :=
  properPairs T (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2)

def Rules (g : Forest) (T : Sig) : Prop :=
  ∀ c ∈ g.cols, Slice g.mode (vars g.mask) T (subcube c.1 c.2.1) c.2.2.2.2

def hintedRule (g : Forest) (k i : Nat) (h : Nat × Nat) : Option BoundPool :=
  match g.cols[h.1]? with
  | none => none
  | some c =>
    if h.2 = 0 then some (rulePool (vars g.mask) c) else
      let node := readNode g k i
      materialize g.mode (vars g.mask)
        (chosenSteps node.2.1 node.1 h.2 (g.levels k).2.1)
        (subcube c.1 c.2.1) c.2.2.2.2

theorem hintedRule_sound {g T k i h r} (cols : Rules g T)
    (he : hintedRule g k i h = some r) : ValidPool g.mode (vars g.mask) T r := by
  unfold hintedRule at he
  cases hc : g.cols[h.1]? with
  | none => simp [hc] at he
  | some c =>
    simp only [hc] at he
    split at he
    · cases he
      exact build_valid (cols c (List.mem_of_getElem? hc)) [] rfl
    · exact materialize_sound (cols c (List.mem_of_getElem? hc)) he

def nextState (g : Forest) (k tag : Nat) : Option (List Sig) := do
  let (j,_) ← g.index k tag
  if j < (g.levels (k-1)).1 then some (stateSet g (k-1) j) else none

def nodeCheck (g : Forest) (T : Sig) (k i : Nat) : Bool :=
  let ws := (readNode g k i).2.2
  let values := ws.map Prod.fst
  let raw := vars g.mask
  let rules := (forestHints (g.levels k) raw.length i).filterMap (hintedRule g k i)
  decide values.Nodup && !(values.contains T) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,fun tag => (nextState g k tag).toList) ws)

theorem nodeCheck_sound (g : Forest) (T : Sig) (k i : Nat)
    (pairs : Matches g T) (cols : Rules g T)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode T (k-1) (stateSet g (k-1) j).toFinset)
    (ok : nodeCheck g T k i = true) : Impossible g.mode T k (stateSet g k i).toFinset := by
  simp only [nodeCheck,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at ok
  have nd := ok.1.1
  have absent : T ∉ stateSet g k i := by simpa [stateSet] using ok.1.2
  by_cases hzero : k=0
  · subst k
    intro t lo h
    have eq : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hs,_⟩ := h
    exact absent (List.mem_toFinset.mp (by rw [he,hs]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) pairs _ nd absent _ _ (by simpa only [hzero,if_false] using ok.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro pool hp
    obtain ⟨_,_,he⟩ := List.mem_filterMap.mp hp
    exact hintedRule_sound cols he
  · intro tag xs hx
    have he : nextState g k tag = some xs := by simpa using hx
    unfold nextState at he
    cases idx : g.index k tag with
    | none => simp [idx] at he
    | some z =>
      rcases z with ⟨j,a⟩
      by_cases hj : j < (g.levels (k-1)).1
      · simp [idx,hj] at he
        subst xs
        exact prior (by omega) j hj
      · simp [idx,hj] at he

def checks (g : Forest) (T : Sig) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeCheck g T k (start+n) && checks g T k start n

theorem checks_at {g T k start n} (h : checks g T k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeCheck g T k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [checks,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem checks_merge {g T k start a b} (h : checks g T k start a=true)
    (h' : checks g T k (start+a) b=true) : checks g T k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [Nat.add_succ,checks,Bool.and_eq_true] at h' ⊢
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

theorem allRows {g T} (pairs : Matches g T) (cols : Rules g T)
    (checked : ∀ k ≤ g.cap, checks g T k 0 (g.levels k).1 = true) :
    ∀ k ≤ g.cap, ∀ i < (g.levels k).1, Impossible g.mode T k (stateSet g k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro hk i hi
    exact nodeCheck_sound g T 0 i pairs cols (by omega) (checks_at (checked 0 hk) i (by omega) (by omega))
  | succ k ih =>
    intro hk i hi
    exact nodeCheck_sound g T (k+1) i pairs cols (fun _ => by simpa using ih (by omega)) (checks_at (checked _ hk) i (by omega) (by omega))

theorem rootDone {g T}
    (pairs : Matches g T) (cols : Rules g T)
    (checked : ∀ k ≤ g.cap, checks g T k 0 (g.levels k).1 = true)
    (idx : indexedRoot g g.cap 0 (vars g.mask)=true) : Impossible g.mode T g.cap (vars g.mask).toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact allRows pairs cols checked _ (Nat.le_refl _) 0 idx.1



abbrev Claim := Sig × Forest × Nat

def essentialData (a : Claim) : List (Sig × Row × Row) :=
  (selected a.2.1.mask).map fun (i,w) =>
    let r := (a.2.2 >>> (7*i)) &&& 127
    (w,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def exchangeAxes (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 ((1 <<< j)-(1 <<< i)))

def faceMoves : Nat → List Move
  | 1 => [exchangeAxes 33, exchangeAxes 48]
  | 2 => [exchangeAxes 50]
  | 3 => [exchangeAxes 82, exchangeAxes 32, exchangeAxes 96]
  | 4 => [exchangeAxes 82, exchangeAxes 98]
  | 5 => [exchangeAxes 101]
  | 6 => [exchangeAxes 48, exchangeAxes 32, exchangeAxes 16]
  | 7 => [exchangeAxes 50, exchangeAxes 16]
  | 8 => [exchangeAxes 83, exchangeAxes 99]
  | 9 => [exchangeAxes 83, exchangeAxes 66, exchangeAxes 16]
  | 10 => [exchangeAxes 66, exchangeAxes 16]
  | 11 => [exchangeAxes 83, exchangeAxes 48, exchangeAxes 96]
  | 12 => [exchangeAxes 80, exchangeAxes 96, exchangeAxes 32, exchangeAxes 16]
  | 13 => [exchangeAxes 101, exchangeAxes 48, exchangeAxes 32, exchangeAxes 16]
  | 14 => [exchangeAxes 82, exchangeAxes 98, exchangeAxes 48]
  | 15 => [exchangeAxes 82, exchangeAxes 98, exchangeAxes 16]
  | 16 => [exchangeAxes 101, exchangeAxes 50]
  | 17 => [exchangeAxes 101, exchangeAxes 50, exchangeAxes 16]
  | 18 => [exchangeAxes 99, exchangeAxes 66, exchangeAxes 16]
  | 19 => [exchangeAxes 33, exchangeAxes 16, exchangeAxes 48]
  | 20 => [exchangeAxes 16, exchangeAxes 33, exchangeAxes 48]
  | 21 => [exchangeAxes 83, exchangeAxes 49, exchangeAxes 97, exchangeAxes 32]
  | 22 => [exchangeAxes 83, exchangeAxes 99, exchangeAxes 16, exchangeAxes 32]
  | 23 => [exchangeAxes 98, exchangeAxes 50, exchangeAxes 83, exchangeAxes 66, exchangeAxes 16]
  | 24 => [exchangeAxes 101, exchangeAxes 16, exchangeAxes 33, exchangeAxes 48]
  | 25 => [exchangeAxes 98, exchangeAxes 82, exchangeAxes 65]
  | 26 => [exchangeAxes 50, exchangeAxes 83, exchangeAxes 66, exchangeAxes 16]
  | 27 => [exchangeAxes 82, exchangeAxes 65]
  | 28 => [exchangeAxes 50, exchangeAxes 33, exchangeAxes 16, exchangeAxes 64]
  | 29 => [exchangeAxes 50, exchangeAxes 65]
  | 30 => [exchangeAxes 67, exchangeAxes 32]
  | 31 => [exchangeAxes 33]
  | 32 => [exchangeAxes 49, exchangeAxes 32, exchangeAxes 81, exchangeAxes 64]
  | 33 => [exchangeAxes 83, exchangeAxes 48, exchangeAxes 16, exchangeAxes 97, exchangeAxes 32]
  | 34 => [exchangeAxes 101, exchangeAxes 33, exchangeAxes 48]
  | 35 => [exchangeAxes 80, exchangeAxes 96]
  | 36 => [exchangeAxes 83, exchangeAxes 99, exchangeAxes 33]
  | _ => []

def ruleCheck (a b : Claim) (c : ColumnInfo) :=
  let packed := c.2.2.2.1
  let ms := faceMoves (packed / 128) ++ fixRows (c.1 ||| (packed % 128)) c.2.1
  checkMap ms (vars a.2.1.mask) a.1 (vars b.2.1.mask) b.1 &&
    (movedWord ms (subcube c.1 c.2.1) == one) && properB b.1 &&
    (c.2.2.2.2 == b.2.1.cap+1)

def Solved (a : Claim) := Lower true (vars a.2.1.mask) a.1 (a.2.1.cap+1)

theorem ruleChecked {a b : Claim} {c : ColumnInfo} (prev : Solved b)
    (h : ruleCheck a b c = true) :
    Slice true (vars a.2.1.mask) a.1 (subcube c.1 c.2.1) c.2.2.2.2 := by
  simp only [ruleCheck,Bool.and_eq_true,beq_iff_eq] at h
  rw [h.2]
  exact slice_correct h.1.1.1 h.1.1.2 (proper_of _ h.1.2) prev

def localCheck (a : Claim) :=
  a.2.1.mode && properB a.1 && checkEssential a.1 (vars a.2.1.mask) (essentialData a) &&
  ((essentialData a).map Prod.fst == vars a.2.1.mask) &&
  indexedRoot a.2.1 a.2.1.cap 0 (vars a.2.1.mask)

def columnsCheck (book : Nat → Claim) (i : Nat) :=
  let a := book i
  a.2.1.cols.all fun c => decide (c.2.2.1 < i) && ruleCheck a (book c.2.2.1) c

def Resolved (a : Claim) :=
  Impossible true a.1 a.2.1.cap (vars a.2.1.mask).toFinset ∧ Solved a

set_option maxHeartbeats 2000000 in
theorem resolve {book : Nat → Claim} {i : Nat}
    (previous : ∀ j < i, Resolved (book j))
    (lc : localCheck (book i)=true) (pc : Matches (book i).2.1 (book i).1)
    (cc : columnsCheck book i=true)
    (rows : ∀ k ≤ (book i).2.1.cap, checks (book i).2.1 (book i).1 k 0 ((book i).2.1.levels k).1 = true) :
    Resolved (book i) := by
  let a := book i
  change localCheck a = true at lc
  simp only [localCheck,Bool.and_eq_true,beq_iff_eq] at lc
  have hm : a.2.1.mode = true := lc.1.1.1.1
  have cols : Rules a.2.1 a.1 := by
    intro c hc
    rw [hm]
    have h := List.all_eq_true.mp cc c hc
    simp only [Bool.and_eq_true,decide_eq_true_eq] at h
    exact ruleChecked (previous _ h.1).2 h.2
  have noRun := rootDone pc cols rows lc.2
  rw [hm] at noRun
  refine ⟨noRun,lower_impossible (proper_of _ lc.1.1.1.2) (essential_plain lc.1.1.2).1
    (essential_plain lc.1.1.2).2 ?_ noRun⟩
  intro v hv
  apply essential_ok lc.1.1.2 v
  rw [lc.1.2]
  exact List.mem_toFinset.mpr hv

theorem extendResults {book : Nat → Claim} {i : Nat}
    (prev : ∀ j < i, Resolved (book j)) (this : Resolved (book i)) :
    ∀ j < i+1, Resolved (book j) := by
  intro j hj
  by_cases h : j=i
  · exact h ▸ this
  · exact prev j (by omega)

def layers0 : Nat → Packing
  | 3 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x7 | _ => 0)⟩
  | _ => emptyPacking
def index0 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g0 : Forest := ⟨37,3,(fun | 0 => (0xffffffffffffffffffffffffffffffffffffcf,0xffffffffffffffffffffffffffffffffffffc5) | 2 => (0xfffffffffffffffffffffffffffffffffffff3,0x12) | 5 => (0x3c,0x28) | _ => (0,0)),[],[],layers0,index0⟩
def claim0 : Claim := (0xfafafafaa0a0a0a0fafafafaa0a0a0a0fafafafaa0a0a0a0fafafafaa0a0a0a0fafafafaa0a0a0a0fafafafaa0a0a0a0fafafafaa0a0a0a0fafafafaa0a0a0a0,g0,34359754756)

def layers1 : Nat → Packing
  | 3 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0xf | _ => 0)⟩
  | _ => emptyPacking
def index1 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g1 : Forest := ⟨15,3,(fun | 0 => (0xffffffffffffffffffffffffffffffffffff9f,0xffffffffffffffffffffffffffffffffffff8b) | 1 => (0x64,0x46) | 2 => (0xffffffffffffffffffffffffffffffffffffc7,0x44) | 3 => (0x78,0x30) | _ => (0,0)),[],[],layers1,index1⟩
def claim1 : Claim := (0xeea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0,g1,2114564)

def layers2 : Nat → Packing
  | 4 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x2f | _ => 0)⟩
  | _ => emptyPacking
def index2 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g2 : Forest := ⟨53,4,(fun | 0 => (0xffffffffffffffffffffffffffffffffffffc3,0xffffffffffffffffffffffffffffffffffff41) | 2 => (0xffffffffffffffffffffffffffffffffffff3f,0x16) | 4 => (0xcc,0xc8) | 5 => (0xf0,0xa0) | _ => (0,0)),[(16,0,0,16,4)],[],layers2,index2⟩
def claim2 : Claim := (0xfafafafaf0f0a0a0fafafafaf0f0a0a0fafafafaf0f0a0a0fafafafaf0f0a0a0fafafafaf0f0a0a0fafafafaf0f0a0a0fafafafaf0f0a0a0fafafafaf0f0a0a0,g2,35433496580)

def layers3 : Nat → Packing
  | 4 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x2f | _ => 0)⟩
  | _ => emptyPacking
def index3 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g3 : Forest := ⟨43,4,(fun | 0 => (0xffffffffffffffffffffffffffffffffffff2d,0x24) | 1 => (0x36,0x24) | 3 => (0xffffffffffffffffffffffffffffffffffffc7,0xffffffffffffffffffffffffffffffffffff43) | 5 => (0xf8,0x98) | _ => (0,0)),[(1,0,0,897,4)],[],layers3,index3⟩
def claim3 : Claim := (0xffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00,g3,34361836552)

def layers4 : Nat → Packing
  | 4 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x2f | _ => 0)⟩
  | _ => emptyPacking
def index4 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g4 : Forest := ⟨43,4,(fun | 0 => (0xfffffffffffffffffffffffffffffffffffe37,0xfffffffffffffffffffffffffffffffffffe13) | 1 => (0xfffffffffffffffffffffffffffffffffffe49,0x0) | 3 => (0x18e,0x8c) | 5 => (0x1f0,0x160) | _ => (0,0)),[(2,0,0,258,4)],[],layers4,index4⟩
def claim4 : Claim := (0xffeeffeeeecceeccffeeffeeeecceeccffeeffeeeecceeccffeeffeeeecceeccffeeffeeeecceeccffeeffeeeecceeccffeeffeeeecceeccffeeffeeeecceecc,g4,34361835528)

def layers5 : Nat → Packing
  | 3 => ⟨8,3,2,0,0,7,0,(fun | 0 => 0x80208021002104200000090e14182430300f0882429074441314c3924099261c5214c9319da826890cdd45344825ea49a2211e3549110 | _ => 0)⟩
  | 4 => ⟨28,2,2,0,0,9,0,(fun | 0 => 0x3208c422108c8230088023108c021008842200840200441204c1000000000000000000853f1dce0693116ca84d230fc7033170a448210f06c30150903c18090300c00f930483e4c110f920443d4c521f531443d48510ed32487b4c920ed2148374c931dd324c374c530bd34486f4d120bd34442f49110bf404cafd0131bf40486fd0532bf414c2fd0520bf424c6fd0930be24442f8d121be34482f8d110 | _ => 0)⟩
  | 5 => ⟨6,1,2,0,0,7,0,(fun | 0 => 0x21a11064445811844465011a204b521b242403e997d31fa61f487e907d10 | _ => 0)⟩
  | 6 => ⟨1,0,2,0,0,1,0,(fun | 0 => 0x7208f | _ => 0)⟩
  | _ => emptyPacking
def index5 : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 4 12 2 7 3 0 (fun | 0 => 0xd8af8681cd7ba20000081 | _ => 0)
  | 5 => lookupWord 12 39 3 9 5 0 (fun | 0 => 0x28ee30270251ce8a12e24c6c7e6095c5003c00101f68000062c48012200bb8002d4cfa8cc0000005ec3479000080e52 | _ => 0)
  | 6 => lookupWord 6 12 1 7 3 0 (fun | 0 => 0xba4000614c03a00f00 | _ => 0)
  | _ => fun _ => none
def g5 : Forest := ⟨101,6,(fun | 0 => (0xfffffffffffffffffffffffffffffffffff0cf,0xfffffffffffffffffffffffffffffffffff045) | 2 => (0xfffffffffffffffffffffffffffffffffff333,0x112) | 5 => (0xc3c,0x428) | 6 => (0xfc0,0xa80) | _ => (0,0)),[(1,0,0,385,4),(4,0,0,516,4),(32,0,0,672,4),(64,0,0,64,4)],[],layers5,index5⟩
def claim5 : Claim := (0xfffffffffafafafafafafafaa0a0a0a0fffffffffafafafafafafafaa0a0a0a0fffffffffafafafafafafafaa0a0a0a0fffffffffafafafafafafafaa0a0a0a0,g5,4432406265860)

def layers6 : Nat → Packing
  | 4 => ⟨5,2,3,0,0,5,0,(fun | 0 => 0xc498605ed4132bba8a876f52502bc6a884f91521 | _ => 0)⟩
  | 5 => ⟨10,1,3,0,0,7,0,(fun | 0 => 0x4100020401000404030634074c13203440500fd43fd42fd41fd40fd32fd31fd30fd21fd20fd10 | _ => 0)⟩
  | 6 => ⟨1,0,3,0,0,1,0,(fun | 0 => 0x468815f | _ => 0)⟩
  | _ => emptyPacking
def index6 : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 7 1 7 3 0 (fun | 0 => 0x1223240041100 | _ => 0)
  | 6 => lookupWord 3 12 3 8 4 0 (fun | 0 => 0x10ea401c312f0ca26010ce88100 | _ => 0)
  | _ => fun _ => none
def g6 : Forest := ⟨31,6,(fun | 0 => (0xffffffffffffffffffffffffffffffccc03fff,0xffffffffffffffffffffffffffffffc4c01363) | 1 => (0xffc0c0,0x54c2ca) | 2 => (0xfffffffffffffffffffffffffffffff30c00ff,0x110c889c) | 3 => (0x3c0fff00,0x380b2c10) | 4 => (0x3ff00000,0x2ea23020) | _ => (0,0)),[(1,0,1,3585,4),(2,0,1,3714,4),(4,0,1,1284,4),(8,0,1,3848,4),(16,0,1,16,4)],[],layers6,index6⟩
def claim6 : Claim := (0xfefceea0fefceea0fefceea0fefceea0fefceea0fefceea0fefceea0fefceea0fefceea0fefceea0fefceea0fefceea0fefceea0fefceea0fefceea0fefceea0,g6,538985476)

def layers7 : Nat → Packing
  | 5 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index7 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g7 : Forest := ⟨55,5,(fun | 0 => (0xfffffffffffffffffffffffffffffffffffd8f,0xfffffffffffffffffffffffffffffffffffc8d) | 1 => (0xfffffffffffffffffffffffffffffffffffc6f,0xfffffffffffffffffffffffffffffffffffc47) | 2 => (0xfffffffffffffffffffffffffffffffffffe53,0x52) | 4 => (0x39c,0x388) | 5 => (0x3e0,0x320) | _ => (0,0)),[(2,0,2,2,5)],[],layers7,index7⟩
def claim7 : Claim := (0xfefefefefcfca0a0fefefefefcfca0a0fefefefefcfca0a0fefefefefcfca0a0fefefefefcfca0a0fefefefefcfca0a0fefefefefcfca0a0fefefefefcfca0a0,g7,34896627716)

def layers8 : Nat → Packing
  | 4 => ⟨1,2,3,0,0,1,0,(fun | 0 => 0x5ed4142 | _ => 0)⟩
  | 5 => ⟨1,1,3,0,0,1,0,(fun | 0 => 0x19006fd42 | _ => 0)⟩
  | 6 => ⟨1,0,3,0,0,1,0,(fun | 0 => 0x8d111f | _ => 0)⟩
  | _ => emptyPacking
def index8 : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => some (0,0)
  | 6 => fun _ => some (0,0)
  | _ => fun _ => none
def g8 : Forest := ⟨59,6,(fun | 0 => (0x107a,0x101a) | 1 => (0xffffffffffffffffffffffffffffffffffc19f,0x8e) | 3 => (0xffffffffffffffffffffffffffffffffffee23,0xffffffffffffffffffffffffffffffffffc621) | 4 => (0x303c,0x3430) | 5 => (0x3fc0,0x2940) | _ => (0,0)),[(0,16,4,0,5),(2,16,0,258,4),(17,0,0,913,4),(8,0,1,1160,4),(32,0,1,1312,4)],[],layers8,index8⟩
def claim8 : Claim := (0xffeeffeeeeccee00ffeeffeeeeccee00ffeeffeeeeccee00ffeeffeeeeccee00ffeeffeeeeccee00ffeeffeeeeccee00ffeeffeeeeccee00ffeeffeeeeccee00,g8,34898707464)

def layers9 : Nat → Packing
  | 6 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x209f | _ => 0)⟩
  | _ => emptyPacking
def index9 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g9 : Forest := ⟨47,6,(fun | 0 => (0xffffffffffffffffffffffffffffffffffe0cf,0xffffffffffffffffffffffffffffffffffe045) | 1 => (0xffffffffffffffffffffffffffffffffffe333,0xffffffffffffffffffffffffffffffffffe113) | 2 => (0xfffffffffffffffffffffffffffffffffff433,0x1032) | 3 => (0x183c,0x1028) | 5 => (0x1fc0,0xe80) | _ => (0,0)),[(5,0,0,901,4),(10,0,0,10,4)],[],layers9,index9⟩
def claim9 : Claim := (0xfffefffeeea0eea0fffefffeeea0eea0fffefffeeea0eea0fffefffeeea0eea0fffefffeeea0eea0fffefffeeea0eea0fffefffeeea0eea0fffefffeeea0eea0,g9,34361852932)

def layers10 : Nat → Packing
  | 5 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index10 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g10 : Forest := ⟨47,5,(fun | 0 => (0xfffffffffffffffffffffffffffffffffff0cf,0xfffffffffffffffffffffffffffffffffff047) | 1 => (0xfffffffffffffffffffffffffffffffffff111,0x0) | 2 => (0x222,0x0) | 3 => (0xc3c,0x438) | 5 => (0xfc0,0xb80) | _ => (0,0)),[(2,0,4,3970,5)],[],layers10,index10⟩
def claim10 : Claim := (0xfffefffefefcfefcfffefffefefcfefcfffefffefefcfefcfffefffefefcfefcfffefffefefcfefcfffefffefefcfefcfffefffefefcfefcfffefffefefcfefc,g10,34361835528)

def layers11 : Nat → Packing
  | 7 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index11 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g11 : Forest := ⟨117,7,(fun | 0 => (0xffffffffffffffffffffffffffffffffffe4ab,0xffffffffffffffffffffffffffffffffffe409) | 2 => (0xffffffffffffffffffffffffffffffffffe357,0x116) | 4 => (0x1464,0x1460) | 5 => (0x1878,0x860) | 6 => (0x1f80,0x1280) | _ => (0,0)),[(16,0,5,16,7)],[],layers11,index11⟩
def claim11 : Claim := (0xfffffffffafafafafafafafaf0f0a0a0fffffffffafafafafafafafaf0f0a0a0fffffffffafafafafafafafaf0f0a0a0fffffffffafafafafafafafaf0f0a0a0,g11,4433480007684)

def layers12 : Nat → Packing
  | 5 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index12 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g12 : Forest := ⟨118,5,(fun | 1 => (0xfffffffffffffffffffffffffffffffffff9a9,0xfffffffffffffffffffffffffffffffffff8a1) | 2 => (0xf6,0xa2) | 4 => (0xffffffffffffffffffffffffffffffffffff07,0x704) | 5 => (0x638,0x218) | 6 => (0x7c0,0x540) | _ => (0,0)),[(2,0,2,4482,5)],[],layers12,index12⟩
def claim12 : Claim := (0xfffffffffcfcfcfcfcfcfcfcfcfc0000fffffffffcfcfcfcfcfcfcfcfcfc0000fffffffffcfcfcfcfcfcfcfcfcfc0000fffffffffcfcfcfcfcfcfcfcfcfc0000,g12,8865349634048)

def layers13 : Nat → Packing
  | 7 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index13 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g13 : Forest := ⟨103,7,(fun | 0 => (0xffffffffffffffffffffffffffffffffffc297,0xffffffffffffffffffffffffffffffffffc211) | 1 => (0xffffffffffffffffffffffffffffffffffc31b,0xffffffffffffffffffffffffffffffffffc213) | 2 => (0xffffffffffffffffffffffffffffffffffcc63,0x422) | 5 => (0x307c,0x104c) | 6 => (0x3f80,0x2980) | _ => (0,0)),[(2,0,5,2,7)],[],layers13,index13⟩
def claim13 : Claim := (0xfffffffffefefefefefefefea0a0a0a0fffffffffefefefefefefefea0a0a0a0fffffffffefefefefefefefea0a0a0a0fffffffffefefefefefefefea0a0a0a0,g13,4432406269956)

def layers14 : Nat → Packing
  | 7 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index14 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g14 : Forest := ⟨107,7,(fun | 0 => (0xffffffffffffffffffffffffffffffffff852d,0x424) | 1 => (0x636,0x424) | 3 => (0xffffffffffffffffffffffffffffffffff98c7,0xffffffffffffffffffffffffffffffffff8843) | 5 => (0x60f8,0x2098) | 6 => (0x7f00,0x5300) | _ => (0,0)),[(1,0,5,897,7)],[],layers14,index14⟩
def claim14 : Claim := (0xffffffffffeeffeeffeeffeeee00ee00ffffffffffeeffeeffeeffeeee00ee00ffffffffffeeffeeffeeffeeee00ee00ffffffffffeeffeeffeeffeeee00ee00,g14,4432408347656)

def layers15 : Nat → Packing
  | 7 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index15 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g15 : Forest := ⟨107,7,(fun | 0 => (0xffffffffffffffffffffffffffffffffff0637,0xffffffffffffffffffffffffffffffffff0213) | 1 => (0xffffffffffffffffffffffffffffffffff0849,0x0) | 3 => (0x318e,0x108c) | 5 => (0xc1f0,0x4160) | 6 => (0xfe00,0xac00) | _ => (0,0)),[(2,0,5,258,7)],[],layers15,index15⟩
def claim15 : Claim := (0xffffffffffeeffeeffeeffeeeecceeccffffffffffeeffeeffeeffeeeecceeccffffffffffeeffeeffeeffeeeecceeccffffffffffeeffeeffeeffeeeecceecc,g15,4432408346632)

def layers16 : Nat → Packing
  | 5 => ⟨70,4,5,0,0,9,0,(fun | 0 => 0x130803c30482000000000c100001820304000000000000005020304000060800000304000000000000000000000000000000000000000000000000000000000003cdd7e8f2f8bbfdceab499ec7e02f574b75a2c55cab542953b9649a411185c15fef075391bcd8693318cc05d2d15ca8512712c9045210fc78391b0cc602d1509c48210f06c30150903c18090300c00fc1104c930487d84415254121f511054d504c7d44415354530f3110551514c3d24c15254132e6960549504cb9a5815254121f492054d504cb9a4815654132e596054d504cb965815354131e593055953443964c15654132e595654d30943965593054e10e59564c150ccb964d95054e10e593654153883964195354331e590654d50ccbd14855354532e556154d514cb955855354530e5531559534438d5855454530e3516551518c34d45d5498151f0d32551524c38b5895454930e2d2655152cc34b49d5498d52c3d27552564c30f45d54959308fb805d9534874e5537058d528f987d832054e3ee017654b31e553154f605478b54954d8132f0d3255152cc3724cb7054b308fb8049f6154f395d921cc620e593054f615439654153d8530e59305436254f9654153d89308df835d9524439a48150d8d52d1d54dcd605463761b73546308df835d9518838d545548d9108de3845f62543cc4415454630dd110dcd518c21f961764c910c3d5495d364830f552574d910e3910552564c3874c95495930e3954842564c3875533295930c3d5495d368430f552574da20c3d5495d06cc70f5525741b32c3d5485e564c30f5522795930 | _ => 0)⟩
  | 6 => ⟨377,3,5,0,0,13,0,(fun | 0 => 0x27e9bc4c886bd36552209fa6f2b221b71cd56442ee39ac2a84fd76483319faec904a73f49f6054e7e93ec0a8edd2654f30d7a4caa6613f49f6154e7e93ec2a84fd27d8530dba4ca9e632fdd954cca7e93ec6a8cfd27d8d509fa4f1b2213f49e564c36e9326129cfd279591097eecaa4213f45f6054e7e8bec0a94fd17d81329fa2fb12a73f45f625427e8bec4984fd17d8d529fa2fb1aa1af459548c27e8bcac994fd17959309fa0fb0aa73f41f6154a7e83ec2996f50648731dba0ca9e63af41954cc67e83ec4a9cfd07d8951dba0ca9e65af41954ccade83ec6aa4fd07d8d549fa0fb1aa53f41f635467e83cac996dd064ca53df0e0ab2657e1c16254e5fbb2a8186fb7055932bf6e0b12a77edc16354a7db82ac995fb70559329fee0ab2653fdc1564c77ca06c0a9edd32d81539fee0ab243be4436054b76996c0a96f531d8151dea43b02a39f54f605467fb826c90ef910d8132ddaa5b0265b754f604cb5eaa6c0997cd3254b30ebaa6a8661775cd52cc3ce992a99873d5454b30bf6e0a96613f5db31882fbb8ac8a9cff71559329fee2ab261bd4876154e7fb8aac906ed32d8552df261b0aa19f54f615427fb8a6c906ed52d8532dbaa7b0a65fc443614c37ca86c2986f561d8530dea43b0a61bd443614c36ea9ec2986bd54d85309fee29b4413f5db319427fb8a6d287e52154b31faa42a9e63d754d50cc7ec982a7087795054e10bf2e0a9c21ee4c154842f7b92c8a84ff72559319fee4ab261b74c36254f3ea86c4a9cff7255910dea21b12a3bb487625427fb926c886f950d8930f9a65b1261bb58b624c376996c4986ed21d8930dbaa7b1261af553624c3ec982a19975d5354332bbae6a8665e74c154ccb7ca844c886f551899109fc4e836633f5da2094e7f13a0d29fe95048620ef2a0a9c41f948551883f290e63104fe17d89309fee6ab2433fdcd564837690ec6a96ed20d8d52cfaa1b1aa5b7dcd56442efb9ac0a8ddf73585509bee6ab2213fdcd56442efb9aac886f510d8d51dba65b1aa3be443635436ea1ec6a84fe3749910df2a11b221bd546364436e9946c886bd548d910fe220a8c61de541538c2fcb82a3187b91055230e7aa8a8c6177dcd518c2efb9aa121ebd5391921d7aa123243af4c246486fdb82a7204fe574d9219fcae9b241bb486564cb76904ac996dd30959329fcae9b221de542564c37c884ac986dd3295930ebaa72b2618f552564c33eaa4ac9867d5695930cfaa72b2619f542564c27f2ba0d29f3d5495930df4212b261b7cca564c27f2ba6d084fe574da209fcae9b481f34c92094eee9ba4129ddd3788253bbee4984a73f95d264437c984ac886f53195910dea432b2213f95d06cc67f2ba0d994fe5741a43fe22098ca17e5c131942fc83e63285fb714c2509fc2f2b261cf552605467f13cac9873d5498d52 | 1 => 0xe254128891848623811a88c845e228110887843621410688184061fc0fc87d83e61ec0f487983c61e00ee87683ae1d40e887383961c80de86c835e1ac0d486883361940c8862830e1840c085f82ee1700b685a82ce1640b085682ae14c0a4851827e13c09c84c825e12c092848823e11c08a843820e10407e83d81de0ec07483881b60d806883381960c8062830817e0b405882b81560a80528278136098048822810607c03a81b80ce06002e81680ae054028813809604802280e806e03401880b8056028012808803e01c00c80380160007f11054131fe220a8a61fc44150487f88826090f692054950fd240a8265d64c153543ec982a0996f96054132df2c0a8263de541534c3bca82a4985f97054530df2ac984a1be559308437c9b2a1086f93654220df2c0a8243de54153483ec982a6887d9304c910ef2a0a9a21de54152442fcb82a6886f95644230f7260aa221be4d9109437c8b2a1106f91654230df22c984a1be41950cc77c832a1996f90654243bf20f31aa1f9485514cbaa98aa6a8ef56154532deac2a8a61cd545544c6fab8aa098ef56154520eeaa2a9a437d5c5504877aab24398fe52154910fca4299221f54c5534439aa8aa8887755154d10beae2a9a217d5c552442fab8a64887b53155110d6a2caa061bd459518837a8b263106f51654630dea2ca9c817d45e605477a8b263287cd3254930ddac4a9263bb589524c396a92a89976d5254132bdae4a8a657b5c9504cb76932a4886ed264c910f9a64a9a43f34c930487b6a92a090ded7254d21ddaac90c41bb4d921883e6992a69072d5255120bdae4a9a41eb4c95448356932a8186ed2654b30dda4ca9663bb49920cc776932a121ded2798d52dda4c904a7b74d9534876e9b2a69075d5354532ebaa6a8265775cd504cb6eab265986dd3654d10ebaa6a8263d754d514c3aea9aa0985dd7354930dbaac984a7b755930ccbce992a8986dd3654e10dba6ca9c41b74d953902ee9bcc0a9f3d5458d52e7aa8b02a5cf551635479eaa2c0a8e3d7455830c7aacaa0612f55e464875ea32a7086bd4654332cfaaca9a219f559504cabeabcc6a867d5654331cfaaca9c215f55e60546beabcc6a967d5654332cfaaca9c415f55e6054f3eab2a121e7d5654e409faeca9a433f5d9534827eb3cc4a9cfd7654d109facf302a73f5d9538427ebb2a7104fd7654e409faeca92213f5d952cc27ebb2a598cfd67981519faeca8c413f5d9518c27ebb2a198cfd76543329faeca84873f55f604ca7eabec2994fd57d85309faafb12613f55e264427eabc6c884fd764c910d7a6caa241af4d9544427ebb263104fd764c650e7aa8a9261cf551514c35eab2612a5bd3718154b7ae031aa96f4df605527e9bec0aa4fd37d81529fa6fb02a33f4df6154a7e9bec2a86bd36552109fa6fb12a33f4df6254 | 2 => 0x4010b0f080c402020c18543000c10304181001810304000003040004c3c213044c1000400704003040c1000c103040c100043c2820312083c0c2030448583c306043c0c20004501003c2421410080160f08005043c2c20b042c11012083c0c205040c100001050400f03080c1170f0800f0e081810f03083811204383c201044c10000100405c3c305042c11210080c10f03081410000105040c103045011404041000c100005041410304008040c103040c10004605c403151008604821615120c484021210081010000604141000414105041c14208060814105040010404101040b0800504000000081040e08005041810604000002040000000001064203040c100017045814304380c20b03080000000000c10004000040c1000000000000c100141000400103043c6020402080040208000100820f15080040208100820104181010400000402080000010004041000c1000000c1000000000000121008141000a3040000020584100001000010400000163058c10000504141002010000000048042003c182000003c103040000010104001000c1000003c10000000000000000000f050840002000000010004001000c100000003043c1000000003c100100820000004000181000a304000001058010204063058c10104000141060400704000000000100820000000014100006040810204001000400143040c1000000000000001008200000000000000000301c2003420286042ea15909684041ea0b905682440ea05902680c402a008ffe7fc3fa9fc8fde7e43ee9f58f9e7cc3e29f08f767b43d89ea8f4679c3ca9e28efe7743b69d78eae74c3a29cf8e767303929c88e2e7143869c08df66f43749b78dae6d03669b18d7e6bc3589aa8d3e69c3489a28cfe6783389998cbe65832a9938c9663c31a98b8c4661c3089828c0e6002fc97c8bd65e42ee9758ba65cc2e49718b7e5b82d896b8b4e5a02cc9648b1657c2b89598aae54c2a094e8a6e5342969498a3e51828894189f64f427693989be4d826693289864c025e92e896e4b02529288936494246922890e48423e91e88ee47423891b88d646022c914889e44c22290f886e42c210907883641820a904881e4082008ff87ee3f01f68fa87ce3e41f08f787b63d41e88f287863bc1da8ea873e39c1c88e387163801ba8dc86ce35c1aa8d3868e3441a08cf86663301968c9863e31818a8c386163081828bf85f62f817a8bc85de2ec1748b985b62d41688b3858e2c41608af856e2b01568a985462a014c8a5852628c14289f84f627813889a84ce26012e89684a | _ => 0)⟩
  | 7 => ⟨201,2,5,0,0,13,0,(fun | 0 => 0x1585ab1d4eaa3f4fda74d31e93d47ca2d50fe8494109f74efa7473819b34d12645307972cb0e54328693249424331f08e3c6b23231768b144ca2130e7862c2aa0e705881b4051ff2fe57e53ebdf1af727abbcd5e26ef876ebaedd32e85738b975c92e2770637a9b90db46ccb615ad4d5669db4659fccea660b299916c7062e312185ac125fbaf8d790bb45ccae156c6b48596ac2d5e0ad5560aa7d516a7052e28e94309f64ea270134a9834b7a55128092548523a118c8a444821d50a683840e9fd0fb27be3ce1e04ecc7443949c38dca6ca35b1a6ccf265e31e18a0c366072f99760b7a5a92ca95e8acc54429494389d84d125e92c092a48122f911084440e1fd0f7c7963b01ce0e206da35219b8c705f42d815e8a884f226512508d84361f90ef070c35018d0b5852425c11307c03901a00ae04981e00c805002180a001a000fe54130fe54120fe54110fe4c110fd54531fd54521fd54510fd4c510fd48510bd45830bd45a40fb54932fb54921fb4c921fb54920fb4c920bb49830bb49a43f754d32f754d31f754d30f74c930cf55152cf55151af51830af51a10af51b32df54d51df54d50df549509f55830bf55932bf55931bf55930ff59153ff58953ff58553ff58153bf55921bf55920ff58d52ff58552ff58152bf55910ff58d51ff58951ff58151ff59150ff58d50ff58950ff58550bf55830bf55b30bf55b31bf55a10bf55b32bf55a20bf55a30bf55a43bf55a40ff54143ff54d42ff54141ff54d40bf4d921bf4d920ef55132ff55932ff54d32ff54532ff54132ff58532ff58132bf4d910ef55131ff54931ff54131ef55130ff55130ff55930ff54d30ff54930ff54530ff54130bf4da30ff51930ff58930ff4c930ff58530bf4da10bf4da20bf4da40bf4da50ef18d54bf49910ff54d21ff54121ff4c121ef55120ff54d20ff54520ff4c520bf49b30bf49b31bf49a53ef55110ff54d10ff54910ff55910ff54110ff4c910ff4d910ff4c110ff49910bf45a20bf45a30bf45a50bf41b31bf41b32bf41a43bf41a53ef18154ef55030efd8154bfd8154bfd8153bfd8152bfd8151bfd8132f754f30f74cb30ef55330ff54b30ff54330bfd8553bfd8552bfd8550bfd8532bfd8530ffd8530fd48731f754f31ef55331ff54b31ff54331ff48331fe54210fe4c210ef55210ff54e10bfd8953bfd8951bfd8950bfd8930ffd8930f754f32f74c332ef55332ff54332bf89910fe54220fb48620ef55220ff54e20ff54620ff4c620ffcc620efd8d54bfd8d54bfd8d52bfd8d51bfd8d50bf8d910fe54230fe44230ef55230ff54e30ff54630ff91930ff54243af91921ff54e40ef4ca54ef4c254ef44254bf95932bf95930ff95930f74ca53f74c253ff48253ff88253bf95910fe4c250fe44250ff4c650ffcc650ff98d50ff98151ff98d52ff98153 | 1 => 0x1431546215464032a4c390808c62624906591920cb0a463c4265858f4628f26483262880f1049208a92163c4285c70f46297128c788504921e217464031e50806288046080e1e218282094146318464830c14c2310a0a201832e407880cb121e206163c32a4858f10c101c3c43058192102982a1972a0c8082880460a17828c38b1d1982c2490a8cc15043c532109065cc140cc16141982a1172c4430b1e3232e5451014c092e5042e5868f10b9512195265a0231038730585065cb0c1e2151458988642100cc1508b95121962a4c308545101049230189304830c1c81510288246041454806288150c298104840c543901020e08684086040820b08a151e4842858806385a31e218125ca0850c0458a0f0ca9408a121e194121132e483168c7921078a2e19514119084882314584321a3305430a18c0618b8414b04182950c18a2018e082c32824228184864c5040c5100cb10087030e40486288062c7990c9981e40430387865458f0c58f087231e404302421e24b0628484501892420f2a509090c4942420e168c788609845c98f0cb0a2a4c426542284c7864c5044c28a0c9901e18f304c8084c18a20243144c8085c9040c4920c583104848624906387990cca31e4880a387990c30f32182c23cc08288170c7082c1e32c40a08145180ca0a201991620c1214b890c1862a109246030c14797107082a1912a507885c904281243c23048216607863c3170c315083090a0102a18a2010e2a1c808382980c587301860a3cb08288150cb1008483049180c49208598104841618a8640c131e215201101e10e2a3c30a6021e14b0614504182842c7990c28f3218b0e5c31248b060b00f2a2632e48988184950c989241991c1ca901429808b0a0a184161090c543c64880f10505301c32440386488070c9100d18b0e5040c2c7a310305461c3284832b0c90624304143048c7082621886403864c8062828418284541181cb06344170cc03606af5d6eeb4 | _ => 0)⟩
  | 8 => ⟨28,1,5,0,0,10,0,(fun | 0 => 0x20cf0ce2c20cf1451188434861970500cf1855804833c61845600d01a32ce3c48ce40f1232d23c48ce2cf1140632523c61633d21048d24044428ca24f1868cf4044c08ca40f1820400ca4068c94831633d21028ca0101428c90521468cf4048ca4030632ce3c502338b3c54420d24051610d2106803404e8b7ed532ac02d6ae29a9f25e8d2167e1ce6c1865714449902378c02a0841803c07800deaa7f553faa7fd52fea8ff543fa87fd42fea0ff503fa65fd31fe987f487fa41fd10fe187fcc3fe63fe10ff997f883fc61fe43ff206f953fca7fe50 | _ => 0)⟩
  | 9 => ⟨1,0,5,0,0,1,0,(fun | 0 => 0x3104023f | _ => 0)⟩
  | _ => emptyPacking
def index16 : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 25 81 6 11 7 0 (fun | 0 => 0x10cad9e4328062a0700000040105a84000a7800c34d38a5097e82d89ca089c0705400354eb59206b5d731be3b08c82c36001ee21593d00000248d3ac4588760ba087320c0041611f86593145912a7c92095b4a00206b0cb2466b04000f840039b81747ec6198231d786fa53b3b20cab0000f00400001c09c02400c10a0cf5010807c1 | _ => 0)
  | 7 => lookupWord 125 449 7 13 9 0 (fun | 0 => 0x4a1417383e000110e4daa240002b7b431214a1b701758a0964889a7f4de23e51b579841bc98f59804201d16568bb6cb456587c7a72c816e88cb5d5196db01be66b941ccc6444679d5462c7e2d22fa8f72d015688c84f0001e8dd52833040e081011e50e29c9494a0b36ea76ebc0c0f1b3423247696a3438d400091a10c8d06a9375a48ee19fa9494d14880025dde5200000024bc0000000cfa4e600012a04840000009764382447efe7716cd660b2fa01bcc3b4ad40b329ddc0eaece95a60b3a09a8449bc2cab4216c6323b328000a90b15e97d93f698c624450ee96bba9e02b986129bc6b0000000662256f2669ec000f3b5ddf17d2fce0c3404ec9ad8483dd83d660b8589cca7e4a3658a1e3c98734cc120f19387d2b0f5c814083940e19074c9c418a6000485e190a0465b75500002c10b402a86b1d3d39f81fcdd6300551a23400016eea7390f8f1665491143c25eab500000008772ff0007511d0d64f46f09440000e314bba71ecca3498850ab026016d72a8a462e769c0d422805b2fda04fc458020f0d144d1e259863a2d33d098a00000000018282e6013f9c69260007130000152887e0f2960000cbc37de5ac00000005f8d6c0d43300001d580000000001523db547571fa24a88404eb0a8c12667694d9380029440009b950f4000f45c9c237249200056808e99f2a9a1afa893e800000006c2f996a61652f9f8dea76331e39b3a72000f4743500010e133ec02ad58edb5b098c5458f0dc2ee492dabf18706000000095000011ca18e448dbb49a7d0a00049d03360f728f0000000000480ca5800000128400070180018e70417d5400057196b85705bacd1000000211396d5b3d5ab800000607f9b8001e1d867b3a80000000006bbd61200057bf9c0001c122300000205919412d9df4ded2d478b1d2c5d11c2a9800281a934119bae90700000b9f15c000695ba8d34f903655b9422bf97a87c0000001d85d2bb743be325ce05000792bda400082283b75924b7bbaec99e76ce460183347408a020400a0200000101832f044402416044810400a09180c1020c083082c00080080531a060079d0024115063e1058a44081100028006880820878895000820a264c50202445860a8ca0022040800220002000830a080099e1a5c08102000ae661410002002800410009 | _ => 0)
  | 8 => lookupWord 68 255 6 12 8 0 (fun | 0 => 0x5bc7bd625d9c00058eb37a871a5000000000b95f1a1668b6717bb736e000000516c89a1c81fa36988885620c790000b89ad000000000703f054c4d4850b32d000a5297b97e78c3826588249a70005a23a10105962475556b2e3b43231e8b08197156136c6b73000168e40a8a0000000bf0bb0571910009af000e2a7ba0009462c1dc7322451114000d63953000000c3d85627400013992669ff11f4193ed43938b0f29841bd69c9754449ef84f4a0000006015c8000000c5b00045dc3340a0b4000e8b86c7a839a34d000000c6acb13ae0000001836800000007b325900000000011d0000b52b9da9000ea3bc3f4e00000094fb0647a502f65000f08a50528b7574b94985e22cb99377090000523000e7f58115c8ab100286d93f5a000c9b462170f0de0463ce3037db7cf54cac535f34e0cc09baac0e66dc4c4420000000009c0ea0a07e216c2d2b931f92164d3f86f77806097600000022e00096b618294d8f96181283aca49bec45827f2fb5fc67d9d1c5e7100002900028d6a6000e720480812421ca0001c410a3483c00800001c014004000b00110629300504028310384018b00574400110100000004024009b681 | _ => 0)
  | 9 => lookupWord 11 34 4 9 5 0 (fun | 0 => 0x2d141951472533006680117c16b86000218033249001ee4f4dcc2d588b6d5d141e200009859143021609100a | _ => 0)
  | _ => fun _ => none
def g16 : Forest := ⟨63,9,(fun | 0 => (0xfffffffffffffffe1c22830787207813c07fff,0xfffffffffffffffa0c04012283243100c115a3) | 1 => (0x204303f808c07ffcff8380,0x311700040185483830a) | 2 => (0xfffffffffffffff84383fc0070ff801f0003ff,0x18338401041001e0a021c) | 3 => (0x783fc00007f00001ffffc00,0x4810820013c08020b1c2810) | 4 => (0x7fc0000007fffffe0000000,0x7f80000026ebe6780103020) | 5 => (0x7ffffffff80000000000000,0x17270c28440904400204040) | _ => (0,0)),[(2,0,8,130,7),(4,0,8,4,7),(16,0,9,16,7),(32,0,6,32,7),(0,16,10,0,6),(1,0,7,129,6),(8,0,7,8,6),(2,16,4,3970,5),(4,16,4,4,5),(5,0,2,773,5),(10,0,2,10,5),(17,0,2,3345,5),(18,0,3,2578,5),(20,0,3,20,5),(24,0,2,3480,5),(6,16,0,262,4),(21,0,0,917,4),(22,0,0,278,4),(26,0,0,26,4),(3,0,1,4099,4),(12,0,1,1164,4),(33,0,1,3617,4),(34,0,1,3746,4),(36,0,1,1316,4),(40,0,1,3880,4),(48,0,1,48,4)],[],layers16,index16⟩
def claim16 : Claim := (0xfffefffefefceea0fffefffefefceea0fffefffefefceea0fffefffefefceea0fffefffefefceea0fffefffefefceea0fffefffefefceea0fffefffefefceea0,g16,34898723844)

def layers17 : Nat → Packing
  | 8 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0xbf | _ => 0)⟩
  | _ => emptyPacking
def index17 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g17 : Forest := ⟨119,8,(fun | 0 => (0xfffffffffffffffffffffffffffffffff90a2f,0xfffffffffffffffffffffffffffffffff80a0d) | 1 => (0xfffffffffffffffffffffffffffffffff830cf,0xfffffffffffffffffffffffffffffffff81047) | 2 => (0xfffffffffffffffffffffffffffffffff8c513,0x4112) | 4 => (0x5061c,0x50608) | 5 => (0x607e0,0x404a0) | 6 => (0x7f800,0x3a000) | _ => (0,0)),[(2,0,11,2,8)],[],layers17,index17⟩
def claim17 : Claim := (0xfffffffffefefefefefefefefcfca0a0fffffffffefefefefefefefefcfca0a0fffffffffefefefefefefefefcfca0a0fffffffffefefefefefefefefcfca0a0,g17,4432943138820)

def layers18 : Nat → Packing
  | 3 => ⟨6,6,5,0,0,6,0,(fun | 0 => 0x4c10260816040000d2348c180d4044197509540c552f0044167509540c552e4044187509540c552a304a8318237155942a24528318237155942a14568318237155942 | _ => 0)⟩
  | 4 => ⟨14,5,5,0,0,8,0,(fun | 0 => 0x1604c202c1000b04003810000000201e9d1692910d0b8786048301803a4220b92a8a0aa5d21105095748554e9088284aba82a97c0441425503154aa1b2ea12a818aa550d97509548c552e06b3a84aa062a970359d425523154b21b0ea12a818aa590d87509548c55286ccbf00ab462a153424573dc15650a9a1229c6e0ab2858d0318237155942 | _ => 0)⟩
  | 5 => ⟨30,4,5,0,0,9,0,(fun | 0 => 0xd050400441c104416103816101c1038206040c0814102820c048404040000000000000001a0a080060242001809081e09081e0c0b1f89b8d66833291c520af673b3d80ba5a2b950a24e259208a421b0cc4e240c03000f29105095454a3e4637055942f0d425cd5454bc35096355152f0d5258d5450b4b5c95450552d2d725514054b4b5095748554d2d4255d205534b5095750552d2d4255d4054bc3509540c552cd973dc15650b3658f7058954cd963dc16454b3658f7055942cd938dc15650b8b50952d8154e2d425536054b8b54954d8142e2d4254b615538b50954d8552e2d525536150bca50954841528fa08dc55650bc3509548c552adb8055a3150bc35495498d42f0d425526354bc35095298d54 | _ => 0)⟩
  | 6 => ⟨6,3,5,0,0,7,0,(fun | 0 => 0x726450d901c6640b15902a7c6c5641315902eda293c2c0396a12a8a96fb7055942bf6e0b12a97edc16454a7db82aca15fb7055942 | _ => 0)⟩
  | 7 => ⟨10,2,5,0,0,9,0,(fun | 0 => 0xe9c0b913e38c39e381b227c71473c743e44d8e28e78e9cc98c58c7701e399068a7b01d399068a7b01d399064b9319e11364c67444f9319c131b568fbd98c96331104400fb54942ef55142df55152bf55942ff58954ff59152ff55942bfd8954bfd9152bf95942 | _ => 0)⟩
  | 8 => ⟨3,1,5,0,0,7,0,(fun | 0 => 0x1e9471a48c67661c592319c9c61648c6a8a807f553faa5fd42 | _ => 0)⟩
  | 9 => ⟨1,0,5,0,0,1,0,(fun | 0 => 0xe629062bf | _ => 0)⟩
  | _ => emptyPacking
def index18 : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 3 8 3 7 3 0 (fun | 0 => 0xb405886038a2d804 | _ => 0)
  | 5 => lookupWord 4 18 4 8 4 0 (fun | 0 => 0x62429910c2a3dd5004360bb080000a7320e07 | _ => 0)
  | 6 => lookupWord 10 36 5 9 5 0 (fun | 0 => 0x2fb599d8e0002e000c9082a56350015c0073426287b955560030ce98ac0717bed210eb0038e11a1c98a11038109842 | _ => 0)
  | 7 => lookupWord 3 9 1 7 3 0 (fun | 0 => 0x456601c00998b08 | _ => 0)
  | 8 => lookupWord 5 14 3 8 4 0 (fun | 0 => 0x3b44d93a80006200380c798073c0f0c0 | _ => 0)
  | 9 => lookupWord 2 5 1 6 2 0 (fun | 0 => 0x38003044 | _ => 0)
  | _ => fun _ => none
def g18 : Forest := ⟨123,9,(fun | 0 => (0xfffffffffffffffffffff0701f0863c18de043,0xfffffffffffffffffffff010090a2101a4e251) | 1 => (0x200f8401f27ffc,0x1001b00053020d8) | 3 => (0xfffffffffffffffffffff380c7f018fe03807f,0x8242200848030422) | 4 => (0xc00f8001f0003ff80,0xc00f8001f0003df00) | 5 => (0xfff00001ffffc0000,0x52400401690480800) | 6 => (0xfffffffe000000000,0xa48b4844020001000) | _ => (0,0)),[(0,16,15,0,8),(1,0,11,769,8),(16,0,14,16,8),(2,16,5,258,7),(17,0,5,913,7),(8,0,8,1032,7),(32,0,8,672,7),(64,0,8,64,7),(1,16,4,1409,5),(8,16,4,1032,5),(9,0,2,1545,5),(24,0,3,1048,5),(32,16,4,672,5),(33,0,2,1697,5),(48,0,3,688,5),(64,16,4,64,5),(65,0,2,833,5),(80,0,3,80,5),(3,16,0,1795,4),(10,16,0,522,4),(25,0,0,1945,4),(26,0,0,538,4),(34,16,0,2082,4),(49,0,0,2225,4),(50,0,0,2098,4),(66,16,0,322,4),(81,0,0,977,4),(82,0,0,338,4),(40,0,1,2344,4),(72,0,1,1224,4),(96,0,1,1376,4)],[],layers18,index18⟩
def claim18 : Claim := (0xffffffffffeeffeeffeeffeeeeccee00ffffffffffeeffeeffeeffeeeeccee00ffffffffffeeffeeffeeffeeeeccee00ffffffffffeeffeeffeeffeeeeccee00,g18,4432945218568)

def layers19 : Nat → Packing
  | 8 => ⟨1,1,5,0,0,1,0,(fun | 0 => 0x2079a411fd54 | _ => 0)⟩
  | 9 => ⟨1,0,5,0,0,1,0,(fun | 0 => 0x8398823f | _ => 0)⟩
  | _ => emptyPacking
def index19 : Nat → Nat → Option (Nat × Nat)
  | 9 => fun _ => some (0,0)
  | _ => fun _ => none
def g19 : Forest := ⟨111,9,(fun | 0 => (0xfffffffffffffffffffffffffff004602330ff,0xfffffffffffffffffffffffffff004a0251251) | 1 => (0x47823cdf30,0x4d826c4734) | 2 => (0xfffffffffffffffffffffffffff27813c0e03f,0x25912c8c42e) | 3 => (0x3801c00ffc0,0x2901480a888) | 5 => (0xc001fff0000,0x40009120000) | 6 => (0xfffe0000000,0x92240000000) | _ => (0,0)),[(1,0,13,2433,8),(2,0,14,2562,8),(4,0,14,4,8),(8,0,13,8,8),(5,0,5,901,7),(6,0,5,262,7),(10,0,5,10,7),(32,0,9,672,7),(64,0,9,64,7),(3,0,3,2691,5),(9,0,3,2825,5),(12,0,3,1036,5),(33,0,2,2977,5),(34,0,3,3106,5),(36,0,3,676,5),(40,0,2,3240,5),(65,0,2,3393,5),(66,0,3,2626,5),(68,0,3,68,5),(72,0,2,3528,5),(7,0,0,1799,4),(13,0,0,1933,4),(14,0,0,526,4),(37,0,0,2213,4),(38,0,0,2086,4),(42,0,0,682,4),(69,0,0,965,4),(70,0,0,326,4),(74,0,0,74,4),(96,0,1,96,4)],[],layers19,index19⟩
def claim19 : Claim := (0xfffffffffffefffefffefffeeea0eea0fffffffffffefffefffefffeeea0eea0fffffffffffefffefffefffeeea0eea0fffffffffffefffefffefffeeea0eea0,g19,4432408364036)

def layers20 : Nat → Packing
  | 8 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0xbf | _ => 0)⟩
  | _ => emptyPacking
def index20 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g20 : Forest := ⟨111,8,(fun | 0 => (0xfffffffffffffffffffffffffffffffff030cf,0xfffffffffffffffffffffffffffffffff01047) | 1 => (0xfffffffffffffffffffffffffffffffff04111,0x0) | 2 => (0x8222,0x0) | 3 => (0x30c3c,0x10438) | 5 => (0xc0fc0,0x40b80) | 6 => (0xff000,0xae000) | _ => (0,0)),[(2,0,15,3970,8)],[],layers20,index20⟩
def claim20 : Claim := (0xfffffffffffefffefffefffefefcfefcfffffffffffefffefffefffefefcfefcfffffffffffefffefffefffefefcfefcfffffffffffefffefffefffefefcfefc,g20,4432408346632)

def layers21 : Nat → Packing
  | 10 => ⟨1,1,6,0,0,1,0,(fun | 0 => 0x11218b1e23fd30 | _ => 0)⟩
  | 11 => ⟨1,0,6,0,0,1,0,(fun | 0 => 0x402cf1033877f | _ => 0)⟩
  | _ => emptyPacking
def index21 : Nat → Nat → Option (Nat × Nat)
  | 11 => fun _ => some (0,0)
  | _ => fun _ => none
def g21 : Forest := ⟨127,11,(fun | 0 => (0xfffffffffffe3081b0043f3b0021f3060187ff,0x2018092050a191028410640a026) | 1 => (0x87c000043e0007fef8e0,0x858000042c000216b0a4) | 2 => (0xfffffffffffc000040f8000407c00cf80f00ff,0x40b00004058004080d00d8) | 3 => (0x3c00e7f0000c7f8000f000fff00,0x42066020044621002e20094010) | 4 => (0x3ff0f800000f800000ffff00000,0x3ff0d800008f000004bf5e00000) | 5 => (0x3fff0000000fffffff000000000,0x9420040010a042108040800200) | 6 => (0x3ffffffffff0000000000000000,0x128490842200080010081000400) | _ => (0,0)),[(2,0,18,130,10),(4,0,18,4,10),(16,0,19,16,10),(32,0,16,672,10),(64,0,16,64,10),(0,16,20,0,9),(1,0,17,129,9),(8,0,17,8,9),(2,16,15,3970,8),(4,16,15,4,8),(5,0,11,773,8),(10,0,11,10,8),(17,0,13,2449,8),(24,0,13,24,8),(6,16,5,262,7),(21,0,5,917,7),(26,0,5,26,7),(3,0,8,4227,7),(12,0,8,1036,7),(34,0,8,4386,7),(36,0,8,676,7),(48,0,9,688,7),(66,0,8,194,7),(68,0,8,68,7),(80,0,9,80,7),(96,0,6,96,7),(1,16,10,1409,6),(8,16,10,1032,6),(9,0,12,9,6),(32,16,10,672,6),(33,0,7,4385,6),(40,0,7,680,6),(64,16,10,64,6),(65,0,7,193,6),(72,0,7,72,6),(3,16,4,4227,5),(5,16,4,1413,5),(10,16,4,4618,5),(11,0,2,4491,5),(13,0,2,1549,5),(25,0,3,2841,5),(37,0,2,1701,5),(42,0,2,682,5),(49,0,2,2993,5),(56,0,2,3256,5),(69,0,2,837,5),(74,0,2,74,5),(81,0,2,3409,5),(88,0,2,3544,5),(7,16,0,1799,4),(27,0,0,411,4),(29,0,0,1949,4),(38,16,0,2086,4),(53,0,0,2229,4),(58,0,0,698,4),(70,16,0,326,4),(85,0,0,981,4),(90,0,0,90,4)],[],layers21,index21⟩
def claim21 : Claim := (0xfffffffffffefffefffefffefefceea0fffffffffffefffefffefffefefceea0fffffffffffefffefffefffefefceea0fffffffffffefffefffefffefefceea0,g21,4432945234948)

def catalogue : Nat → Claim
  | 0 => claim0
  | 1 => claim1
  | 2 => claim2
  | 3 => claim3
  | 4 => claim4
  | 5 => claim5
  | 6 => claim6
  | 7 => claim7
  | 8 => claim8
  | 9 => claim9
  | 10 => claim10
  | 11 => claim11
  | 12 => claim12
  | 13 => claim13
  | 14 => claim14
  | 15 => claim15
  | 16 => claim16
  | 17 => claim17
  | 18 => claim18
  | 19 => claim19
  | 20 => claim20
  | 21 => claim21
  | _ => claim0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK0 : localCheck claim0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK0 : columnsCheck catalogue 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK0 : Matches g0 claim0.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK1 : localCheck claim1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK1 : columnsCheck catalogue 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK1 : Matches g1 claim1.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK2 : localCheck claim2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK2 : columnsCheck catalogue 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK2 : Matches g2 claim2.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK3 : localCheck claim3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK3 : columnsCheck catalogue 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK3 : Matches g3 claim3.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK4 : localCheck claim4 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK4 : columnsCheck catalogue 4 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK4 : Matches g4 claim4.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK5 : localCheck claim5 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK5 : columnsCheck catalogue 5 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK5 : Matches g5 claim5.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK6 : localCheck claim6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK6 : columnsCheck catalogue 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK6 : Matches g6 claim6.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK7 : localCheck claim7 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK7 : columnsCheck catalogue 7 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK7 : Matches g7 claim7.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK8 : localCheck claim8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK8 : columnsCheck catalogue 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK8 : Matches g8 claim8.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK9 : localCheck claim9 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK9 : columnsCheck catalogue 9 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK9 : Matches g9 claim9.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK10 : localCheck claim10 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK10 : columnsCheck catalogue 10 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK10 : Matches g10 claim10.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK11 : localCheck claim11 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK11 : columnsCheck catalogue 11 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK11 : Matches g11 claim11.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK12 : localCheck claim12 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK12 : columnsCheck catalogue 12 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK12 : Matches g12 claim12.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK13 : localCheck claim13 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK13 : columnsCheck catalogue 13 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK13 : Matches g13 claim13.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK14 : localCheck claim14 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK14 : columnsCheck catalogue 14 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK14 : Matches g14 claim14.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK15 : localCheck claim15 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK15 : columnsCheck catalogue 15 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK15 : Matches g15 claim15.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK16 : localCheck claim16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK16 : columnsCheck catalogue 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK16 : Matches g16 claim16.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK17 : localCheck claim17 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK17 : columnsCheck catalogue 17 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK17 : Matches g17 claim17.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK18 : localCheck claim18 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK18 : columnsCheck catalogue 18 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK18 : Matches g18 claim18.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK19 : localCheck claim19 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK19 : columnsCheck catalogue 19 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK19 : Matches g19 claim19.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK20 : localCheck claim20 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK20 : columnsCheck catalogue 20 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK20 : Matches g20 claim20.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK21 : localCheck claim21 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK21 : columnsCheck catalogue 21 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK21 : Matches g21 claim21.1 := by unfold Matches properPairs; decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c0_3_0 : checks g0 claim0.1 3 0 1 = true := by decide +kernel
theorem rows0 : ∀ k ≤ g0.cap, checks g0 claim0.1 k 0 (g0.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => c0_3_0
  | _+4,h => by change _ ≤ 3 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c1_3_0 : checks g1 claim1.1 3 0 1 = true := by decide +kernel
theorem rows1 : ∀ k ≤ g1.cap, checks g1 claim1.1 k 0 (g1.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => c1_3_0
  | _+4,h => by change _ ≤ 3 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c2_4_0 : checks g2 claim2.1 4 0 1 = true := by decide +kernel
theorem rows2 : ∀ k ≤ g2.cap, checks g2 claim2.1 k 0 (g2.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c2_4_0
  | _+5,h => by change _ ≤ 4 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c3_4_0 : checks g3 claim3.1 4 0 1 = true := by decide +kernel
theorem rows3 : ∀ k ≤ g3.cap, checks g3 claim3.1 k 0 (g3.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c3_4_0
  | _+5,h => by change _ ≤ 4 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c4_4_0 : checks g4 claim4.1 4 0 1 = true := by decide +kernel
theorem rows4 : ∀ k ≤ g4.cap, checks g4 claim4.1 k 0 (g4.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c4_4_0
  | _+5,h => by change _ ≤ 4 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c5_3_0 : checks g5 claim5.1 3 0 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c5_4_0 : checks g5 claim5.1 4 0 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c5_4_8 : checks g5 claim5.1 4 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c5_4_16 : checks g5 claim5.1 4 16 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c5_4_24 : checks g5 claim5.1 4 24 4 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c5_5_0 : checks g5 claim5.1 5 0 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c5_6_0 : checks g5 claim5.1 6 0 1 = true := by decide +kernel
theorem rows5 : ∀ k ≤ g5.cap, checks g5 claim5.1 k 0 (g5.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => c5_3_0
  | 4,_ => (@checks_merge g5 claim5.1 4 0 16 12 (@checks_merge g5 claim5.1 4 0 8 8 c5_4_0 c5_4_8) (@checks_merge g5 claim5.1 4 16 8 4 c5_4_16 c5_4_24))
  | 5,_ => c5_5_0
  | 6,_ => c5_6_0
  | _+7,h => by change _ ≤ 6 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c6_4_0 : checks g6 claim6.1 4 0 5 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c6_5_0 : checks g6 claim6.1 5 0 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c6_5_8 : checks g6 claim6.1 5 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c6_6_0 : checks g6 claim6.1 6 0 1 = true := by decide +kernel
theorem rows6 : ∀ k ≤ g6.cap, checks g6 claim6.1 k 0 (g6.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c6_4_0
  | 5,_ => (@checks_merge g6 claim6.1 5 0 8 2 c6_5_0 c6_5_8)
  | 6,_ => c6_6_0
  | _+7,h => by change _ ≤ 6 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c7_5_0 : checks g7 claim7.1 5 0 1 = true := by decide +kernel
theorem rows7 : ∀ k ≤ g7.cap, checks g7 claim7.1 k 0 (g7.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => c7_5_0
  | _+6,h => by change _ ≤ 5 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c8_4_0 : checks g8 claim8.1 4 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c8_5_0 : checks g8 claim8.1 5 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c8_6_0 : checks g8 claim8.1 6 0 1 = true := by decide +kernel
theorem rows8 : ∀ k ≤ g8.cap, checks g8 claim8.1 k 0 (g8.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c8_4_0
  | 5,_ => c8_5_0
  | 6,_ => c8_6_0
  | _+7,h => by change _ ≤ 6 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c9_6_0 : checks g9 claim9.1 6 0 1 = true := by decide +kernel
theorem rows9 : ∀ k ≤ g9.cap, checks g9 claim9.1 k 0 (g9.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => rfl
  | 6,_ => c9_6_0
  | _+7,h => by change _ ≤ 6 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c10_5_0 : checks g10 claim10.1 5 0 1 = true := by decide +kernel
theorem rows10 : ∀ k ≤ g10.cap, checks g10 claim10.1 k 0 (g10.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => c10_5_0
  | _+6,h => by change _ ≤ 5 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c11_7_0 : checks g11 claim11.1 7 0 1 = true := by decide +kernel
theorem rows11 : ∀ k ≤ g11.cap, checks g11 claim11.1 k 0 (g11.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => rfl
  | 6,_ => rfl
  | 7,_ => c11_7_0
  | _+8,h => by change _ ≤ 7 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c12_5_0 : checks g12 claim12.1 5 0 1 = true := by decide +kernel
theorem rows12 : ∀ k ≤ g12.cap, checks g12 claim12.1 k 0 (g12.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => c12_5_0
  | _+6,h => by change _ ≤ 5 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c13_7_0 : checks g13 claim13.1 7 0 1 = true := by decide +kernel
theorem rows13 : ∀ k ≤ g13.cap, checks g13 claim13.1 k 0 (g13.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => rfl
  | 6,_ => rfl
  | 7,_ => c13_7_0
  | _+8,h => by change _ ≤ 7 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c14_7_0 : checks g14 claim14.1 7 0 1 = true := by decide +kernel
theorem rows14 : ∀ k ≤ g14.cap, checks g14 claim14.1 k 0 (g14.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => rfl
  | 6,_ => rfl
  | 7,_ => c14_7_0
  | _+8,h => by change _ ≤ 7 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c15_7_0 : checks g15 claim15.1 7 0 1 = true := by decide +kernel
theorem rows15 : ∀ k ≤ g15.cap, checks g15 claim15.1 k 0 (g15.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => rfl
  | 6,_ => rfl
  | 7,_ => c15_7_0
  | _+8,h => by change _ ≤ 7 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_5_0 : checks g16 claim16.1 5 0 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_5_8 : checks g16 claim16.1 5 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_5_16 : checks g16 claim16.1 5 16 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_5_24 : checks g16 claim16.1 5 24 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_5_32 : checks g16 claim16.1 5 32 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_5_40 : checks g16 claim16.1 5 40 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_5_48 : checks g16 claim16.1 5 48 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_5_56 : checks g16 claim16.1 5 56 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_5_64 : checks g16 claim16.1 5 64 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_0 : checks g16 claim16.1 6 0 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_8 : checks g16 claim16.1 6 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_16 : checks g16 claim16.1 6 16 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_24 : checks g16 claim16.1 6 24 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_32 : checks g16 claim16.1 6 32 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_40 : checks g16 claim16.1 6 40 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_48 : checks g16 claim16.1 6 48 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_56 : checks g16 claim16.1 6 56 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_64 : checks g16 claim16.1 6 64 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_72 : checks g16 claim16.1 6 72 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_80 : checks g16 claim16.1 6 80 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_88 : checks g16 claim16.1 6 88 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_96 : checks g16 claim16.1 6 96 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_104 : checks g16 claim16.1 6 104 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_112 : checks g16 claim16.1 6 112 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_120 : checks g16 claim16.1 6 120 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_128 : checks g16 claim16.1 6 128 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_136 : checks g16 claim16.1 6 136 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_144 : checks g16 claim16.1 6 144 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_152 : checks g16 claim16.1 6 152 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_160 : checks g16 claim16.1 6 160 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_168 : checks g16 claim16.1 6 168 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_176 : checks g16 claim16.1 6 176 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_184 : checks g16 claim16.1 6 184 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_192 : checks g16 claim16.1 6 192 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_200 : checks g16 claim16.1 6 200 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_208 : checks g16 claim16.1 6 208 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_216 : checks g16 claim16.1 6 216 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_224 : checks g16 claim16.1 6 224 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_232 : checks g16 claim16.1 6 232 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_240 : checks g16 claim16.1 6 240 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_248 : checks g16 claim16.1 6 248 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_256 : checks g16 claim16.1 6 256 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_264 : checks g16 claim16.1 6 264 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_272 : checks g16 claim16.1 6 272 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_280 : checks g16 claim16.1 6 280 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_288 : checks g16 claim16.1 6 288 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_296 : checks g16 claim16.1 6 296 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_304 : checks g16 claim16.1 6 304 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_312 : checks g16 claim16.1 6 312 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_320 : checks g16 claim16.1 6 320 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_328 : checks g16 claim16.1 6 328 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_336 : checks g16 claim16.1 6 336 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_344 : checks g16 claim16.1 6 344 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_352 : checks g16 claim16.1 6 352 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_360 : checks g16 claim16.1 6 360 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_368 : checks g16 claim16.1 6 368 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_6_376 : checks g16 claim16.1 6 376 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_0 : checks g16 claim16.1 7 0 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_8 : checks g16 claim16.1 7 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_16 : checks g16 claim16.1 7 16 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_24 : checks g16 claim16.1 7 24 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_32 : checks g16 claim16.1 7 32 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_40 : checks g16 claim16.1 7 40 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_48 : checks g16 claim16.1 7 48 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_56 : checks g16 claim16.1 7 56 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_64 : checks g16 claim16.1 7 64 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_72 : checks g16 claim16.1 7 72 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_80 : checks g16 claim16.1 7 80 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_88 : checks g16 claim16.1 7 88 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_96 : checks g16 claim16.1 7 96 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_104 : checks g16 claim16.1 7 104 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_112 : checks g16 claim16.1 7 112 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_120 : checks g16 claim16.1 7 120 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_128 : checks g16 claim16.1 7 128 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_136 : checks g16 claim16.1 7 136 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_144 : checks g16 claim16.1 7 144 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_152 : checks g16 claim16.1 7 152 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_160 : checks g16 claim16.1 7 160 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_168 : checks g16 claim16.1 7 168 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_176 : checks g16 claim16.1 7 176 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_184 : checks g16 claim16.1 7 184 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_192 : checks g16 claim16.1 7 192 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_7_200 : checks g16 claim16.1 7 200 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_8_0 : checks g16 claim16.1 8 0 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_8_8 : checks g16 claim16.1 8 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_8_16 : checks g16 claim16.1 8 16 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_8_24 : checks g16 claim16.1 8 24 4 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_9_0 : checks g16 claim16.1 9 0 1 = true := by decide +kernel
theorem rows16 : ∀ k ≤ g16.cap, checks g16 claim16.1 k 0 (g16.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => (@checks_merge g16 claim16.1 5 0 32 38 (@checks_merge g16 claim16.1 5 0 16 16 (@checks_merge g16 claim16.1 5 0 8 8 c16_5_0 c16_5_8) (@checks_merge g16 claim16.1 5 16 8 8 c16_5_16 c16_5_24)) (@checks_merge g16 claim16.1 5 32 16 22 (@checks_merge g16 claim16.1 5 32 8 8 c16_5_32 c16_5_40) (@checks_merge g16 claim16.1 5 48 8 14 c16_5_48 (@checks_merge g16 claim16.1 5 56 8 6 c16_5_56 c16_5_64))))
  | 6,_ => (@checks_merge g16 claim16.1 6 0 192 185 (@checks_merge g16 claim16.1 6 0 96 96 (@checks_merge g16 claim16.1 6 0 48 48 (@checks_merge g16 claim16.1 6 0 24 24 (@checks_merge g16 claim16.1 6 0 8 16 c16_6_0 (@checks_merge g16 claim16.1 6 8 8 8 c16_6_8 c16_6_16)) (@checks_merge g16 claim16.1 6 24 8 16 c16_6_24 (@checks_merge g16 claim16.1 6 32 8 8 c16_6_32 c16_6_40))) (@checks_merge g16 claim16.1 6 48 24 24 (@checks_merge g16 claim16.1 6 48 8 16 c16_6_48 (@checks_merge g16 claim16.1 6 56 8 8 c16_6_56 c16_6_64)) (@checks_merge g16 claim16.1 6 72 8 16 c16_6_72 (@checks_merge g16 claim16.1 6 80 8 8 c16_6_80 c16_6_88)))) (@checks_merge g16 claim16.1 6 96 48 48 (@checks_merge g16 claim16.1 6 96 24 24 (@checks_merge g16 claim16.1 6 96 8 16 c16_6_96 (@checks_merge g16 claim16.1 6 104 8 8 c16_6_104 c16_6_112)) (@checks_merge g16 claim16.1 6 120 8 16 c16_6_120 (@checks_merge g16 claim16.1 6 128 8 8 c16_6_128 c16_6_136))) (@checks_merge g16 claim16.1 6 144 24 24 (@checks_merge g16 claim16.1 6 144 8 16 c16_6_144 (@checks_merge g16 claim16.1 6 152 8 8 c16_6_152 c16_6_160)) (@checks_merge g16 claim16.1 6 168 8 16 c16_6_168 (@checks_merge g16 claim16.1 6 176 8 8 c16_6_176 c16_6_184))))) (@checks_merge g16 claim16.1 6 192 96 89 (@checks_merge g16 claim16.1 6 192 48 48 (@checks_merge g16 claim16.1 6 192 24 24 (@checks_merge g16 claim16.1 6 192 8 16 c16_6_192 (@checks_merge g16 claim16.1 6 200 8 8 c16_6_200 c16_6_208)) (@checks_merge g16 claim16.1 6 216 8 16 c16_6_216 (@checks_merge g16 claim16.1 6 224 8 8 c16_6_224 c16_6_232))) (@checks_merge g16 claim16.1 6 240 24 24 (@checks_merge g16 claim16.1 6 240 8 16 c16_6_240 (@checks_merge g16 claim16.1 6 248 8 8 c16_6_248 c16_6_256)) (@checks_merge g16 claim16.1 6 264 8 16 c16_6_264 (@checks_merge g16 claim16.1 6 272 8 8 c16_6_272 c16_6_280)))) (@checks_merge g16 claim16.1 6 288 48 41 (@checks_merge g16 claim16.1 6 288 24 24 (@checks_merge g16 claim16.1 6 288 8 16 c16_6_288 (@checks_merge g16 claim16.1 6 296 8 8 c16_6_296 c16_6_304)) (@checks_merge g16 claim16.1 6 312 8 16 c16_6_312 (@checks_merge g16 claim16.1 6 320 8 8 c16_6_320 c16_6_328))) (@checks_merge g16 claim16.1 6 336 24 17 (@checks_merge g16 claim16.1 6 336 8 16 c16_6_336 (@checks_merge g16 claim16.1 6 344 8 8 c16_6_344 c16_6_352)) (@checks_merge g16 claim16.1 6 360 8 9 c16_6_360 (@checks_merge g16 claim16.1 6 368 8 1 c16_6_368 c16_6_376))))))
  | 7,_ => (@checks_merge g16 claim16.1 7 0 104 97 (@checks_merge g16 claim16.1 7 0 48 56 (@checks_merge g16 claim16.1 7 0 24 24 (@checks_merge g16 claim16.1 7 0 8 16 c16_7_0 (@checks_merge g16 claim16.1 7 8 8 8 c16_7_8 c16_7_16)) (@checks_merge g16 claim16.1 7 24 8 16 c16_7_24 (@checks_merge g16 claim16.1 7 32 8 8 c16_7_32 c16_7_40))) (@checks_merge g16 claim16.1 7 48 24 32 (@checks_merge g16 claim16.1 7 48 8 16 c16_7_48 (@checks_merge g16 claim16.1 7 56 8 8 c16_7_56 c16_7_64)) (@checks_merge g16 claim16.1 7 72 16 16 (@checks_merge g16 claim16.1 7 72 8 8 c16_7_72 c16_7_80) (@checks_merge g16 claim16.1 7 88 8 8 c16_7_88 c16_7_96)))) (@checks_merge g16 claim16.1 7 104 48 49 (@checks_merge g16 claim16.1 7 104 24 24 (@checks_merge g16 claim16.1 7 104 8 16 c16_7_104 (@checks_merge g16 claim16.1 7 112 8 8 c16_7_112 c16_7_120)) (@checks_merge g16 claim16.1 7 128 8 16 c16_7_128 (@checks_merge g16 claim16.1 7 136 8 8 c16_7_136 c16_7_144))) (@checks_merge g16 claim16.1 7 152 24 25 (@checks_merge g16 claim16.1 7 152 8 16 c16_7_152 (@checks_merge g16 claim16.1 7 160 8 8 c16_7_160 c16_7_168)) (@checks_merge g16 claim16.1 7 176 16 9 (@checks_merge g16 claim16.1 7 176 8 8 c16_7_176 c16_7_184) (@checks_merge g16 claim16.1 7 192 8 1 c16_7_192 c16_7_200)))))
  | 8,_ => (@checks_merge g16 claim16.1 8 0 16 12 (@checks_merge g16 claim16.1 8 0 8 8 c16_8_0 c16_8_8) (@checks_merge g16 claim16.1 8 16 8 4 c16_8_16 c16_8_24))
  | 9,_ => c16_9_0
  | _+10,h => by change _ ≤ 9 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c17_8_0 : checks g17 claim17.1 8 0 1 = true := by decide +kernel
theorem rows17 : ∀ k ≤ g17.cap, checks g17 claim17.1 k 0 (g17.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => rfl
  | 6,_ => rfl
  | 7,_ => rfl
  | 8,_ => c17_8_0
  | _+9,h => by change _ ≤ 8 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c18_3_0 : checks g18 claim18.1 3 0 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c18_4_0 : checks g18 claim18.1 4 0 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c18_4_8 : checks g18 claim18.1 4 8 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c18_5_0 : checks g18 claim18.1 5 0 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c18_5_8 : checks g18 claim18.1 5 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c18_5_16 : checks g18 claim18.1 5 16 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c18_5_24 : checks g18 claim18.1 5 24 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c18_6_0 : checks g18 claim18.1 6 0 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c18_7_0 : checks g18 claim18.1 7 0 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c18_7_8 : checks g18 claim18.1 7 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c18_8_0 : checks g18 claim18.1 8 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c18_9_0 : checks g18 claim18.1 9 0 1 = true := by decide +kernel
theorem rows18 : ∀ k ≤ g18.cap, checks g18 claim18.1 k 0 (g18.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => c18_3_0
  | 4,_ => (@checks_merge g18 claim18.1 4 0 8 6 c18_4_0 c18_4_8)
  | 5,_ => (@checks_merge g18 claim18.1 5 0 16 14 (@checks_merge g18 claim18.1 5 0 8 8 c18_5_0 c18_5_8) (@checks_merge g18 claim18.1 5 16 8 6 c18_5_16 c18_5_24))
  | 6,_ => c18_6_0
  | 7,_ => (@checks_merge g18 claim18.1 7 0 8 2 c18_7_0 c18_7_8)
  | 8,_ => c18_8_0
  | 9,_ => c18_9_0
  | _+10,h => by change _ ≤ 9 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c19_8_0 : checks g19 claim19.1 8 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c19_9_0 : checks g19 claim19.1 9 0 1 = true := by decide +kernel
theorem rows19 : ∀ k ≤ g19.cap, checks g19 claim19.1 k 0 (g19.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => rfl
  | 6,_ => rfl
  | 7,_ => rfl
  | 8,_ => c19_8_0
  | 9,_ => c19_9_0
  | _+10,h => by change _ ≤ 9 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c20_8_0 : checks g20 claim20.1 8 0 1 = true := by decide +kernel
theorem rows20 : ∀ k ≤ g20.cap, checks g20 claim20.1 k 0 (g20.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => rfl
  | 6,_ => rfl
  | 7,_ => rfl
  | 8,_ => c20_8_0
  | _+9,h => by change _ ≤ 8 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c21_10_0 : checks g21 claim21.1 10 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c21_11_0 : checks g21 claim21.1 11 0 1 = true := by decide +kernel
theorem rows21 : ∀ k ≤ g21.cap, checks g21 claim21.1 k 0 (g21.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => rfl
  | 6,_ => rfl
  | 7,_ => rfl
  | 8,_ => rfl
  | 9,_ => rfl
  | 10,_ => c21_10_0
  | 11,_ => c21_11_0
  | _+12,h => by change _ ≤ 11 at h; omega

theorem ready0 : ∀ j < 0, Resolved (catalogue j) := fun j h => (Nat.not_lt_zero j h).elim
theorem resolved0 : Resolved (catalogue 0) := resolve (i:=0) ready0 localOK0 pairsOK0 colsOK0 rows0
theorem ready1 : ∀ j < 1, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=0) ready0 resolved0
theorem resolved1 : Resolved (catalogue 1) := resolve (i:=1) ready1 localOK1 pairsOK1 colsOK1 rows1
theorem ready2 : ∀ j < 2, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=1) ready1 resolved1
theorem resolved2 : Resolved (catalogue 2) := resolve (i:=2) ready2 localOK2 pairsOK2 colsOK2 rows2
theorem ready3 : ∀ j < 3, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=2) ready2 resolved2
theorem resolved3 : Resolved (catalogue 3) := resolve (i:=3) ready3 localOK3 pairsOK3 colsOK3 rows3
theorem ready4 : ∀ j < 4, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=3) ready3 resolved3
theorem resolved4 : Resolved (catalogue 4) := resolve (i:=4) ready4 localOK4 pairsOK4 colsOK4 rows4
theorem ready5 : ∀ j < 5, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=4) ready4 resolved4
theorem resolved5 : Resolved (catalogue 5) := resolve (i:=5) ready5 localOK5 pairsOK5 colsOK5 rows5
theorem ready6 : ∀ j < 6, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=5) ready5 resolved5
theorem resolved6 : Resolved (catalogue 6) := resolve (i:=6) ready6 localOK6 pairsOK6 colsOK6 rows6
theorem ready7 : ∀ j < 7, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=6) ready6 resolved6
theorem resolved7 : Resolved (catalogue 7) := resolve (i:=7) ready7 localOK7 pairsOK7 colsOK7 rows7
theorem ready8 : ∀ j < 8, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=7) ready7 resolved7
theorem resolved8 : Resolved (catalogue 8) := resolve (i:=8) ready8 localOK8 pairsOK8 colsOK8 rows8
theorem ready9 : ∀ j < 9, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=8) ready8 resolved8
theorem resolved9 : Resolved (catalogue 9) := resolve (i:=9) ready9 localOK9 pairsOK9 colsOK9 rows9
theorem ready10 : ∀ j < 10, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=9) ready9 resolved9
theorem resolved10 : Resolved (catalogue 10) := resolve (i:=10) ready10 localOK10 pairsOK10 colsOK10 rows10
theorem ready11 : ∀ j < 11, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=10) ready10 resolved10
theorem resolved11 : Resolved (catalogue 11) := resolve (i:=11) ready11 localOK11 pairsOK11 colsOK11 rows11
theorem ready12 : ∀ j < 12, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=11) ready11 resolved11
theorem resolved12 : Resolved (catalogue 12) := resolve (i:=12) ready12 localOK12 pairsOK12 colsOK12 rows12
theorem ready13 : ∀ j < 13, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=12) ready12 resolved12
theorem resolved13 : Resolved (catalogue 13) := resolve (i:=13) ready13 localOK13 pairsOK13 colsOK13 rows13
theorem ready14 : ∀ j < 14, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=13) ready13 resolved13
theorem resolved14 : Resolved (catalogue 14) := resolve (i:=14) ready14 localOK14 pairsOK14 colsOK14 rows14
theorem ready15 : ∀ j < 15, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=14) ready14 resolved14
theorem resolved15 : Resolved (catalogue 15) := resolve (i:=15) ready15 localOK15 pairsOK15 colsOK15 rows15
theorem ready16 : ∀ j < 16, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=15) ready15 resolved15
theorem resolved16 : Resolved (catalogue 16) := resolve (i:=16) ready16 localOK16 pairsOK16 colsOK16 rows16
theorem ready17 : ∀ j < 17, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=16) ready16 resolved16
theorem resolved17 : Resolved (catalogue 17) := resolve (i:=17) ready17 localOK17 pairsOK17 colsOK17 rows17
theorem ready18 : ∀ j < 18, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=17) ready17 resolved17
theorem resolved18 : Resolved (catalogue 18) := resolve (i:=18) ready18 localOK18 pairsOK18 colsOK18 rows18
theorem ready19 : ∀ j < 19, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=18) ready18 resolved18
theorem resolved19 : Resolved (catalogue 19) := resolve (i:=19) ready19 localOK19 pairsOK19 colsOK19 rows19
theorem ready20 : ∀ j < 20, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=19) ready19 resolved19
theorem resolved20 : Resolved (catalogue 20) := resolve (i:=20) ready20 localOK20 pairsOK20 colsOK20 rows20
theorem ready21 : ∀ j < 21, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=20) ready20 resolved20
theorem resolved21 : Resolved (catalogue 21) := resolve (i:=21) ready21 localOK21 pairsOK21 colsOK21 rows21

end PEqualNP.Outside.L_meta_33557_aux.Cert


namespace PEqualNP.Outside.L_meta_33557_aux
open PEqualNP.Outside.L_meta_33557_aux.Base
open PEqualNP.CircuitLowerBounds

def eightInputs : List Sig := [inputs.getD 1 zero, inputs.getD 2 zero, inputs.getD 7 zero, inputs.getD 3 zero, inputs.getD 4 zero, inputs.getD 5 zero, inputs.getD 6 zero, inputs.getD 0 zero]

def sampleEight (r : Row) (i : Fin 8) : Bool := bit r (eightInputs.getD i.val zero)

set_option maxRecDepth 10000 in
theorem eightList : List.ofFn (fun i : Fin 8 => eightInputs.getD i.val zero) = eightInputs := rfl

theorem eightSampled (r : Row) : List.ofFn (sampleEight r) = eightInputs.map (bit r) := by
  rw [←eightList,List.map_ofFn]
  rfl

theorem eightEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates eightInputs).getD i zero) =
      (C.wires (List.ofFn (sampleEight r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),eightSampled]
  rfl

def newTarget (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def witness : Circuit := ⟨[⟨.or, [5, 6]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [1, 0]⟩, ⟨.and, [10, 14]⟩, ⟨.and, [13, 7]⟩, ⟨.and, [3, 11]⟩, ⟨.and, [6, 5]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [19, 17]⟩, ⟨.or, [20, 18]⟩], 21⟩
theorem witnessFit : ∀ g ∈ witness.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g h
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr rfl, by decide⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, witness.eval (List.ofFn x) = newTarget x := by decide +kernel

theorem replacementAtBudget (gs : List Gate) (bound : 14 ≤ gs.length) :
    ∃ (out : List Gate) (o : Nat), (∀ g ∈ out, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      out.length ≤ gs.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk out o).eval (List.ofFn x) = newTarget x :=
  ⟨witness.gates, witness.output, witnessFit, bound, witnessCorrect⟩

def newGraph : Sig := 0xfffffffffffefffefffefffefefeeeaafffffffffffefffefffefffefefceea0fffffffffffefffefffefffefefeeeaafffffffffffefffefffefffefefceea0
theorem currentProper : proper newGraph := by unfold proper; decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem currentTable : ∀ r : Row, bit r newGraph = newTarget (sampleEight r) := by decide +kernel
def lowCurrent (i : Fin 8) : Row := Fin.ofNat 512 (([8, 16, 1, 2, 2, 2, 2, 4] : List Nat).getD i.val 0)
def highCurrent (i : Fin 8) : Row := Fin.ofNat 512 (([10, 20, 129, 10, 18, 34, 66, 5] : List Nat).getD i.val 0)
set_option maxHeartbeats 1000000 in
theorem currentRequired :
    (∀ i : Fin 8, bit (lowCurrent i) newGraph ≠ bit (highCurrent i) newGraph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (lowCurrent i) (eightInputs.getD j.val zero) =
      bit (highCurrent i) (eightInputs.getD j.val zero)) := by decide +kernel
theorem physicalGraph (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=newTarget x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true newGraph k eightInputs.toFinset := by
  have goalEq : (execute C.gates eightInputs).getD C.output zero = newGraph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (eightEval C legal C.output r).trans ((computes (sampleEight r)).trans (currentTable r).symm)
  have out := get_rep (u:=true) (execute C.gates eightInputs) C.output
  rw [goalEq] at out
  unfold PEqualNP.Outside.L_meta_33557_aux.Base.Repr at out
  have pg : bit 0 newGraph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates eightInputs legal (by simp) currentProper
    (out.resolve_right (fun h => h currentProper))
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
      apply raw_required run eightInputs (eightInputs.getD i.val zero) sub (lowCurrent i) (highCurrent i)
        (currentRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply currentRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩


theorem conclude (low : Impossible true newGraph 12 eightInputs.toFinset) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o fit _ correct
  by_cases large : 14 ≤ gs.length
  · exact replacementAtBudget gs large
  by_cases mono : ∀ g ∈ gs, g.op ≠ GateOp.not
  · exact ⟨gs,o,noNotReuse fit mono,Nat.le_refl _,correct⟩
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have count : gs.countP (fun q => !isNot q) < gs.length := by
    by_contra! ge
    have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length ge) g hg
    simp [isNot,hop] at eq
  have legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gs o) := by
    intro q hq
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using fit q hq
  obtain ⟨k,bound,run⟩ := physicalGraph (Circuit.mk gs o) legal correct
  change k ≤ gs.countP (fun q => !isNot q) at bound
  exact (low k (by omega) run).elim


def pinMove : List Move := [(zero, inputs.getD 7 zero, 128)]
def restrictionMask : Sig := ~~~(inputs.getD 7 zero)
def oldGraph : Sig := 0xfffffffffffefffefffefffefefceea0fffffffffffefffefffefffefefceea0fffffffffffefffefffefffefefceea0fffffffffffefffefffefffefefceea0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem liftCertificate (prior : Lower true sevenInputs oldGraph 12) :
    Impossible true newGraph 12 eightInputs.toFinset := by
  have slice : Slice true eightInputs newGraph restrictionMask 12 := by
    exact slice_correct (ms := pinMove) (G := oldGraph) (base := sevenInputs)
      (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) prior
  obtain ⟨f, roots, domain, supplied, nc, lower⟩ := slice
  intro k bound run
  have reach : Reach true (roots.map observe) 0 (roots.map observe) := Reach.start
  have stocks : supply true (roots.map observe) ((eightInputs.map observe).map (restrictRows f)) := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hb
    exact supplied w hw
  have seq := list_run run eightInputs (by decide +kernel) rfl
  have total := projected_bound f seq nc reach stocks lower
  have paid := count_constants domain eightInputs
  have num : eightInputs.countP (isMaskedConstant restrictionMask) = 1 := by decide +kernel
  rw [num] at paid
  omega

end PEqualNP.Outside.L_meta_33557_aux

theorem PEqualNP.Outside.L_meta_33557 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  PEqualNP.Outside.L_meta_33557_aux.conclude (PEqualNP.Outside.L_meta_33557_aux.liftCertificate PEqualNP.Outside.L_meta_33557_aux.Cert.resolved21.2)

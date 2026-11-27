import Mathlib
import PEqualNP.Defs

-- Copied from PEqualNP/Outside/L_meta_3064.lean (itself adapted from L_meta_1667.lean, Apache-2.0).
namespace PEqualNP.Outside.L_meta_27695_aux
open PEqualNP.CircuitLowerBounds
private abbrev Sig := BitVec 128
private def zero : Sig := 0
private def one : Sig := BitVec.allOnes 128
private def neg (a : Sig) : Sig := ~~~a
private def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
private def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

private def Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | 0,t,S => t=0 ∧ S={target} ∧ proper target
  | k+1,t,S =>
    (∃ (u : Nat) (U : Finset Sig) (a : Sig), t=u+1 ∧ S=insert a U ∧ proper a ∧
      neg a ∉ insert a U ∧ Live target k u (insert (neg a) U)) ∨
    (∃ (U : Finset Sig) (a b : Sig) (d : Bool), S=insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live target k t (insert (bin d a b) U))
private theorem Live.stop {target : Sig} (hp : proper target) : Live target 0 0 {target} := ⟨rfl,rfl,hp⟩
private theorem Live.unary {target : Sig} {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
    (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
    Live target (k+1) (t+1) (insert a U) :=
  Or.inl ⟨t,U,a,rfl,rfl,ha,hfresh,tail⟩
private theorem Live.binary {target : Sig} {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
    Live target (k+1) t (insert a (insert b U)) :=
  Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hfresh,tail⟩
private theorem Live.ind {target : Sig} {motive : ∀ (k t : Nat) (S : Finset Sig), Live target k t S → Prop}
    (stop : ∀ (hp : proper target), motive 0 0 {target} (Live.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)),
      motive k t (insert (neg a) U) tail → motive (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)),
      motive k t (insert (bin d a b) U) tail →
      motive (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t : Nat} {S : Finset Sig} (h : Live target k t S) : motive k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩


private def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

private def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

private def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,
    BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self]
  simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

private def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private def bit (i : Fin 128) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

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
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
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

-- Truth tables on the 128 assignments with inputs 0 and 3 fixed to true.
private def roots : List Sig :=
  [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00,
   0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000,
   0xffffffffffffffff0000000000000000]

private def goal : Sig := 0xfffefffefafafafaffccffcceac00000

-- Live wires must separate every pair of rows separated by the target.
private def Factors (target : Sig) (s : Finset Sig) : Prop :=
  ∀ i j : Fin 128, (∀ a ∈ s, bit i a = bit j a) → bit i target = bit j target

private lemma live_factors {s k t} (h : Live target k t s) : Factors target s := by
  induction h using Live.ind with
  | stop hp => intro i j h; exact h _ (by simp)
  | @unary k t U a ha hf _ ih =>
    intro i j h
    apply ih i j
    simp only [Finset.forall_mem_insert] at h ⊢
    exact ⟨by rw [bit_neg, bit_neg, h.1], h.2⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    intro i j h
    apply ih i j
    simp only [Finset.forall_mem_insert] at h ⊢
    exact ⟨by rw [bit_bin, bit_bin, h.1, h.2.1], h.2.2⟩

private def collisions : List (Fin 128 × Fin 128) :=
  [(120,112),(94,90),(29,28),(113,49),(39,7),(22,6),(35,33),(120,88),
   (78,14),(30,28),(25,9),(97,96),(100,96),(29,21),(114,112),(23,19),
   (104,96),(91,90),(27,19)]

private def pass (l : List Sig) : Bool :=
  collisions.all fun (i,j) => bit i goal == bit j goal ||
    l.any (fun a => bit i a != bit j a)

private lemma pass_of_factors (h : Factors goal l.toFinset) : pass l = true := by
  unfold pass
  rw [List.all_eq_true]
  rintro ⟨i,j⟩ _
  by_cases e : bit i goal = bit j goal
  · simp [e]
  · have hh : (l.any fun a => bit i a != bit j a) = true := by
      rw [List.any_eq_true]
      by_contra hn
      apply e (h i j ?_)
      intro a ha
      by_contra he
      exact hn ⟨a, List.mem_toFinset.mp ha, by simp [he]⟩
    simp [hh]

private def rem1 (l : List Sig) (a : Sig) (keep : Bool) :=
  l.filter fun x => x != a || keep

private def rem2 (l : List Sig) (a b : Sig) (ka kb : Bool) :=
  rem1 (rem1 l a ka) b kb

private def flags : List Bool := [false,true]

private lemma mem_flags (a : Bool) : a ∈ flags := by cases a <;> simp [flags]

private def next (n : Nat) (l : List Sig) : List (List Sig) :=
  (l.flatMap (fun a =>
    (flags.map fun ka => neg a :: rem1 l a ka) ++
      (l.filter (· != a)).flatMap (fun b =>
        flags.flatMap (fun d => flags.flatMap (fun ka =>
          flags.map fun kb => bin d a b :: rem2 l a b ka kb))))).filter
    fun w => decide (w.toFinset.card ≤ n) && pass w

private lemma rem1_set (l : List Sig) (u : Finset Sig) (a : Sig)
    (h : l.toFinset = insert a u) :
    (rem1 l a (decide (a ∈ u))).toFinset = u := by
  ext x
  have hx : x ∈ l ↔ x = a ∨ x ∈ u := by
    rw [← List.mem_toFinset, h, Finset.mem_insert]
  simp only [rem1, List.mem_toFinset, List.mem_filter, hx, Bool.or_eq_true,
    bne_iff_ne, decide_eq_true_eq]
  by_cases e : x = a
  · subst x; simp
  · simp [e]

private lemma rem2_set (l : List Sig) (u : Finset Sig) (a b : Sig) (hne : a ≠ b)
    (h : l.toFinset = insert a (insert b u)) :
    (rem2 l a b (decide (a ∈ u)) (decide (b ∈ u))).toFinset = u := by
  have h1 := rem1_set l (insert b u) a h
  simp only [Finset.mem_insert, hne, false_or] at h1
  exact rem1_set _ u b h1

private lemma lift_live {l : List Sig} {k t : Nat} (h : Live goal (k+1) t l.toFinset)
    (n : Nat) (hn : k+1 ≤ n) :
    ∃ w ∈ next n l, ∃ t', Live goal k t' w.toFinset := by
  rcases h with ⟨u,U,a,rfl,hs,ha,hf,tail⟩ | ⟨U,a,b,d,hs,ha,hb,hab,hf,tail⟩
  · let w := neg a :: rem1 l a (decide (a ∈ U))
    have he : w.toFinset = insert (neg a) U := by simp [w, rem1_set l U a hs]
    have ht : Live goal k u w.toFinset := he ▸ tail
    have hc := (live_size ht).2
    have ham : a ∈ l := List.mem_toFinset.mp (hs.symm ▸ Finset.mem_insert_self a U)
    refine ⟨w, List.mem_filter.mpr ⟨?_, ?_⟩, u, ht⟩
    · apply List.mem_flatMap.mpr
      refine ⟨a, ham, List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨_, ?_, rfl⟩))⟩
      exact mem_flags _
    · simp [pass_of_factors (live_factors ht), show w.toFinset.card ≤ n by omega]
  · let w := bin d a b :: rem2 l a b (decide (a ∈ U)) (decide (b ∈ U))
    have he : w.toFinset = insert (bin d a b) U := by simp [w, rem2_set l U a b hab hs]
    have ht : Live goal k t w.toFinset := he ▸ tail
    have hc := (live_size ht).2
    have ham : a ∈ l := List.mem_toFinset.mp (hs.symm ▸ Finset.mem_insert_self a _)
    have hbm : b ∈ l := List.mem_toFinset.mp (hs.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self b U))
    refine ⟨w, List.mem_filter.mpr ⟨?_, ?_⟩, t, ht⟩
    · apply List.mem_flatMap.mpr
      refine ⟨a,ham,List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨b,?_,?_⟩))⟩
      · simp [hbm, hab.symm]
      · exact List.mem_flatMap.mpr ⟨d, mem_flags _, List.mem_flatMap.mpr
          ⟨_, mem_flags _, List.mem_map.mpr ⟨_, mem_flags _, rfl⟩⟩⟩
    · simp [pass_of_factors (live_factors ht), show w.toFinset.card ≤ n by omega]

-- From seven roots a live derivation of length at most seven must still have
-- at most seven live signals after its first step, then at most six.
set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private lemma no_two : (next 7 roots).flatMap (next 6) = [] := by decide +kernel

private lemma all_roots (h : Factors goal s) (sub : s ⊆ roots.toFinset) :
    s = roots.toFinset := by
  have cert : roots.all (fun a => !(pass (rem1 roots a false))) = true := by decide +kernel
  apply Finset.Subset.antisymm sub
  intro a ha
  by_contra hn
  have hf : Factors goal (rem1 roots a false).toFinset := by
    intro i j hij
    exact h i j fun b hb => hij b (by
      simp [rem1, List.mem_toFinset.mp (sub hb), show b ≠ a from fun e => hn (e ▸ hb)])
  have ht := List.all_eq_true.mp cert a (List.mem_toFinset.mp ha)
  simp [pass_of_factors hf] at ht

private lemma too_short {k t s} (h : Live goal k t s) (hk : k ≤ 7) (hs : s ⊆ roots.toFinset) :
    False := by
  have hs' := all_roots (live_factors h) hs
  subst s
  have hc := (live_size h).2
  have h7 : roots.toFinset.card = 7 := by decide +kernel
  obtain ⟨m,rfl⟩ : ∃ m, k = m+1+1 := ⟨k-2, by omega⟩
  obtain ⟨w,hw,u,hu⟩ := lift_live h 7 (by omega)
  obtain ⟨v,hv,t',ht'⟩ := lift_live hu 6 (by omega)
  have hm : v ∈ (next 7 roots).flatMap (next 6) := List.mem_flatMap.mpr ⟨w,hw,hv⟩
  rw [no_two] at hm
  exact List.not_mem_nil hm

private lemma execute_append (gs hs : List Gate) (w : List Sig) :
    execute (gs ++ hs) w = execute hs (execute gs w) := by
  simp [execute, List.foldl_append]

private lemma execute_len (gs : List Gate) (w : List Sig) :
    (execute gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [execute]
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).length = _
    rw [ih]
    simp
    omega

private lemma execute_ext (gs : List Gate) (w : List Sig) :
    ∃ l, execute gs w = w ++ l := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (w++[gv w g])
    exact ⟨gv w g::l,by simpa [execute,List.append_assoc] using hl⟩

private lemma read_prefix {gs : List Gate} {w : List Sig} {i : Nat} :
    i < w.length → (execute gs w).getD i zero = w.getD i zero := by
  intro hi
  obtain ⟨l,hl⟩ := execute_ext gs w
  rw [hl, List.getD_append _ _ _ _ hi]

private def wirePrefix (gs : List Gate) (w : List Sig) (j : Nat) :=
  execute (gs.take j) w

private lemma prefix_len {gs : List Gate} {w : List Sig} {j : Nat} (hj : j ≤ gs.length) :
    (wirePrefix gs w j).length = w.length + j := by simp [wirePrefix, execute_len, Nat.min_eq_left hj]

private lemma take_succ_of_get {gs : List Gate} {j : Nat} {g : Gate}
    (h : gs[j]? = some g) : gs.take (j+1) = gs.take j ++ [g] := by
  induction gs generalizing j with
  | nil => simp at h
  | cons a gs ih =>
    cases j with
    | zero =>
      have ha : a = g := by simpa using h
      simp [ha]
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      simp [List.take, ih h]

private lemma prefix_read_gate {gs : List Gate} {w : List Sig} {j k : Nat} {g : Gate}
    (hg : gs[j]? = some g) (hjk : j < k) :
    (wirePrefix gs w k).getD (w.length+j) zero = gv (wirePrefix gs w j) g := by
  have hget : (gs.take k)[j]? = some g := by simpa [List.getElem?_take, hjk] using hg
  have hd : gs.take k = (gs.take j ++ [g]) ++ (gs.take k).drop (j+1) := by
    conv_lhs => rw [← List.take_append_drop (j+1) (gs.take k), take_succ_of_get hget,
      List.take_take, Nat.min_eq_left (by omega : j ≤ k)]
  unfold wirePrefix
  rw [hd, execute_append, execute_append]
  change (execute _ ((execute (gs.take j) w) ++ [gv (execute (gs.take j) w) g])).getD _ _ = _
  have hj : j ≤ gs.length := by
    by_contra! hn
    simp [List.getElem?_eq_none (by omega : gs.length ≤ j)] at hg
  have hlen : (execute (gs.take j) w).length = w.length+j := prefix_len hj
  rw [← hlen, read_prefix (by simp), List.getD_append_right _ _ _ _ (by omega)]
  simp

private lemma pull_free {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z) (sub : ∀ a ∈ S, a ∈ w++[z]) : ∀ a ∈ S, a ∈ w := by
  intro a ha
  have ha' : a ∈ w ∨ a = z := by simpa using sub a ha
  rcases ha' with hmem | rfl
  · exact hmem
  · exact hz.resolve_right (fun hn => hn (live_proper h _ ha))

private lemma extract_savings (gs : List Gate) (w : List Sig) (skip : Finset Nat)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hs : ∀ i ∈ skip, w.length ≤ i ∧ i < w.length + gs.length ∧
      ∀ g, gs[i-w.length]? = some g →
        represented (wirePrefix gs w (i-w.length)) (gv (wirePrefix gs w (i-w.length)) g))
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k + skip.card ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w skip with
  | nil =>
    have he : skip = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have := hs i hi
      simp at this
      omega
    exact ⟨0,0,{target},by simp [he],Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    let w' := w++[gv w g]
    let skip' := skip.erase w.length
    have hl : w'.length = w.length+1 := by simp [w']
    have hskip : ∀ i ∈ skip', w'.length ≤ i ∧ i < w'.length + gs.length ∧
        ∀ a, gs[i-w'.length]? = some a →
          represented (wirePrefix gs w' (i-w'.length)) (gv (wirePrefix gs w' (i-w'.length)) a) := by
      intro i hi
      obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hi
      obtain ⟨hlo,hhi,hr⟩ := hs i hm
      refine ⟨by omega,by simp at hhi; omega,?_⟩
      intro a ha
      have he : i-w.length = (i-w'.length)+1 := by omega
      rw [he] at hr
      exact hr a ha
    obtain ⟨k,t,S,hk,ht,hS⟩ := ih w' skip' (fun a ha => legal a (by simp [ha])) hskip hout
    by_cases he : w.length ∈ skip
    · have hrep := (hs w.length he).2.2 g (by simp)
      have hr : represented w (gv w g) := by simpa [wirePrefix,execute] using hrep
      have hc := Finset.card_erase_add_one he
      refine ⟨k,t,S,?_,ht,pull_free ht hr hS⟩
      change skip'.card + 1 = skip.card at hc
      simp
      omega
    · obtain ⟨l,u,T,hl',hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hS
      have hEq : skip' = skip := Finset.erase_eq_of_notMem he
      rw [hEq] at hk
      exact ⟨l,u,T,by simp; omega,hu,hT⟩

private def roots9 : List Sig :=
  [one, roots.getD 0 zero, roots.getD 1 zero, one, roots.getD 2 zero,
    roots.getD 3 zero, roots.getD 4 zero, roots.getD 5 zero, roots.getD 6 zero]

private def sample (r : Fin 128) (j : Fin 9) := bit r (roots9.getD j.val zero)

private def f (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
    (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

private lemma table : ∀ r : Fin 128, bit r goal = f (sample r) := by decide +kernel
private lemma good_goal : proper goal := by unfold proper; decide +kernel
private lemma roots9_len : roots9.length = 9 := rfl

private lemma table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Fin 128) : bit r ((execute C.gates roots9).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  have hlist : List.ofFn (fun j : Fin 9 => roots9.getD j.val zero) = roots9 := rfl
  have hsample : List.ofFn (sample r) = roots9.map (bit r) := by
    rw [← hlist, List.map_ofFn]
    rfl
  rw [← b_read, execute_bits _ _ _ (fun g hg => (h g hg).1), hsample]
  rfl

private lemma only_roots {S : Finset Sig} {k t} (h : Live goal k t S)
    (sub : ∀ a ∈ S, a ∈ roots9) : S ⊆ roots.toFinset := by
  intro a ha
  have hn := (live_proper h a ha).2
  have hm := sub a ha
  simp [roots9, roots] at hm ⊢
  tauto

private def Shape (n : Nat) (g : Gate) : Prop :=
  (g.op = .not ∧ ∃ a, a < n ∧ g.inputs = [a]) ∨
  ((g.op = .and ∨ g.op = .or) ∧ ∃ a b, a < b ∧ b < n ∧ g.inputs = [a,b])

private lemma shape_const {w : List Sig} {g : Gate} {i : Nat}
    (h : Shape w.length g) (hi : i ∈ g.inputs) (hv : w.getD i zero = one) :
    represented w (gv w g) := by
  obtain ⟨o, l⟩ := g
  rcases h with ⟨ho,a,ha,rfl⟩ | ⟨ho,a,b,hab,hb,rfl⟩
  · have he : i = a := by simpa using hi
    subst i
    cases ho
    have hh : gv w ⟨.not,[a]⟩ = zero := by
      change neg (w.getD a zero) = zero
      rw [hv, neg_laws.2]
    rw [hh]
    exact Or.inr (fun hp => hp.1 rfl)
  · have he : i = a ∨ i = b := by simpa using hi
    rcases ho with rfl | rfl
    · rcases he with rfl | rfl
      · rw [show gv w ⟨.and,[i,b]⟩ = w.getD b zero by
          simp only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,
            (bin_laws _).1,hv]
          rw [bin_comm, (bin_laws _).1]]
        exact get_rep w b
      · rw [show gv w ⟨.and,[a,i]⟩ = w.getD a zero by
          simp only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,
            hv,(bin_laws _).1]]
        exact get_rep w a
    · have hh : gv w ⟨.or,[a,b]⟩ = one := by
        rcases he with rfl | rfl
        · simp only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,
            (bin_laws _).2.1,hv]
          rw [bin_comm, (bin_laws _).2.2.2.1]
        · simp only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,
            hv,(bin_laws _).2.1,(bin_laws _).2.2.2.1]
      rw [hh]
      exact Or.inr (fun hp => hp.2 rfl)

private lemma shape_both {w : List Sig} {g : Gate} {i j : Nat}
    (h : Shape w.length g) (hne : i ≠ j) (hi : i ∈ g.inputs) (hj : j ∈ g.inputs)
    (hvi : w.getD i zero = one) (hvj : w.getD j zero = one) :
    gv w g = one := by
  obtain ⟨o,l⟩ := g
  rcases h with ⟨ho,a,ha,rfl⟩ | ⟨ho,a,b,hab,hb,rfl⟩
  · simp at hi hj
    omega
  · have ei : i = a ∨ i = b := by simpa using hi
    have ej : j = a ∨ j = b := by simpa using hj
    have ha : w.getD a zero = one := by
      rcases ei with rfl | rfl <;> rcases ej with rfl | rfl <;> first | contradiction | assumption
    have hb : w.getD b zero = one := by
      rcases ei with rfl | rfl <;> rcases ej with rfl | rfl <;> first | contradiction | assumption
    rcases ho with rfl | rfl
    · simp only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,ha,hb,(bin_laws _).1]
    · simp only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,ha,hb,
        (bin_laws _).2.1,(bin_laws _).2.2.2.1]

private lemma four_skips (gs : List Gate)
    (form : ∀ j : Fin gs.length, Shape (9+j.val) (gs.get j))
    (live : ∀ j : Fin gs.length, j.val+1 < gs.length →
      ∃ k : Fin gs.length, j.val < k.val ∧ 9+j.val ∈ (gs.get k).inputs)
    (g0 : gs.head? = some ⟨.or,[0,1]⟩)
    (g1 : gs.tail.head? = some ⟨.or,[3,8]⟩)
    (last : (execute gs roots9).getD (8+gs.length) zero = goal) :
    ∃ skip : Finset Nat, skip.card = 4 ∧
      ∀ i ∈ skip, roots9.length ≤ i ∧ i < roots9.length + gs.length ∧
        ∀ g, gs[i-roots9.length]? = some g →
          represented (wirePrefix gs roots9 (i-roots9.length)) (gv (wirePrefix gs roots9 (i-roots9.length)) g) := by
  have h0 : gs[0]? = some ⟨.or,[0,1]⟩ := by
    cases gs with
    | nil => simp at g0
    | cons => exact g0
  have h1 : gs[1]? = some ⟨.or,[3,8]⟩ := by simpa using g1
  have hlt {j g} (h : gs[j]? = some g) : j < gs.length := by
    by_contra! hn
    simp [List.getElem?_eq_none hn] at h
  have hsize := hlt h1
  have HShape {j g} (h : gs[j]? = some g) :
      Shape (wirePrefix gs roots9 j).length g := by
    have hj := hlt h
    rw [prefix_len (Nat.le_of_lt hj), roots9_len]
    have he : gs.get ⟨j,hj⟩ = g := by simpa [List.getElem?_eq_getElem hj] using h
    rw [← he]
    exact form ⟨j,hj⟩
  have const0 : gv (wirePrefix gs roots9 0) ⟨.or,[0,1]⟩ = one := by
    change gv roots9 ⟨.or,[0,1]⟩ = one
    decide +kernel
  have gsplit : gs.take 1 = [⟨.or,[0,1]⟩] := by
    cases gs with
    | nil => simp at g0
    | cons a tail =>
      have ha : a = ⟨.or,[0,1]⟩ := by simpa using g0
      simp [ha]
  have const1 : gv (wirePrefix gs roots9 1) ⟨.or,[3,8]⟩ = one := by
    unfold wirePrefix
    rw [gsplit]
    decide +kernel
  have read0 {j} (h : 0 < j) : (wirePrefix gs roots9 j).getD 9 zero = one := by
    simpa [roots9_len, const0] using prefix_read_gate (w := roots9) h0 h
  have read1 {j} (h : 1 < j) : (wirePrefix gs roots9 j).getD 10 zero = one := by
    simpa [roots9_len, const1] using prefix_read_gate (w := roots9) h1 h
  obtain ⟨p,hp,hpMem⟩ := live ⟨0,hlt h0⟩ (by simpa using hsize)
  change 0 < p.val at hp
  change 9 ∈ (gs.get p).inputs at hpMem
  have hp1 : 1 < p.val := by
    by_contra! hh
    have he : p.val = 1 := by omega
    have hs : gs[p.val]? = some (gs.get p) := by simp
    rw [he,h1] at hs
    rw [← Option.some.inj hs] at hpMem
    simp at hpMem
  have hpLt := p.isLt
  obtain ⟨q,hq,hqMem⟩ := live ⟨1,hsize⟩ (by change 2 < gs.length; omega)
  change 1 < q.val at hq
  change 10 ∈ (gs.get q).inputs at hqMem
  let Saves (j : Nat) := ∀ g, gs[j]? = some g →
    represented (wirePrefix gs roots9 j) (gv (wirePrefix gs roots9 j) g)
  have saved0 : Saves 0 := by
    intro g hg
    rw [h0] at hg
    cases hg
    rw [const0]
    exact Or.inr (fun h => h.2 rfl)
  have saved1 : Saves 1 := by
    intro g hg
    rw [h1] at hg
    cases hg
    rw [const1]
    exact Or.inr (fun h => h.2 rfl)
  have getEq {k : Fin gs.length} {g} (h : gs[k.val]? = some g) : gs.get k = g := by
    simpa [List.getElem?_eq_getElem k.isLt] using h
  have savedp : Saves p.val := by
    intro g hg
    rw [getEq hg] at hpMem
    exact shape_const (HShape hg) hpMem (read0 (by omega))
  have savedq : Saves q.val := by
    intro g hg
    rw [getEq hg] at hqMem
    exact shape_const (HShape hg) hqMem (read1 (by omega))
  have out (a b : Fin gs.length) (ha : 1 < a.val) (hb : 1 < b.val)
      (hne : a.val ≠ b.val) (sa : Saves a.val) (sb : Saves b.val) :
      ∃ skip : Finset Nat, skip.card = 4 ∧
        ∀ i ∈ skip, roots9.length ≤ i ∧ i < roots9.length + gs.length ∧
          ∀ g, gs[i-roots9.length]? = some g →
            represented (wirePrefix gs roots9 (i-roots9.length)) (gv (wirePrefix gs roots9 (i-roots9.length)) g) := by
    refine ⟨{9,10,9+a.val,9+b.val}, ?_, ?_⟩
    · have hd9 : 9 ∉ ({10,9+a.val,9+b.val} : Finset Nat) := by
        simp only [Finset.mem_insert,Finset.mem_singleton]
        omega
      have hd10 : 10 ∉ ({9+a.val,9+b.val} : Finset Nat) := by
        simp only [Finset.mem_insert,Finset.mem_singleton]
        omega
      have hda : 9+a.val ∉ ({9+b.val} : Finset Nat) := by
        simp only [Finset.mem_singleton]
        omega
      rw [Finset.card_insert_of_notMem hd9, Finset.card_insert_of_notMem hd10,
        Finset.card_insert_of_notMem hda, Finset.card_singleton]
    · intro i hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact ⟨by simp [roots9_len],by simp [roots9_len]; omega, saved0⟩
      · exact ⟨by simp [roots9_len],by simp [roots9_len]; omega, saved1⟩
      · refine ⟨by simp [roots9_len],by simp [roots9_len],?_⟩
        simpa only [roots9_len, Nat.add_sub_cancel_left] using sa
      · refine ⟨by simp [roots9_len],by simp [roots9_len],?_⟩
        simpa only [roots9_len, Nat.add_sub_cancel_left] using sb
  by_cases epq : p.val = q.val
  · have ep : p = q := Fin.ext epq
    have gh : gs[p.val]? = some (gs.get p) := by simp
    have both : gv (wirePrefix gs roots9 p.val) (gs.get p) = one :=
      shape_both (HShape gh) (by decide : 9 ≠ 10) (by simpa using hpMem)
        (by simpa [← ep] using hqMem) (read0 (by omega)) (read1 hp1)
    have hnlast : p.val+1 < gs.length := by
      by_contra! hn
      have he : 9+p.val = 8+gs.length := by have := p.isLt; omega
      have hr := prefix_read_gate (w := roots9) gh p.isLt
      rw [roots9_len, he, both] at hr
      have hfull : wirePrefix gs roots9 gs.length = execute gs roots9 := by simp [wirePrefix]
      rw [hfull,last] at hr
      exact good_goal.2 hr
    obtain ⟨r,hr,hrMem⟩ := live p hnlast
    refine out p r hp1 (by omega) (by omega) savedp ?_
    intro g hg
    rw [getEq hg] at hrMem
    have hread := prefix_read_gate (w := roots9) gh hr
    rw [both, roots9_len] at hread
    exact shape_const (HShape hg) hrMem hread
  · exact out p q hp1 (by omega) epq savedp savedq

end PEqualNP.Outside.L_meta_27695_aux

open PEqualNP.Outside.L_meta_27695_aux in
theorem PEqualNP.Outside.L_meta_27695 :
¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 8]⟩) := by
  rintro ⟨C,hC,hsize,he,hout,hform,_,hlive,h0,h1⟩
  change C.gates.length ≤ 11 at hsize
  change C.output + 1 = 9 + C.gates.length at hout
  have eq : (execute C.gates roots9).getD (8+C.gates.length) zero = goal := by
    rw [show 8+C.gates.length = C.output by omega]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Fin 128 := ⟨j,hj⟩
    exact (table_eval C hC C.output r).trans ((he (sample r)).trans (table r).symm)
  obtain ⟨s,hs,hskip⟩ := four_skips C.gates hform hlive h0 h1 eq
  have hm := get_rep (execute C.gates roots9) (8+C.gates.length)
  rw [eq] at hm
  have hmem := hm.resolve_right (fun hn => hn good_goal)
  obtain ⟨k,t,S,hk,hL,hS⟩ := extract_savings C.gates roots9 s hC hskip good_goal hmem
  exact too_short hL (by omega) (only_roots hL hS)

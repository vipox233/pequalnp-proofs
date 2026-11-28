import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1179_aux

abbrev Site (n : ℕ) := Fin n
abbrev Word (n : ℕ) := Finset (Site n)
abbrev Edge (n : ℕ) := {ij : Site n × Site n // ij.1 < ij.2}
abbrev Signing (n : ℕ) := Edge n → Bool × Bool

def region (n : ℕ) (s : Signing n) : Finset (Word n) :=
  Finset.univ.filter (fun x =>
    ∀ e : Edge n, (decide (e.val.1 ∈ x), decide (e.val.2 ∈ x)) ≠ s e)

def tree (n : ℕ) (X : Finset (Word n)) : Prop :=
  ∃ node : Fin (n + 1) → Word n, ∃ dir : Equiv.Perm (Site n), ∃ parent : Site n → Fin (n + 1),
    X = Finset.univ.image node ∧ ∀ i : Site n,
      (parent i).val ≤ i.val ∧ node i.succ =
        (if dir i ∈ node (parent i) then (node (parent i)).erase (dir i)
         else insert (dir i) (node (parent i)))

def largest (n : ℕ) : Finset (Signing n) :=
  Finset.univ.filter (fun s => (region n s).card = n + 1)

section Part1_Shift

def xorWord {n : ℕ} (a b : Word n) : Word n :=
  Finset.univ.filter (fun i => decide (i ∈ a) != decide (i ∈ b))

lemma mem_xorWord {n : ℕ} (a b : Word n) (c : Site n) :
    c ∈ xorWord a b ↔ (decide (c ∈ a) != decide (c ∈ b)) = true := by
  simp [xorWord]

lemma decide_mem_xorWord {n : ℕ} (a b : Word n) (c : Site n) :
    decide (c ∈ xorWord a b) = (decide (c ∈ a) != decide (c ∈ b)) := by
  by_cases h : c ∈ xorWord a b
  · rw [decide_eq_true h]; exact ((mem_xorWord a b c).mp h).symm
  · rw [decide_eq_false h]
    cases hb : (decide (c ∈ a) != decide (c ∈ b))
    · rfl
    · exact absurd ((mem_xorWord a b c).mpr hb) h

lemma xorWord_invol {n : ℕ} (r x : Word n) : xorWord (xorWord x r) r = x := by
  ext c
  rw [mem_xorWord, decide_mem_xorWord]
  by_cases h1 : c ∈ x <;> by_cases h2 : c ∈ r <;> simp [h1, h2]

lemma xorWord_self {n : ℕ} (r : Word n) : xorWord r r = ∅ := by
  ext c; rw [mem_xorWord]; simp

lemma xorWord_empty_right {n : ℕ} (x : Word n) : xorWord x ∅ = x := by
  ext c; rw [mem_xorWord]; simp

lemma xorWord_empty_left {n : ℕ} (x : Word n) : xorWord ∅ x = x := by
  ext c; rw [mem_xorWord]; simp

lemma xorWord_comm {n : ℕ} (a b : Word n) : xorWord a b = xorWord b a := by
  ext c
  rw [mem_xorWord, mem_xorWord]
  cases decide (c ∈ a) <;> cases decide (c ∈ b) <;> simp

lemma xorWord_assoc {n : ℕ} (a b c : Word n) :
    xorWord (xorWord a b) c = xorWord a (xorWord b c) := by
  ext i
  simp only [mem_xorWord, decide_mem_xorWord]
  cases decide (i ∈ a) <;> cases decide (i ∈ b) <;> cases decide (i ∈ c) <;> simp

lemma xorWord_inj {n : ℕ} (r : Word n) : Function.Injective (fun x : Word n => xorWord x r) := by
  intro x y h
  have := congrArg (fun z => xorWord z r) h
  simpa [xorWord_invol] using this

lemma xorWord_inj_left {n : ℕ} (r : Word n) : Function.Injective (fun x : Word n => xorWord r x) := by
  intro x y h
  have := congrArg (fun z => xorWord r z) h
  simpa [xorWord_comm r, xorWord_invol] using this

lemma xorWord_eq_empty_iff {n : ℕ} (x r : Word n) : xorWord x r = ∅ ↔ x = r := by
  constructor
  · intro h
    have h1 := congrArg (fun z => xorWord z r) h
    rwa [xorWord_invol, xorWord_empty_left] at h1
  · rintro rfl; exact xorWord_self _

lemma stepWord_eq_xorWord {n : ℕ} (w : Word n) (d : Site n) :
    (if d ∈ w then w.erase d else insert d w) = xorWord w {d} := by
  ext c
  by_cases hdw : d ∈ w <;> by_cases hcd : c = d
  · subst hcd; simp [hdw, xorWord]
  · simp [hdw, hcd, xorWord]
  · subst hcd; simp [hdw, xorWord]
  · simp [hdw, hcd, xorWord]

lemma insert_eq_xorWord {n : ℕ} {w : Word n} {d : Site n} (hd : d ∉ w) :
    insert d w = xorWord w {d} := by
  rw [← stepWord_eq_xorWord w d]
  simp [hd]

def shiftSigning {n : ℕ} (r : Word n) (s : Signing n) : Signing n :=
  fun e => (Bool.xor (s e).1 (decide (e.val.1 ∈ r)), Bool.xor (s e).2 (decide (e.val.2 ∈ r)))

lemma shiftSigning_invol {n : ℕ} (r : Word n) (s : Signing n) :
    shiftSigning r (shiftSigning r s) = s := by
  funext e
  dsimp [shiftSigning]
  ext <;> simp

lemma mem_region_shiftSigning {n : ℕ} (r : Word n) (s : Signing n) (x : Word n) :
    xorWord x r ∈ region n (shiftSigning r s) ↔ x ∈ region n s := by
  simp only [region, Finset.mem_filter, Finset.mem_univ, true_and]
  refine forall_congr' fun e => ?_
  dsimp [shiftSigning]
  rw [decide_mem_xorWord, decide_mem_xorWord]
  constructor
  · intro h hEq
    apply h
    have h1 := congrArg Prod.fst hEq
    have h2 := congrArg Prod.snd hEq
    dsimp at h1 h2
    ext <;> dsimp
    · cases decide (e.val.1 ∈ x) <;> cases decide (e.val.1 ∈ r) <;> cases (s e).1 <;> simp_all
    · cases decide (e.val.2 ∈ x) <;> cases decide (e.val.2 ∈ r) <;> cases (s e).2 <;> simp_all
  · intro h hEq
    apply h
    have h1 := congrArg Prod.fst hEq
    have h2 := congrArg Prod.snd hEq
    dsimp at h1 h2
    ext <;> dsimp
    · revert h1; cases decide (e.val.1 ∈ x) <;> cases decide (e.val.1 ∈ r) <;> cases (s e).1 <;> simp
    · revert h2; cases decide (e.val.2 ∈ x) <;> cases decide (e.val.2 ∈ r) <;> cases (s e).2 <;> simp

lemma region_shiftSigning {n : ℕ} (r : Word n) (s : Signing n) :
    region n (shiftSigning r s) = (region n s).image (fun x => xorWord x r) := by
  ext y
  rw [Finset.mem_image]
  constructor
  · intro hy
    refine ⟨xorWord y r, ?_, xorWord_invol r y⟩
    rw [← mem_region_shiftSigning r s, xorWord_invol]
    exact hy
  · rintro ⟨x, hx, rfl⟩
    exact (mem_region_shiftSigning r s x).mpr hx

lemma tree_shift {n : ℕ} (r : Word n) {X : Finset (Word n)} (hX : tree n X) :
    tree n (X.image (fun x => xorWord x r)) := by
  rcases hX with ⟨node, dir, parent, rfl, hstep⟩
  refine ⟨fun k => xorWord (node k) r, dir, parent, ?_, fun i => ?_⟩
  · ext w; simp [Finset.mem_image]
  · refine ⟨(hstep i).1, ?_⟩
    rw [stepWord_eq_xorWord]
    have hs := (hstep i).2
    rw [stepWord_eq_xorWord] at hs
    dsimp
    rw [hs, xorWord_assoc, xorWord_comm {dir i} r, ← xorWord_assoc]

lemma tree_shift_iff {n : ℕ} (r : Word n) (X : Finset (Word n)) :
    tree n (X.image (fun x => xorWord x r)) ↔ tree n X := by
  constructor
  · intro h
    have h2 := tree_shift r h
    have heq : (X.image (fun x => xorWord x r)).image (fun x => xorWord x r) = X := by
      ext w; simp [Finset.mem_image, xorWord_invol]
    rwa [heq] at h2
  · exact tree_shift r

end Part1_Shift

section Part2_TreeStructure

def buildNodeAux (n : ℕ) (r₀ : Word n) (dir : Equiv.Perm (Site n))
    (parent : Site n → Fin (n + 1)) (hp : ∀ i : Site n, (parent i).val ≤ i.val)
    (k : ℕ) : Word n :=
  match k with
  | 0 => r₀
  | m + 1 =>
    if hm : m < n then
      let prev := buildNodeAux n r₀ dir parent hp (parent ⟨m, hm⟩).val
      let d := dir ⟨m, hm⟩
      if d ∈ prev then prev.erase d else insert d prev
    else r₀
termination_by k
decreasing_by
  exact Nat.lt_succ_of_le (hp ⟨m, hm⟩)

def buildNode (n : ℕ) (r₀ : Word n) (dir : Equiv.Perm (Site n))
    (parent : Site n → Fin (n + 1)) (hp : ∀ i : Site n, (parent i).val ≤ i.val)
    (k : Fin (n + 1)) : Word n :=
  buildNodeAux n r₀ dir parent hp k.val

lemma buildNode_zero (n : ℕ) (r₀ : Word n) (dir : Equiv.Perm (Site n))
    (parent : Site n → Fin (n + 1)) (hp : ∀ i : Site n, (parent i).val ≤ i.val) :
    buildNode n r₀ dir parent hp 0 = r₀ := by
  dsimp [buildNode]; rw [buildNodeAux]

lemma buildNode_step (n : ℕ) (r₀ : Word n) (dir : Equiv.Perm (Site n))
    (parent : Site n → Fin (n + 1)) (hp : ∀ i : Site n, (parent i).val ≤ i.val)
    (i : Site n) :
    buildNode n r₀ dir parent hp i.succ =
      if dir i ∈ buildNode n r₀ dir parent hp (parent i) then
        (buildNode n r₀ dir parent hp (parent i)).erase (dir i)
      else insert (dir i) (buildNode n r₀ dir parent hp (parent i)) := by
  dsimp [buildNode]
  conv_lhs => rw [buildNodeAux]
  simp only [Fin.val_succ, i.isLt, ↓reduceDIte, Fin.eta]
  rfl

lemma tree_of_buildNode (n : ℕ) (r₀ : Word n) (dir : Equiv.Perm (Site n))
    (parent : Site n → Fin (n + 1)) (hp : ∀ i : Site n, (parent i).val ≤ i.val) :
    tree n (Finset.univ.image (buildNode n r₀ dir parent hp)) :=
  ⟨buildNode n r₀ dir parent hp, dir, parent, rfl, fun i => ⟨hp i, buildNode_step n r₀ dir parent hp i⟩⟩

lemma star_tree_exists (n : ℕ) : ∃ X : Finset (Word n), tree n X := by
  let parent : Site n → Fin (n + 1) := fun _ => 0
  have hp : ∀ i : Site n, (parent i).val ≤ i.val := fun _ => Nat.zero_le _
  exact ⟨_, tree_of_buildNode n ∅ (Equiv.refl _) parent hp⟩

def ancestorsAux (n : ℕ) (parent : Site n → Fin (n + 1))
    (hp : ∀ i : Site n, (parent i).val ≤ i.val) (k : ℕ) : Finset (Site n) :=
  match k with
  | 0 => ∅
  | m + 1 =>
    if hm : m < n then
      insert ⟨m, hm⟩ (ancestorsAux n parent hp (parent ⟨m, hm⟩).val)
    else ∅
termination_by k
decreasing_by
  exact Nat.lt_succ_of_le (hp ⟨m, hm⟩)

def ancestors (n : ℕ) (parent : Site n → Fin (n + 1))
    (hp : ∀ i : Site n, (parent i).val ≤ i.val) (k : Fin (n + 1)) : Finset (Site n) :=
  ancestorsAux n parent hp k.val

lemma ancestors_zero (n : ℕ) (parent : Site n → Fin (n + 1))
    (hp : ∀ i : Site n, (parent i).val ≤ i.val) :
    ancestors n parent hp 0 = ∅ := by
  dsimp [ancestors]; rw [ancestorsAux]

lemma ancestors_succ (n : ℕ) (parent : Site n → Fin (n + 1))
    (hp : ∀ i : Site n, (parent i).val ≤ i.val) (i : Site n) :
    ancestors n parent hp i.succ = insert i (ancestors n parent hp (parent i)) := by
  dsimp [ancestors]
  conv_lhs => rw [ancestorsAux]
  simp only [Fin.val_succ, i.isLt, ↓reduceDIte, Fin.eta]

lemma ancestorsAux_lt (n : ℕ) (parent : Site n → Fin (n + 1))
    (hp : ∀ i : Site n, (parent i).val ≤ i.val) :
    ∀ (k : ℕ) (j : Site n), j ∈ ancestorsAux n parent hp k → j.val < k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro j hj
    cases k with
    | zero => rw [ancestorsAux] at hj; simp at hj
    | succ m =>
      rw [ancestorsAux] at hj
      by_cases hm : m < n
      · simp only [hm, ↓reduceDIte, Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact Nat.lt_succ_self _
        · have hlt := ih (parent ⟨m, hm⟩).val (Nat.lt_succ_of_le (hp ⟨m, hm⟩)) j hj
          have hpm := hp ⟨m, hm⟩
          change (parent ⟨m, hm⟩).val ≤ m at hpm
          omega
      · simp only [hm, ↓reduceDIte, Finset.notMem_empty] at hj

lemma ancestors_lt (n : ℕ) (parent : Site n → Fin (n + 1))
    (hp : ∀ i : Site n, (parent i).val ≤ i.val) (k : Fin (n + 1)) (j : Site n)
    (hj : j ∈ ancestors n parent hp k) : j.val < k.val :=
  ancestorsAux_lt n parent hp k.val j hj

lemma self_mem_ancestors_succ (n : ℕ) (parent : Site n → Fin (n + 1))
    (hp : ∀ i : Site n, (parent i).val ≤ i.val) (i : Site n) :
    i ∈ ancestors n parent hp i.succ := by
  rw [ancestors_succ]; exact Finset.mem_insert_self _ _

lemma not_mem_ancestors_parent (n : ℕ) (parent : Site n → Fin (n + 1))
    (hp : ∀ i : Site n, (parent i).val ≤ i.val) (i : Site n) :
    i ∉ ancestors n parent hp (parent i) := by
  intro h
  have := ancestors_lt n parent hp (parent i) i h
  have := hp i
  omega

lemma node_eq_xorWord_ancestors {n : ℕ} (node : Fin (n + 1) → Word n)
    (dir : Equiv.Perm (Site n)) (parent : Site n → Fin (n + 1))
    (hstep : ∀ i : Site n, (parent i).val ≤ i.val ∧ node i.succ =
      (if dir i ∈ node (parent i) then (node (parent i)).erase (dir i)
       else insert (dir i) (node (parent i)))) :
    ∀ k : Fin (n + 1),
      node k = xorWord (node 0) ((ancestors n parent (fun i => (hstep i).1) k).image dir) := by
  let hp : ∀ i : Site n, (parent i).val ≤ i.val := fun i => (hstep i).1
  intro k
  rcases k with ⟨kv, hkv⟩
  induction kv using Nat.strong_induction_on with
  | ind kv ih =>
    cases kv with
    | zero =>
      have hk0 : (⟨0, hkv⟩ : Fin (n + 1)) = 0 := Fin.ext rfl
      rw [hk0, ancestors_zero, Finset.image_empty, xorWord_empty_right]
    | succ m =>
      have hm : m < n := by omega
      let i : Site n := ⟨m, hm⟩
      have hki : (⟨m + 1, hkv⟩ : Fin (n + 1)) = i.succ := Fin.ext rfl
      rw [hki]
      have hs := (hstep i).2
      rw [stepWord_eq_xorWord] at hs
      have ihp := ih (parent i).val (Nat.lt_succ_of_le (hp i)) (parent i).isLt
      have hpe : (⟨(parent i).val, (parent i).isLt⟩ : Fin (n + 1)) = parent i := Fin.ext rfl
      rw [hpe] at ihp
      rw [hs, ihp, xorWord_assoc, ancestors_succ, Finset.image_insert]
      have hnot : dir i ∉ (ancestors n parent hp (parent i)).image dir := by
        intro hmem
        obtain ⟨j, hj, hEq⟩ := Finset.mem_image.mp hmem
        have hj' := dir.injective hEq
        subst hj'
        exact not_mem_ancestors_parent n parent hp i hj
      rw [insert_eq_xorWord hnot]

lemma ancestors_inj {n : ℕ} (parent : Site n → Fin (n + 1))
    (hp : ∀ i : Site n, (parent i).val ≤ i.val) :
    Function.Injective (ancestors n parent hp) := by
  intro a b hab
  rcases a with ⟨va, ha⟩; rcases b with ⟨vb, hb⟩
  cases va with
  | zero =>
    have ha0 : (⟨0, ha⟩ : Fin (n + 1)) = 0 := Fin.ext rfl
    rw [ha0, ancestors_zero] at hab
    cases vb with
    | zero => rfl
    | succ mb =>
      have hb1 : (⟨mb + 1, hb⟩ : Fin (n + 1)) = (⟨mb, by omega⟩ : Site n).succ := Fin.ext rfl
      rw [hb1] at hab
      have hm := self_mem_ancestors_succ n parent hp ⟨mb, by omega⟩
      rw [← hab] at hm
      simp at hm
  | succ ma =>
    cases vb with
    | zero =>
      have hb0 : (⟨0, hb⟩ : Fin (n + 1)) = 0 := Fin.ext rfl
      have ha1 : (⟨ma + 1, ha⟩ : Fin (n + 1)) = (⟨ma, by omega⟩ : Site n).succ := Fin.ext rfl
      rw [hb0, ancestors_zero, ha1] at hab
      have hm := self_mem_ancestors_succ n parent hp ⟨ma, by omega⟩
      rw [hab] at hm
      simp at hm
    | succ mb =>
      let a' : Site n := ⟨ma, by omega⟩
      let b' : Site n := ⟨mb, by omega⟩
      have ha1 : (⟨ma + 1, ha⟩ : Fin (n + 1)) = a'.succ := Fin.ext rfl
      have hb1 : (⟨mb + 1, hb⟩ : Fin (n + 1)) = b'.succ := Fin.ext rfl
      rw [ha1, hb1] at hab
      have hma : a' ∈ ancestors n parent hp b'.succ := by
        rw [← hab]; exact self_mem_ancestors_succ n parent hp _
      have hmb : b' ∈ ancestors n parent hp a'.succ := by
        rw [hab]; exact self_mem_ancestors_succ n parent hp _
      have lt1 := ancestors_lt n parent hp a'.succ b' hmb
      have lt2 := ancestors_lt n parent hp b'.succ a' hma
      have : ma = mb := by
        change b'.val < a'.val + 1 at lt1
        change a'.val < b'.val + 1 at lt2
        dsimp [a', b'] at lt1 lt2
        omega
      subst this
      rfl

lemma tree_card_eq {n : ℕ} {X : Finset (Word n)} (hX : tree n X) : X.card = n + 1 := by
  rcases hX with ⟨node, dir, parent, rfl, hstep⟩
  have hnode := node_eq_xorWord_ancestors node dir parent hstep
  have hinj : Function.Injective node := by
    intro u v huv
    rw [hnode u, hnode v] at huv
    have him := xorWord_inj_left (node 0) huv
    exact ancestors_inj parent _ (Finset.image_injective dir.injective him)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]

lemma ancestors_mono {n : ℕ} (parent : Site n → Fin (n + 1))
    (hp : ∀ i : Site n, (parent i).val ≤ i.val) (i : Site n) :
    ∀ k : Fin (n + 1), i ∈ ancestors n parent hp k →
      ancestors n parent hp i.succ ⊆ ancestors n parent hp k := by
  intro k
  rcases k with ⟨kv, hkv⟩
  induction kv using Nat.strong_induction_on with
  | ind kv ih =>
    intro hi
    cases kv with
    | zero =>
      have hk0 : (⟨0, hkv⟩ : Fin (n + 1)) = 0 := Fin.ext rfl
      rw [hk0, ancestors_zero] at hi; simp at hi
    | succ m =>
      have hm : m < n := by omega
      have hkm : (⟨m + 1, hkv⟩ : Fin (n + 1)) = (⟨m, hm⟩ : Site n).succ := Fin.ext rfl
      rw [hkm] at hi ⊢
      have hi' := hi
      rw [ancestors_succ] at hi'
      rcases Finset.mem_insert.mp hi' with rfl | hip
      · exact Finset.Subset.refl _
      · conv_rhs => rw [ancestors_succ]
        have ihp := ih (parent ⟨m, hm⟩).val (Nat.lt_succ_of_le (hp ⟨m, hm⟩)) (parent ⟨m, hm⟩).isLt
        have hpe : (⟨(parent ⟨m, hm⟩).val, (parent ⟨m, hm⟩).isLt⟩ : Fin (n + 1)) = parent ⟨m, hm⟩ := Fin.ext rfl
        rw [hpe] at ihp
        exact (ihp hip).trans (Finset.subset_insert _ _)

lemma ancestors_dichotomy {n : ℕ} (parent : Site n → Fin (n + 1))
    (hp : ∀ i : Site n, (parent i).val ≤ i.val) (i j : Site n) (hij : i ≠ j) :
    ∃ bad : Bool × Bool,
      (∀ k : Fin (n + 1), (decide (i ∈ ancestors n parent hp k), decide (j ∈ ancestors n parent hp k)) ≠ bad) ∧
      (∀ b : Bool × Bool, b ≠ bad →
        ∃ k : Fin (n + 1), (decide (i ∈ ancestors n parent hp k), decide (j ∈ ancestors n parent hp k)) = b) := by
  by_cases hij1 : i ∈ ancestors n parent hp j.succ
  · have hjni : j ∉ ancestors n parent hp i.succ := by
      intro hmem
      have l1 := ancestors_lt n parent hp j.succ i hij1
      have l2 := ancestors_lt n parent hp i.succ j hmem
      simp only [Fin.val_succ] at l1 l2
      exact hij (Fin.ext (by omega))
    refine ⟨(false, true), fun k hEq => ?_, fun b hb => ?_⟩
    · have h1 := congrArg Prod.fst hEq; have h2 := congrArg Prod.snd hEq
      dsimp at h1 h2
      rw [decide_eq_false_iff_not] at h1; rw [decide_eq_true_iff] at h2
      exact h1 ((ancestors_mono parent hp j k h2) hij1)
    · rcases b with ⟨⟨⟩, ⟨⟩⟩
      · exact ⟨0, by simp [ancestors_zero]⟩
      · exact absurd rfl hb
      · exact ⟨i.succ, by simp [self_mem_ancestors_succ, hjni]⟩
      · exact ⟨j.succ, by simp [hij1, self_mem_ancestors_succ]⟩
  · by_cases hji1 : j ∈ ancestors n parent hp i.succ
    · refine ⟨(true, false), fun k hEq => ?_, fun b hb => ?_⟩
      · have h1 := congrArg Prod.fst hEq; have h2 := congrArg Prod.snd hEq
        dsimp at h1 h2
        rw [decide_eq_true_iff] at h1; rw [decide_eq_false_iff_not] at h2
        exact h2 ((ancestors_mono parent hp i k h1) hji1)
      · rcases b with ⟨⟨⟩, ⟨⟩⟩
        · exact ⟨0, by simp [ancestors_zero]⟩
        · exact ⟨j.succ, by simp [hij1, self_mem_ancestors_succ]⟩
        · exact absurd rfl hb
        · exact ⟨i.succ, by simp [self_mem_ancestors_succ, hji1]⟩
    · refine ⟨(true, true), fun k hEq => ?_, fun b hb => ?_⟩
      · have h1 := congrArg Prod.fst hEq; have h2 := congrArg Prod.snd hEq
        dsimp at h1 h2
        rw [decide_eq_true_iff] at h1 h2
        have hdisj : ∀ m : Fin (n + 1), ¬(i ∈ ancestors n parent hp m ∧ j ∈ ancestors n parent hp m) := by
          intro m
          rcases m with ⟨mv, hmv⟩
          induction mv using Nat.strong_induction_on with
          | ind mv ihm =>
            rintro ⟨him, hjm⟩
            cases mv with
            | zero =>
              have hm0 : (⟨0, hmv⟩ : Fin (n + 1)) = 0 := Fin.ext rfl
              rw [hm0, ancestors_zero] at him; simp at him
            | succ z =>
              have hz : z < n := by omega
              have hkz : (⟨z + 1, hmv⟩ : Fin (n + 1)) = (⟨z, hz⟩ : Site n).succ := Fin.ext rfl
              rw [hkz, ancestors_succ] at him hjm
              rcases Finset.mem_insert.mp him with rfl | himp
              · exact hji1 (by rw [ancestors_succ]; exact hjm)
              · rcases Finset.mem_insert.mp hjm with rfl | hjmp
                · exact hij1 (by rw [ancestors_succ]; exact Finset.mem_insert_of_mem himp)
                · exact ihm (parent ⟨z, hz⟩).val (Nat.lt_succ_of_le (hp ⟨z, hz⟩)) (parent ⟨z, hz⟩).isLt
                    ⟨himp, hjmp⟩
        exact hdisj k ⟨h1, h2⟩
      · rcases b with ⟨⟨⟩, ⟨⟩⟩
        · exact ⟨0, by simp [ancestors_zero]⟩
        · exact ⟨j.succ, by simp [hij1, self_mem_ancestors_succ]⟩
        · exact ⟨i.succ, by simp [self_mem_ancestors_succ, hji1]⟩
        · exact absurd rfl hb

lemma tree_signing_unique {n : ℕ} {X : Finset (Word n)} (hX : tree n X) :
    ∃ s : Signing n, X ⊆ region n s ∧
      ∀ e : Edge n, ∀ b : Bool × Bool, b ≠ s e →
        ∃ x ∈ X, (decide (e.val.1 ∈ x), decide (e.val.2 ∈ x)) = b := by
  rcases hX with ⟨node, dir, parent, rfl, hstep⟩
  let hp : ∀ i : Site n, (parent i).val ≤ i.val := fun i => (hstep i).1
  have hnode := node_eq_xorWord_ancestors node dir parent hstep
  have hpair : ∀ e : Edge n, ∃ bad : Bool × Bool,
      (∀ k : Fin (n + 1), (decide (e.val.1 ∈ node k), decide (e.val.2 ∈ node k)) ≠ bad) ∧
      (∀ b : Bool × Bool, b ≠ bad →
        ∃ k : Fin (n + 1), (decide (e.val.1 ∈ node k), decide (e.val.2 ∈ node k)) = b) := by
    intro e
    let i := dir.symm e.val.1
    let j := dir.symm e.val.2
    have hij : i ≠ j := fun h => e.property.ne (dir.symm.injective h)
    obtain ⟨bad0, hmiss, hhit⟩ := ancestors_dichotomy parent hp i j hij
    let r1 := decide (e.val.1 ∈ node 0)
    let r2 := decide (e.val.2 ∈ node 0)
    refine ⟨(Bool.xor r1 bad0.1, Bool.xor r2 bad0.2), fun k hEq => ?_, fun b hb => ?_⟩
    · apply hmiss k
      have hk := hnode k
      have hmem1 : (e.val.1 ∈ (ancestors n parent hp k).image dir) ↔ i ∈ ancestors n parent hp k := by
        simp [i, dir.apply_eq_iff_eq_symm_apply]
      have hmem2 : (e.val.2 ∈ (ancestors n parent hp k).image dir) ↔ j ∈ ancestors n parent hp k := by
        simp [j, dir.apply_eq_iff_eq_symm_apply]
      have hb1 : decide (e.val.1 ∈ node k) = Bool.xor r1 (decide (i ∈ ancestors n parent hp k)) := by
        rw [hk, decide_mem_xorWord, decide_eq_decide.mpr hmem1]
      have hb2 : decide (e.val.2 ∈ node k) = Bool.xor r2 (decide (j ∈ ancestors n parent hp k)) := by
        rw [hk, decide_mem_xorWord, decide_eq_decide.mpr hmem2]
      rw [hb1, hb2] at hEq
      have p1 := congrArg Prod.fst hEq; have p2 := congrArg Prod.snd hEq
      dsimp at p1 p2
      refine Prod.ext ?_ ?_
      · revert p1; cases r1 <;> cases decide (i ∈ ancestors n parent hp k) <;> cases bad0.1 <;> simp
      · revert p2; cases r2 <;> cases decide (j ∈ ancestors n parent hp k) <;> cases bad0.2 <;> simp
    · let b0 : Bool × Bool := (Bool.xor r1 b.1, Bool.xor r2 b.2)
      have hb0 : b0 ≠ bad0 := by
        intro hEq; apply hb
        have p1 := congrArg Prod.fst hEq; have p2 := congrArg Prod.snd hEq
        dsimp [b0] at p1 p2
        refine Prod.ext ?_ ?_
        · revert p1; cases r1 <;> cases b.1 <;> cases bad0.1 <;> simp
        · revert p2; cases r2 <;> cases b.2 <;> cases bad0.2 <;> simp
      obtain ⟨k, hk0⟩ := hhit b0 hb0
      refine ⟨k, ?_⟩
      have hk := hnode k
      have hmem1 : (e.val.1 ∈ (ancestors n parent hp k).image dir) ↔ i ∈ ancestors n parent hp k := by
        simp [i, dir.apply_eq_iff_eq_symm_apply]
      have hmem2 : (e.val.2 ∈ (ancestors n parent hp k).image dir) ↔ j ∈ ancestors n parent hp k := by
        simp [j, dir.apply_eq_iff_eq_symm_apply]
      have hb1 : decide (e.val.1 ∈ node k) = Bool.xor r1 (decide (i ∈ ancestors n parent hp k)) := by
        rw [hk, decide_mem_xorWord, decide_eq_decide.mpr hmem1]
      have hb2 : decide (e.val.2 ∈ node k) = Bool.xor r2 (decide (j ∈ ancestors n parent hp k)) := by
        rw [hk, decide_mem_xorWord, decide_eq_decide.mpr hmem2]
      have p1 := congrArg Prod.fst hk0; have p2 := congrArg Prod.snd hk0
      dsimp [b0] at p1 p2
      rw [hb1, hb2]
      refine Prod.ext ?_ ?_
      · revert p1; cases r1 <;> cases decide (i ∈ ancestors n parent hp k) <;> cases b.1 <;> simp
      · revert p2; cases r2 <;> cases decide (j ∈ ancestors n parent hp k) <;> cases b.2 <;> simp
  choose s hmiss hhit using hpair
  refine ⟨s, fun x hx => ?_, fun e b hb => ?_⟩
  · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    simp only [region, Finset.mem_filter, Finset.mem_univ, true_and]
    intro e
    exact hmiss e k
  · obtain ⟨k, hk⟩ := hhit e b hb
    exact ⟨node k, Finset.mem_image_of_mem _ (Finset.mem_univ k), hk⟩

end Part2_TreeStructure

section Part3_ExtendToTree

lemma card_word_le_pow {n : ℕ} (S : Finset (Word n)) : S.card ≤ 2 ^ n := by
  calc S.card ≤ (Finset.univ : Finset (Word n)).card := Finset.card_le_univ S
    _ = 2 ^ n := by simp [Word, Site]

lemma permSortByKey (n : ℕ) (f : Site n → ℕ) :
    ∃ dir : Equiv.Perm (Site n), ∀ i j : Site n, i.val ≤ j.val → f (dir i) ≤ f (dir j) := by
  let key : Site n → ℕ := fun c => f c * n + c.val
  have hkey_inj : Function.Injective key := by
    intro a b hab
    dsimp [key] at hab
    have h1 := congrArg (· % n) hab
    exact Fin.ext (by simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using h1)
  let S : Finset ℕ := Finset.univ.image key
  have hScard : S.card = n := by
    rw [Finset.card_image_of_injective _ hkey_inj, Finset.card_fin]
  let emb : Fin n ↪o ℕ := S.orderEmbOfFin hScard
  have hemb_mem : ∀ i : Site n, emb i ∈ S := fun i => Finset.orderEmbOfFin_mem S hScard i
  let g : Site n → Site n := fun i => Classical.choose (Finset.mem_image.mp (hemb_mem i))
  have hg_spec : ∀ i : Site n, key (g i) = emb i := fun i =>
    (Classical.choose_spec (Finset.mem_image.mp (hemb_mem i))).2
  have hg_inj : Function.Injective g := by
    intro i j hij
    apply emb.injective
    rw [← hg_spec i, ← hg_spec j, hij]
  let dir : Equiv.Perm (Site n) := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg_inj)
  refine ⟨dir, fun i j hij => ?_⟩
  have hk : key (dir i) ≤ key (dir j) := by
    simpa [dir, hg_spec] using emb.monotone hij
  dsimp [key] at hk
  have ha := (dir i).isLt
  have hb := (dir j).isLt
  by_contra hgt
  have h1 : f (dir j) + 1 ≤ f (dir i) := by omega
  have hmul := Nat.mul_le_mul_right n h1
  rw [Nat.add_mul, Nat.one_mul] at hmul
  omega

lemma empty_region_extend (n : ℕ) (hn : 0 < n) (s : Signing n) (h0 : ∅ ∈ region n s) :
    ∃ (dir : Equiv.Perm (Site n)) (parent : Site n → Fin (n + 1))
      (hp : ∀ i : Site n, (parent i).val ≤ i.val),
      region n s ⊆ Finset.univ.image (buildNode n ∅ dir parent hp) := by
  let X := region n s
  let col : Site n → Finset (Word n) := fun c => X.filter (fun x => c ∈ x)
  have hcol_pair : ∀ a b : Site n, a < b → Disjoint (col a) (col b) ∨ col a ⊆ col b ∨ col b ⊆ col a := by
    intro a b hab
    let e : Edge n := ⟨(a, b), hab⟩
    have h0e := (Finset.mem_filter.mp h0).2 e
    simp only [Finset.notMem_empty, decide_false] at h0e
    cases hs : s e with
    | mk b1 b2 =>
      cases b1 <;> cases b2
      · exact absurd hs.symm h0e
      · right; right
        intro x hx
        have hx' := Finset.mem_filter.mp hx
        have hxe := (Finset.mem_filter.mp hx'.1).2 e
        rw [Finset.mem_filter]
        refine ⟨hx'.1, ?_⟩
        by_contra hna
        apply hxe
        rw [hs]
        exact Prod.ext (decide_eq_false hna) (decide_eq_true hx'.2)
      · right; left
        intro x hx
        have hx' := Finset.mem_filter.mp hx
        have hxe := (Finset.mem_filter.mp hx'.1).2 e
        rw [Finset.mem_filter]
        refine ⟨hx'.1, ?_⟩
        by_contra hnb
        apply hxe
        rw [hs]
        exact Prod.ext (decide_eq_true hx'.2) (decide_eq_false hnb)
      · left
        rw [Finset.disjoint_left]
        intro x hxa hxb
        have hx' := Finset.mem_filter.mp hxa
        have hxe := (Finset.mem_filter.mp hx'.1).2 e
        apply hxe
        rw [hs]
        exact Prod.ext (decide_eq_true hx'.2) (decide_eq_true (Finset.mem_filter.mp hxb).2)
  have hcol_laminar : ∀ a b : Site n, Disjoint (col a) (col b) ∨ col a ⊆ col b ∨ col b ⊆ col a := by
    intro a b
    rcases lt_trichotomy a b with hab | rfl | hba
    · exact hcol_pair a b hab
    · right; left; exact Finset.Subset.refl _
    · rcases hcol_pair b a hba with hdisj | hba_sub | hab_sub
      · exact Or.inl hdisj.symm
      · exact Or.inr (Or.inr hba_sub)
      · exact Or.inr (Or.inl hab_sub)
  obtain ⟨dir, hdir_le⟩ := permSortByKey n (fun c => 2 ^ n - (col c).card)
  have hdir_card : ∀ i j : Site n, i.val ≤ j.val → (col (dir j)).card ≤ (col (dir i)).card := by
    intro i j hij
    have hdiff := hdir_le i j hij
    have hci : (col (dir i)).card ≤ 2 ^ n := card_word_le_pow _
    have hcj : (col (dir j)).card ≤ 2 ^ n := card_word_le_pow _
    omega
  let cands (i : Site n) : Finset (Site n) :=
    Finset.univ.filter (fun j : Site n => j.val < i.val ∧ (col (dir i)).Nonempty ∧ col (dir i) ⊆ col (dir j))
  let parent : Site n → Fin (n + 1) := fun i =>
    if h : (cands i).Nonempty then ((cands i).max' h).succ else 0
  have hp : ∀ i : Site n, (parent i).val ≤ i.val := by
    intro i
    dsimp [parent]
    split_ifs with h
    · exact (Finset.mem_filter.mp ((cands i).max'_mem h)).2.1
    · exact Nat.zero_le _
  have hanc_col : ∀ (i : Site n), (col (dir i)).Nonempty →
      ∀ j : Site n, j ∈ ancestors n parent hp i.succ ↔
        (j = i ∨ (j.val < i.val ∧ col (dir i) ⊆ col (dir j))) := by
    intro i
    rcases i with ⟨iv, hiv⟩
    induction iv using Nat.strong_induction_on with
    | ind iv ih =>
      intro hne j
      let ii : Site n := ⟨iv, hiv⟩
      change j ∈ ancestors n parent hp ii.succ ↔
        (j = ii ∨ (j.val < ii.val ∧ col (dir ii) ⊆ col (dir j)))
      rw [ancestors_succ]
      dsimp [parent]
      split_ifs with hc
      · set m := (cands ii).max' hc
        have hm_mem := Finset.mem_filter.mp ((cands ii).max'_mem hc)
        have hm_lt : m.val < ii.val := hm_mem.2.1
        have hsub_m : col (dir ii) ⊆ col (dir m) := hm_mem.2.2.2
        have hne_m : (col (dir m)).Nonempty := hne.mono hsub_m
        have ih_m := ih m.val hm_lt m.isLt hne_m j
        have hm_eq : (⟨m.val, m.isLt⟩ : Site n) = m := Fin.ext rfl
        rw [hm_eq] at ih_m
        rw [Finset.mem_insert, ih_m]
        constructor
        · rintro (rfl | rfl | ⟨hjm, hsub⟩)
          · left; rfl
          · right; exact ⟨hm_lt, hsub_m⟩
          · right; exact ⟨hjm.trans hm_lt, hsub_m.trans hsub⟩
        · rintro (rfl | ⟨hji, hsub⟩)
          · left; rfl
          · right
            have hjc : j ∈ cands ii := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji, hne, hsub⟩
            have hjle : j ≤ m := Finset.le_max' (cands ii) j hjc
            rcases eq_or_lt_of_le hjle with rfl | hjl
            · left; rfl
            · right
              refine ⟨hjl, ?_⟩
              rcases hcol_laminar (dir m) (dir j) with hdisj | hmj | hjm
              · exfalso
                obtain ⟨w, hw⟩ := hne
                exact Finset.disjoint_left.mp hdisj (hsub_m hw) (hsub hw)
              · exact hmj
              · have hc_le := hdir_card j m (Nat.le_of_lt hjl)
                exact (Finset.eq_of_subset_of_card_le hjm hc_le).symm ▸ Finset.Subset.refl _
      · simp only [Finset.mem_insert, ancestors_zero, Finset.notMem_empty, or_false]
        constructor
        · rintro rfl; left; rfl
        · rintro (rfl | ⟨hji, hsub⟩)
          · rfl
          · exfalso
            apply hc
            exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji, hne, hsub⟩⟩
  refine ⟨dir, parent, hp, fun x hx => ?_⟩
  rw [Finset.mem_image]
  by_cases hx0 : x = ∅
  · subst hx0
    exact ⟨0, Finset.mem_univ _, buildNode_zero n ∅ dir parent hp⟩
  · have hS_ne : (Finset.univ.filter (fun i : Site n => dir i ∈ x)).Nonempty := by
      obtain ⟨c, hcx⟩ := Finset.nonempty_iff_ne_empty.mpr hx0
      exact ⟨dir.symm c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hcx⟩⟩
    set Sx := Finset.univ.filter (fun i : Site n => dir i ∈ x)
    set i₀ := Sx.max' hS_ne
    have hi0_mem : dir i₀ ∈ x := (Finset.mem_filter.mp (Sx.max'_mem hS_ne)).2
    have hcol_ne : (col (dir i₀)).Nonempty := ⟨x, Finset.mem_filter.mpr ⟨hx, hi0_mem⟩⟩
    refine ⟨i₀.succ, Finset.mem_univ _, ?_⟩
    have hnode := node_eq_xorWord_ancestors (buildNode n ∅ dir parent hp) dir parent
      (fun i => ⟨hp i, buildNode_step n ∅ dir parent hp i⟩) i₀.succ
    rw [buildNode_zero, xorWord_empty_left] at hnode
    rw [hnode]
    ext c
    rw [Finset.mem_image]
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [hanc_col i₀ hcol_ne j] at hj
      rcases hj with rfl | ⟨_, hsub⟩
      · exact hi0_mem
      · exact (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hx, hi0_mem⟩))).2
    · intro hcx
      let j := dir.symm c
      have hj_dir : dir j = c := dir.apply_symm_apply c
      refine ⟨j, ?_, hj_dir⟩
      have hjSx : j ∈ Sx := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hj_dir]⟩
      have hjle : j ≤ i₀ := Finset.le_max' Sx j hjSx
      rw [hanc_col i₀ hcol_ne j]
      rcases eq_or_lt_of_le hjle with hEq | hjlt
      · left; exact hEq
      · right
        refine ⟨hjlt, ?_⟩
        rcases hcol_laminar (dir i₀) (dir j) with hdisj | hij | hji
        · exfalso
          exact Finset.disjoint_left.mp hdisj
            (Finset.mem_filter.mpr ⟨hx, hi0_mem⟩) (Finset.mem_filter.mpr ⟨hx, by rwa [hj_dir]⟩)
        · exact hij
        · have hc_le := hdir_card j i₀ (Nat.le_of_lt hjlt)
          exact (Finset.eq_of_subset_of_card_le hji hc_le).symm ▸ Finset.Subset.refl _

lemma region_extend_to_tree (n : ℕ) (hn : 0 < n) (s : Signing n) :
    ∃ X : Finset (Word n), tree n X ∧ region n s ⊆ X := by
  by_cases hne : (region n s).Nonempty
  · obtain ⟨r, hr⟩ := hne
    have h0 : ∅ ∈ region n (shiftSigning r s) := by
      rw [← xorWord_self r, mem_region_shiftSigning]
      exact hr
    obtain ⟨dir, parent, hp, hsub⟩ := empty_region_extend n hn (shiftSigning r s) h0
    let T0 := Finset.univ.image (buildNode n ∅ dir parent hp)
    have hT0 : tree n T0 := tree_of_buildNode n ∅ dir parent hp
    refine ⟨T0.image (fun x => xorWord x r), tree_shift r hT0, fun x hx => ?_⟩
    rw [Finset.mem_image]
    refine ⟨xorWord x r, hsub ?_, xorWord_invol r x⟩
    rwa [mem_region_shiftSigning]
  · obtain ⟨X, hX⟩ := star_tree_exists n
    exact ⟨X, hX, fun x hx => absurd ⟨x, hx⟩ hne⟩

lemma signing_card_le (n : ℕ) (hn : 0 < n) (s : Signing n) : (region n s).card ≤ n + 1 := by
  obtain ⟨X, hX, hsub⟩ := region_extend_to_tree n hn s
  calc (region n s).card ≤ X.card := Finset.card_le_card hsub
    _ = n + 1 := tree_card_eq hX

theorem tree_iff_largest (n : ℕ) (hn : 0 < n) (X : Finset (Word n)) :
    tree n X ↔ ∃ s ∈ largest n, region n s = X := by
  constructor
  · intro hX
    obtain ⟨s, hsub, _⟩ := tree_signing_unique hX
    have hcard : (region n s).card = n + 1 :=
      le_antisymm (signing_card_le n hn s) ((tree_card_eq hX).symm ▸ Finset.card_le_card hsub)
    refine ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard⟩, ?_⟩
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, tree_card_eq hX])).symm
  · rintro ⟨s, hs, rfl⟩
    have hcard : (region n s).card = n + 1 := (Finset.mem_filter.mp hs).2
    obtain ⟨T, hT, hsub⟩ := region_extend_to_tree n hn s
    have hEq := Finset.eq_of_subset_of_card_le hsub (by rw [tree_card_eq hT, hcard])
    rwa [hEq]

theorem extend_to_largest (n : ℕ) (hn : 0 < n) (s : Signing n) :
    ∃ u ∈ largest n, region n s ⊆ region n u := by
  obtain ⟨X, hX, hsub⟩ := region_extend_to_tree n hn s
  obtain ⟨u, hu, rfl⟩ := (tree_iff_largest n hn X).mp hX
  exact ⟨u, hu, hsub⟩

theorem weighted_cover_largest (n : ℕ) (hn : 0 < n)
    (k : ℕ) (P : Finset (Word n)) (w : Word n → ℕ) (f : Fin k → Signing n) :
    ∃ g : Fin k → Signing n, (∀ i, g i ∈ largest n) ∧
      ((P.filter (fun x => ∃ i, x ∈ region n (f i))).sum w) ≤
      ((P.filter (fun x => ∃ i, x ∈ region n (g i))).sum w) := by
  have hg : ∀ i : Fin k, ∃ u ∈ largest n, region n (f i) ⊆ region n u :=
    fun i => extend_to_largest n hn (f i)
  choose g hgmem hgsub using hg
  refine ⟨g, hgmem, Finset.sum_le_sum_of_subset ?_⟩
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  rcases hx with ⟨hxP, i, hxi⟩
  exact ⟨hxP, i, hgsub i hxi⟩

end Part3_ExtendToTree

section Part4_Counting

open Classical

noncomputable def allTrees (n : ℕ) : Finset (Finset (Word n)) :=
  Finset.univ.filter (fun X => tree n X)

noncomputable def treesAt0 (n : ℕ) : Finset (Finset (Word n)) :=
  (allTrees n).filter (fun X => ∅ ∈ X)

lemma largest_card_eq_allTrees (n : ℕ) (hn : 0 < n) : (largest n).card = (allTrees n).card := by
  apply Finset.card_bij (fun s _ => region n s)
  · intro s hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (tree_iff_largest n hn (region n s)).mpr ⟨s, hs, rfl⟩⟩
  · intro s1 hs1 s2 hs2 heq
    have ht : tree n (region n s1) := (tree_iff_largest n hn (region n s1)).mpr ⟨s1, hs1, rfl⟩
    obtain ⟨s0, _, hhit⟩ := tree_signing_unique ht
    have hs_eq : ∀ s : Signing n, region n s = region n s1 → s = s0 := by
      intro s hseq
      funext e
      by_contra hne
      obtain ⟨x, hxX, hpat⟩ := hhit e (s e) hne
      rw [← hseq] at hxX
      exact (Finset.mem_filter.mp hxX).2 e hpat
    exact (hs_eq s1 rfl).trans (hs_eq s2 heq.symm).symm
  · intro X hX
    obtain ⟨s, hs, rfl⟩ := (tree_iff_largest n hn X).mp (Finset.mem_filter.mp hX).2
    exact ⟨s, hs, rfl⟩

lemma double_count_roots (n : ℕ) :
    (n + 1) * (allTrees n).card = 2 ^ n * (treesAt0 n).card := by
  have hlhs : (n + 1) * (allTrees n).card = ∑ X ∈ allTrees n, ∑ r : Word n, (if r ∈ X then (1 : ℕ) else 0) := by
    calc (n + 1) * (allTrees n).card
        = ∑ _X ∈ allTrees n, (n + 1) := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      _ = ∑ X ∈ allTrees n, X.card := by
          refine Finset.sum_congr rfl fun X hX => ?_
          exact (tree_card_eq (Finset.mem_filter.mp hX).2).symm
      _ = ∑ X ∈ allTrees n, ∑ r : Word n, (if r ∈ X then (1 : ℕ) else 0) := by
          refine Finset.sum_congr rfl fun X _ => ?_
          simp [Finset.sum_boole]
  rw [hlhs, Finset.sum_comm]
  have hrhs : ∀ r : Word n, (∑ X ∈ allTrees n, (if r ∈ X then (1 : ℕ) else 0)) = (treesAt0 n).card := by
    intro r
    rw [← Finset.card_filter (fun X => r ∈ X)]
    apply Finset.card_bij (fun X _ => X.image (fun x => xorWord x r))
    · intro X hX
      obtain ⟨hXa, hrX⟩ := Finset.mem_filter.mp hX
      rw [treesAt0, Finset.mem_filter]
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (tree_shift_iff r X).mpr (Finset.mem_filter.mp hXa).2⟩, ?_⟩
      exact Finset.mem_image.mpr ⟨r, hrX, xorWord_self r⟩
    · intro X1 _ X2 _ hEq
      have h1 : (X1.image (fun x => xorWord x r)).image (fun x => xorWord x r) = X1 := by
        ext w; simp [Finset.mem_image, xorWord_invol]
      have h2 : (X2.image (fun x => xorWord x r)).image (fun x => xorWord x r) = X2 := by
        ext w; simp [Finset.mem_image, xorWord_invol]
      rw [← h1, ← h2, hEq]
    · intro Y hY
      obtain ⟨hYa, h0Y⟩ := Finset.mem_filter.mp hY
      let X := Y.image (fun x => xorWord x r)
      have hX : X ∈ (allTrees n).filter (fun X => r ∈ X) := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (tree_shift_iff r Y).mpr (Finset.mem_filter.mp hYa).2⟩, ?_⟩
        exact Finset.mem_image.mpr ⟨∅, h0Y, xorWord_empty_left r⟩
      refine ⟨X, hX, ?_⟩
      ext w; simp [X, Finset.mem_image, xorWord_invol]
  calc ∑ r : Word n, ∑ X ∈ allTrees n, (if r ∈ X then (1 : ℕ) else 0)
      = ∑ _r : Word n, (treesAt0 n).card := Finset.sum_congr rfl fun r _ => hrhs r
    _ = 2 ^ n * (treesAt0 n).card := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        simp [Word, Site]

-- Rooted forests on Fin (n + 1)
abbrev RF (n : ℕ) := Fin (n + 1) → Option (Fin (n + 1))

def iterOpt {n : ℕ} (p : RF n) : ℕ → Fin (n + 1) → Option (Fin (n + 1))
  | 0, v => some v
  | k + 1, v => (iterOpt p k v).bind p

lemma sb {α β : Type} (x : α) (f : α → Option β) : (some x).bind f = f x := rfl
lemma nb {α β : Type} (f : α → Option β) : (none : Option α).bind f = none := rfl

lemma iterOpt_add {n : ℕ} (p : RF n) (a b : ℕ) (v : Fin (n + 1)) :
    iterOpt p (a + b) v = (iterOpt p b v).bind (iterOpt p a) := by
  induction a with
  | zero =>
    rw [Nat.zero_add]
    cases h : iterOpt p b v <;> rfl
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    change (iterOpt p (a + b) v).bind p = (iterOpt p b v).bind (fun u => (iterOpt p a u).bind p)
    rw [ih]
    cases h : iterOpt p b v <;> rfl

lemma iterOpt_succ_left {n : ℕ} (p : RF n) (k : ℕ) (v : Fin (n + 1)) :
    iterOpt p (k + 1) v = (p v).bind (iterOpt p k) := by
  induction k with
  | zero => cases h : p v <;> simp [iterOpt, h, sb, nb]
  | succ k ih =>
    change (iterOpt p (k + 1) v).bind p = (p v).bind (fun u => (iterOpt p k u).bind p)
    rw [ih]
    cases h : p v <;> rfl

def isAcyclic {n : ℕ} (p : RF n) : Prop :=
  ∀ v : Fin (n + 1), iterOpt p (n + 1) v = none

def roots {n : ℕ} (p : RF n) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun v => p v = none)

def edgeCount {n : ℕ} (p : RF n) : ℕ :=
  (Finset.univ.filter (fun v => (p v).isSome)).card

noncomputable def rootedTree0 (n : ℕ) : Finset (RF n) :=
  Finset.univ.filter (fun p => isAcyclic p ∧ roots p = {0})

lemma iterOpt_ge_none {n : ℕ} (p : RF n) (hp : isAcyclic p) {k : ℕ} (hk : n + 1 ≤ k)
    (v : Fin (n + 1)) : iterOpt p k v = none := by
  have hk' : iterOpt p k v = iterOpt p ((k - (n + 1)) + (n + 1)) v :=
    congrArg (fun m => iterOpt p m v) (by omega)
  rw [hk', iterOpt_add, hp v, nb]

lemma iterOpt_cycle_contra {n : ℕ} (p : RF n) (hp : isAcyclic p) {k : ℕ} (hk : 0 < k)
    (v : Fin (n + 1)) (hcyc : iterOpt p k v = some v) : False := by
  have hmul : ∀ m : ℕ, iterOpt p (m * k) v = some v := by
    intro m
    induction m with
    | zero => simp [iterOpt]
    | succ m ih =>
      rw [show (m + 1) * k = m * k + k by ring, iterOpt_add, hcyc, sb, ih]
  have hne := hmul (n + 1)
  have hnone := iterOpt_ge_none p hp (Nat.le_mul_of_pos_right (n + 1) hk) v
  rw [hne] at hnone
  cases hnone

def isAnc {n : ℕ} (p : RF n) (u v : Fin (n + 1)) : Prop :=
  ∃ k : ℕ, iterOpt p k v = some u

lemma isAnc_refl {n : ℕ} (p : RF n) (v : Fin (n + 1)) : isAnc p v v :=
  ⟨0, rfl⟩

lemma isAnc_trans {n : ℕ} (p : RF n) {a b c : Fin (n + 1)}
    (hab : isAnc p a b) (hbc : isAnc p b c) : isAnc p a c := by
  obtain ⟨k1, hk1⟩ := hab
  obtain ⟨k2, hk2⟩ := hbc
  exact ⟨k1 + k2, by rw [iterOpt_add, hk2, sb, hk1]⟩

lemma isAnc_step {n : ℕ} (p : RF n) {u v w : Fin (n + 1)}
    (hpv : p v = some w) (huw : isAnc p u w) : isAnc p u v := by
  obtain ⟨k, hk⟩ := huw
  exact ⟨k + 1, by rw [iterOpt_succ_left, hpv, sb, hk]⟩

lemma isAnc_antisymm {n : ℕ} (p : RF n) (hp : isAcyclic p) {a b : Fin (n + 1)}
    (hab : isAnc p a b) (hba : isAnc p b a) : a = b := by
  obtain ⟨k1, hk1⟩ := hab
  obtain ⟨k2, hk2⟩ := hba
  have hcyc : iterOpt p (k2 + k1) b = some b := by
    rw [iterOpt_add, hk1, sb, hk2]
  cases hk : k2 + k1 with
  | zero =>
    have hk1z : k1 = 0 := by omega
    subst hk1z
    exact (Option.some.inj hk1).symm
  | succ m =>
    exact False.elim (iterOpt_cycle_contra p hp (by omega) b hcyc)

lemma isAnc_parent_iff {n : ℕ} (p : RF n) {u v w : Fin (n + 1)}
    (hne : u ≠ v) (hpv : p v = some w) : isAnc p u v ↔ isAnc p u w := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => exact absurd (Option.some.inj hk).symm hne
    | succ m =>
      rw [iterOpt_succ_left, hpv, sb] at hk
      exact ⟨m, hk⟩
  · exact isAnc_step p hpv

noncomputable def wordOf {n : ℕ} (p : RF n) (v : Fin (n + 1)) : Word n :=
  Finset.univ.filter (fun c : Site n => isAnc p c.succ v)

noncomputable def wordsOf {n : ℕ} (p : RF n) : Finset (Word n) :=
  Finset.univ.image (wordOf p)

lemma wordOf_zero {n : ℕ} (p : RF n) (hp0 : p 0 = none) : wordOf p 0 = ∅ := by
  ext c
  simp only [wordOf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro ⟨k, hk⟩
  cases k with
  | zero => exact Fin.succ_ne_zero c (Option.some.inj hk).symm
  | succ m => rw [iterOpt_succ_left, hp0, nb] at hk; cases hk

noncomputable def depth {n : ℕ} (p : RF n) (v : Fin (n + 1)) : ℕ :=
  ((Finset.range (n + 1)).filter (fun k => (iterOpt p k v).isSome)).card

lemma depth_step {n : ℕ} (p : RF n) (hp : isAcyclic p) {v w : Fin (n + 1)} (hpv : p v = some w) :
    depth p v = depth p w + 1 := by
  dsimp [depth]
  let S := (Finset.range (n + 1)).filter (fun k => (iterOpt p k w).isSome)
  let T := (Finset.range (n + 1)).filter (fun k => (iterOpt p k v).isSome)
  change T.card = S.card + 1
  have hT : T = insert 0 (S.image Nat.succ) := by
    ext k
    simp only [T, S, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    cases k with
    | zero =>
      simp [iterOpt]
    | succ m =>
      constructor
      · rintro ⟨hm, hsome⟩
        right
        refine ⟨m, ⟨?_, ?_⟩, rfl⟩
        · by_contra hge
          have hm' : m = n := by omega
          subst hm'
          have hn1 := hp v
          rw [iterOpt_succ_left, hpv, sb] at hn1
          rw [iterOpt_succ_left, hpv, sb, hn1] at hsome
          simp at hsome
        · rwa [iterOpt_succ_left, hpv, sb] at hsome
      · rintro (h0 | ⟨a, ⟨ha, hsome⟩, hEq⟩)
        · omega
        · have ham : a = m := Nat.succ_inj.mp hEq
          subst ham
          have han : a < n := by
            by_contra hge
            have ha' : a = n := by omega
            subst ha'
            have hn1 := hp v
            rw [iterOpt_succ_left, hpv, sb] at hn1
            rw [hn1] at hsome
            simp at hsome
          refine ⟨by omega, ?_⟩
          rwa [iterOpt_succ_left, hpv, sb]
  rw [hT, Finset.card_insert_of_notMem (by simp), Finset.card_image_of_injective _ Nat.succ_injective]

lemma wordOf_step {n : ℕ} (p : RF n) (hp : isAcyclic p) {c : Site n} {w : Fin (n + 1)}
    (hpc : p c.succ = some w) :
    wordOf p c.succ = insert c (wordOf p w) ∧ c ∉ wordOf p w := by
  have hnot : c ∉ wordOf p w := by
    intro hmem
    have hanc := (Finset.mem_filter.mp hmem).2
    obtain ⟨k, hk⟩ := hanc
    exact iterOpt_cycle_contra p hp (Nat.succ_pos k) c.succ
      (by rw [iterOpt_succ_left, hpc, sb, hk])
  refine ⟨?_, hnot⟩
  ext d
  simp only [wordOf, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hdc : d = c
  · subst hdc
    simp [isAnc_refl p]
  · have hne : d.succ ≠ c.succ := fun h => hdc (Fin.succ_inj.mp h)
    rw [isAnc_parent_iff p hne hpc]
    simp [hdc]

lemma wordOf_inj_root0 {n : ℕ} {p : RF n} (hp : p ∈ rootedTree0 n) :
    Function.Injective (wordOf p) := by
  have hac : isAcyclic p := (Finset.mem_filter.mp hp).2.1
  have hrt : roots p = {0} := (Finset.mem_filter.mp hp).2.2
  have hp0_mem : (0 : Fin (n + 1)) ∈ roots p := by rw [hrt]; exact Finset.mem_singleton_self 0
  have hp0 : p 0 = none := (Finset.mem_filter.mp hp0_mem).2
  intro u v huv
  rcases Fin.eq_zero_or_eq_succ u with rfl | ⟨c, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ v with rfl | ⟨d, rfl⟩
    · rfl
    · have hd : d ∈ wordOf p d.succ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, isAnc_refl p _⟩
      rw [← huv, wordOf_zero p hp0] at hd
      simp at hd
  · rcases Fin.eq_zero_or_eq_succ v with rfl | ⟨d, rfl⟩
    · have hc : c ∈ wordOf p c.succ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, isAnc_refl p _⟩
      rw [huv, wordOf_zero p hp0] at hc
      simp at hc
    · have hc : c ∈ wordOf p d.succ := by
        rw [← huv]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, isAnc_refl p _⟩
      have hd : d ∈ wordOf p c.succ := by
        rw [huv]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, isAnc_refl p _⟩
      exact isAnc_antisymm p hac (Finset.mem_filter.mp hc).2 (Finset.mem_filter.mp hd).2

def minWord {n : ℕ} (X : Finset (Word n)) (c : Site n) : Word n :=
  Finset.univ.filter (fun d : Site n => ∀ x ∈ X, c ∈ x → d ∈ x)

lemma minWord_wordsOf {n : ℕ} {p : RF n} (hp : p ∈ rootedTree0 n) (c : Site n) :
    minWord (wordsOf p) c = wordOf p c.succ := by
  have hac : isAcyclic p := (Finset.mem_filter.mp hp).2.1
  ext d
  simp only [minWord, wordsOf, wordOf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h
    exact (Finset.mem_filter.mp (h (wordOf p c.succ) ⟨c.succ, rfl⟩
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, isAnc_refl p _⟩))).2
  · rintro hd x ⟨v, rfl⟩ hv
    have hc : isAnc p c.succ v := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, isAnc_trans p hd hc⟩

lemma wordsOf_mem_treesAt0 {n : ℕ} {p : RF n} (hp : p ∈ rootedTree0 n) :
    wordsOf p ∈ treesAt0 n := by
  have hac : isAcyclic p := (Finset.mem_filter.mp hp).2.1
  have hrt : roots p = {0} := (Finset.mem_filter.mp hp).2.2
  have hp0 : p 0 = none := by
    have h0 : (0 : Fin (n + 1)) ∈ roots p := by rw [hrt]; exact Finset.mem_singleton_self 0
    exact (Finset.mem_filter.mp h0).2
  have hpsucc : ∀ c : Site n, ∃ w : Fin (n + 1), p c.succ = some w := by
    intro c
    cases h : p c.succ with
    | some w => exact ⟨w, rfl⟩
    | none =>
      exfalso
      have hmem : c.succ ∈ roots p := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      rw [hrt, Finset.mem_singleton] at hmem
      exact Fin.succ_ne_zero c hmem
  obtain ⟨dir, hdir_le⟩ := permSortByKey n (fun c => depth p c.succ)
  let parent2 : Site n → Fin (n + 1) := fun i =>
    match p (dir i).succ with
    | none => 0
    | some w => if h0 : w = 0 then 0 else (dir.symm ⟨w.val - 1, by omega⟩).succ
  have hpar2_spec : ∀ i : Site n,
      (p (dir i).succ = some 0 ∧ parent2 i = 0) ∨
      (∃ j : Site n, p (dir i).succ = some j.succ ∧ parent2 i = (dir.symm j).succ) := by
    intro i
    obtain ⟨w, hw⟩ := hpsucc (dir i)
    rcases Fin.eq_zero_or_eq_succ w with rfl | ⟨j, rfl⟩
    · left; refine ⟨hw, ?_⟩; dsimp [parent2]; rw [hw]; simp
    · right; refine ⟨j, hw, ?_⟩; dsimp [parent2]; rw [hw]; simp [Fin.succ_ne_zero]
  have hp_le : ∀ i : Site n, (parent2 i).val ≤ i.val := by
    intro i
    rcases hpar2_spec i with ⟨_, hEq⟩ | ⟨j, hw, hEq⟩
    · rw [hEq]; exact Nat.zero_le _
    · rw [hEq, Fin.val_succ]
      have hdep := depth_step p hac hw
      have hle : (dir.symm j).val < i.val := by
        by_contra hge
        have hil := hdir_le i (dir.symm j) (by omega)
        simp only [Equiv.apply_symm_apply] at hil
        omega
      exact hle
  let node := buildNode n ∅ dir parent2 hp_le
  have hnode_eq : ∀ k : Fin (n + 1),
      node k = Fin.cases (wordOf p 0) (fun i => wordOf p (dir i).succ) k := by
    intro k
    rcases k with ⟨kv, hkv⟩
    induction kv using Nat.strong_induction_on with
    | ind kv ih =>
      cases kv with
      | zero =>
        change buildNode n ∅ dir parent2 hp_le 0 = Fin.cases (wordOf p 0) (fun i => wordOf p (dir i).succ) 0
        rw [buildNode_zero, wordOf_zero p hp0, Fin.cases_zero]
      | succ m =>
        have hm : m < n := by omega
        let i : Site n := ⟨m, hm⟩
        change buildNode n ∅ dir parent2 hp_le i.succ =
          Fin.cases (wordOf p 0) (fun i => wordOf p (dir i).succ) i.succ
        rw [buildNode_step, Fin.cases_succ]
        rcases hpar2_spec i with ⟨hw0, hpEq⟩ | ⟨j, hwj, hpEq⟩
        · have ih0 := ih 0 (Nat.succ_pos m) (Nat.zero_lt_succ n)
          have hn0 : buildNode n ∅ dir parent2 hp_le (parent2 i) = wordOf p 0 := by
            rw [hpEq]
            simpa using ih0
          rw [hn0]
          obtain ⟨hins, hnot⟩ := wordOf_step p hac hw0
          rw [hins, if_neg hnot]
        · let prevI := dir.symm j
          have hlt := hp_le i
          rw [hpEq, Fin.val_succ] at hlt
          have ihj := ih prevI.succ.val (Nat.succ_lt_succ hlt) prevI.succ.isLt
          have hpar_node : buildNode n ∅ dir parent2 hp_le (parent2 i) = wordOf p j.succ := by
            rw [hpEq]
            change buildNode n ∅ dir parent2 hp_le prevI.succ = _ at ihj
            simpa [prevI] using ihj
          rw [hpar_node]
          obtain ⟨hins, hnot⟩ := wordOf_step p hac hwj
          rw [hins, if_neg hnot]
  have himage : wordsOf p = Finset.univ.image node := by
    ext x
    simp only [wordsOf, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, rfl⟩
      rcases Fin.eq_zero_or_eq_succ v with rfl | ⟨c, rfl⟩
      · exact ⟨0, by simpa using (hnode_eq 0)⟩
      · refine ⟨(dir.symm c).succ, ?_⟩
        have h1 := hnode_eq (dir.symm c).succ
        have hdir : dir (dir.symm c) = c := dir.apply_symm_apply c
        simpa [hdir] using h1
    · rintro ⟨k, rfl⟩
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
      · exact ⟨0, by simpa using (hnode_eq 0).symm⟩
      · exact ⟨(dir i).succ, by simpa using (hnode_eq i.succ).symm⟩
  rw [treesAt0, Finset.mem_filter]
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, himage ▸ tree_of_buildNode n ∅ dir parent2 hp_le⟩, ?_⟩
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, wordOf_zero p hp0⟩

lemma rootedTree0_card_eq_treesAt0 (n : ℕ) (hn : 0 < n) :
    (rootedTree0 n).card = (treesAt0 n).card := by
  apply Finset.card_bij (fun p _ => wordsOf p)
  · intro p hp; exact wordsOf_mem_treesAt0 hp
  · intro p1 hp1 p2 hp2 hEq
    have hp1_rt : roots p1 = {0} := (Finset.mem_filter.mp hp1).2.2
    have hp2_rt : roots p2 = {0} := (Finset.mem_filter.mp hp2).2.2
    have hp1_ac : isAcyclic p1 := (Finset.mem_filter.mp hp1).2.1
    have hp2_ac : isAcyclic p2 := (Finset.mem_filter.mp hp2).2.1
    have hm1 : (0 : Fin (n + 1)) ∈ roots p1 := by rw [hp1_rt]; exact Finset.mem_singleton_self 0
    have hm2 : (0 : Fin (n + 1)) ∈ roots p2 := by rw [hp2_rt]; exact Finset.mem_singleton_self 0
    have h0_1 : p1 0 = none := (Finset.mem_filter.mp hm1).2
    have h0_2 : p2 0 = none := (Finset.mem_filter.mp hm2).2
    funext v
    rcases Fin.eq_zero_or_eq_succ v with rfl | ⟨c, rfl⟩
    · rw [h0_1, h0_2]
    · have hmin : wordOf p1 c.succ = wordOf p2 c.succ := by
        rw [← minWord_wordsOf hp1 c, ← minWord_wordsOf hp2 c, hEq]
      have hsucc : ∀ (q : RF n), q ∈ rootedTree0 n → ∀ a : Site n, ∃ w, q a.succ = some w := by
        intro q hq a
        cases hq_a : q a.succ with
        | some w => exact ⟨w, rfl⟩
        | none =>
          exfalso
          have hmem : a.succ ∈ roots q := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq_a⟩
          rw [(Finset.mem_filter.mp hq).2.2, Finset.mem_singleton] at hmem
          exact Fin.succ_ne_zero a hmem
      obtain ⟨w1, hw1⟩ := hsucc p1 hp1 c
      obtain ⟨w2, hw2⟩ := hsucc p2 hp2 c
      have hw1_er : (wordOf p1 c.succ).erase c = wordOf p1 w1 := by
        obtain ⟨hins, hnot⟩ := wordOf_step p1 hp1_ac hw1
        rw [hins, Finset.erase_insert hnot]
      have hw2_er : (wordOf p2 c.succ).erase c = wordOf p2 w2 := by
        obtain ⟨hins, hnot⟩ := wordOf_step p2 hp2_ac hw2
        rw [hins, Finset.erase_insert hnot]
      have hweq : wordOf p1 w1 = wordOf p2 w2 := by rw [← hw1_er, ← hw2_er, hmin]
      have w1_eq_w2 : w1 = w2 := by
        rcases Fin.eq_zero_or_eq_succ w1 with rfl | ⟨d1, rfl⟩
        · rcases Fin.eq_zero_or_eq_succ w2 with rfl | ⟨d2, rfl⟩
          · rfl
          · exfalso
            have hd2 : d2 ∈ wordOf p2 d2.succ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, isAnc_refl p2 _⟩
            rw [← hweq, wordOf_zero p1 h0_1] at hd2; simp at hd2
        · rcases Fin.eq_zero_or_eq_succ w2 with rfl | ⟨d2, rfl⟩
          · exfalso
            have hd1 : d1 ∈ wordOf p1 d1.succ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, isAnc_refl p1 _⟩
            rw [hweq, wordOf_zero p2 h0_2] at hd1; simp at hd1
          · have hmin_d : wordOf p1 d1.succ = wordOf p2 d1.succ := by
              rw [← minWord_wordsOf hp1 d1, ← minWord_wordsOf hp2 d1, hEq]
            rw [hmin_d] at hweq
            exact congrArg Fin.succ (Fin.succ_inj.mp (wordOf_inj_root0 hp2 hweq))
      rw [hw1, hw2, w1_eq_w2]
  · intro X hX
    obtain ⟨hXa, h0X⟩ := Finset.mem_filter.mp hX
    have htreeX := (Finset.mem_filter.mp hXa).2
    obtain ⟨s, hs, hreg⟩ := (tree_iff_largest n hn X).mp htreeX
    have h0reg : ∅ ∈ region n s := hreg ▸ h0X
    obtain ⟨dir, parent, hp, hsub⟩ := empty_region_extend n hn s h0reg
    let node := buildNode n ∅ dir parent hp
    have hX_eq : X = Finset.univ.image node := by
      have hT := tree_of_buildNode n ∅ dir parent hp
      have hcardX : X.card = n + 1 := tree_card_eq htreeX
      have hcardT : (Finset.univ.image node).card = n + 1 := tree_card_eq hT
      exact Finset.eq_of_subset_of_card_le (hreg ▸ hsub) (by rw [hcardT, hcardX])
    let p2 : RF n := Fin.cases none (fun c =>
      Fin.cases (some 0) (fun j => some (dir j).succ) (parent (dir.symm c)))
    have hp2_0 : p2 0 = none := by simp [p2]
    have hp2_succ : ∀ i : Site n,
        (parent i = 0 ∧ p2 (dir i).succ = some 0) ∨
        (∃ j : Site n, parent i = j.succ ∧ p2 (dir i).succ = some (dir j).succ) := by
      intro i
      dsimp [p2]
      simp only [Fin.cases_succ, Equiv.symm_apply_apply]
      rcases Fin.eq_zero_or_eq_succ (parent i) with h0 | ⟨j, hj⟩
      · left; refine ⟨h0, ?_⟩; rw [h0]; simp
      · right; refine ⟨j, hj, ?_⟩; rw [hj]; simp
    let rank : Fin (n + 1) → ℕ := Fin.cases 0 (fun c => (dir.symm c).val + 1)
    have hrank_dec : ∀ u v : Fin (n + 1), p2 u = some v → rank v < rank u := by
      intro u v huv
      rcases Fin.eq_zero_or_eq_succ u with rfl | ⟨c, rfl⟩
      · rw [hp2_0] at huv; simp at huv
      · let i := dir.symm c
        have hic : dir i = c := dir.apply_symm_apply c
        rw [← hic] at huv ⊢
        rcases hp2_succ i with ⟨_, hw0⟩ | ⟨j, hpj, hwj⟩
        · rw [hw0] at huv; injection huv with hv; subst hv
          dsimp [rank]; simp
        · rw [hwj] at huv; injection huv with hv; subst hv
          dsimp [rank]
          simp only [Fin.cases_succ, Equiv.symm_apply_apply]
          have := hp i; rw [hpj, Fin.val_succ] at this
          omega
    have hiter_rank : ∀ (k : ℕ) (u v : Fin (n + 1)), iterOpt p2 k u = some v → rank v + k ≤ rank u := by
      intro k
      induction k with
      | zero => intro u v h; simp [iterOpt] at h; subst h; simp
      | succ m ih =>
        intro u v h
        rw [iterOpt_succ_left] at h
        cases hu : p2 u with
        | none => rw [hu] at h; simp at h
        | some w =>
          rw [hu, sb] at h
          have hm := ih w v h
          have hlt := hrank_dec u w hu
          omega
    have hp2_ac : isAcyclic p2 := by
      intro v
      cases h : iterOpt p2 (n + 1) v with
      | none => rfl
      | some w =>
        exfalso
        have hle := hiter_rank (n + 1) v w h
        have hrank_le : rank v ≤ n := by
          rcases Fin.eq_zero_or_eq_succ v with rfl | ⟨c, rfl⟩
          · simp [rank]
          · dsimp [rank]; simp
        omega
    have hp2_roots : roots p2 = {0} := by
      ext v
      simp only [roots, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rcases Fin.eq_zero_or_eq_succ v with rfl | ⟨c, rfl⟩
      · simp [hp2_0]
      · constructor
        · intro hv
          exfalso
          let i := dir.symm c
          have hic : dir i = c := dir.apply_symm_apply c
          rw [← hic] at hv
          rcases hp2_succ i with ⟨_, hw0⟩ | ⟨_, _, hwj⟩ <;> rw [hv] at * <;> simp_all
        · intro h; exact False.elim (Fin.succ_ne_zero c h)
    have hp2_mem : p2 ∈ rootedTree0 n := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp2_ac, hp2_roots⟩
    have hword_node : ∀ k : Fin (n + 1),
        Fin.cases (wordOf p2 0) (fun i => wordOf p2 (dir i).succ) k = node k := by
      intro k
      rcases k with ⟨kv, hkv⟩
      induction kv using Nat.strong_induction_on with
      | ind kv ih =>
        cases kv with
        | zero =>
          change Fin.cases (wordOf p2 0) (fun i => wordOf p2 (dir i).succ) 0 =
            buildNode n ∅ dir parent hp 0
          rw [Fin.cases_zero, wordOf_zero p2 hp2_0, buildNode_zero]
        | succ m =>
          have hm : m < n := by omega
          let i : Site n := ⟨m, hm⟩
          change Fin.cases (wordOf p2 0) (fun i => wordOf p2 (dir i).succ) i.succ =
            buildNode n ∅ dir parent hp i.succ
          rw [Fin.cases_succ, buildNode_step]
          rcases hp2_succ i with ⟨hp0, hw0⟩ | ⟨j, hpj, hwj⟩
          · obtain ⟨hins, hnot⟩ := wordOf_step p2 hp2_ac hw0
            have ih0 := ih 0 (Nat.succ_pos m) (Nat.zero_lt_succ n)
            have hn0 : buildNode n ∅ dir parent hp (parent i) = wordOf p2 0 := by
              rw [hp0]; simpa using ih0.symm
            rw [hins, hn0, if_neg hnot]
          · obtain ⟨hins, hnot⟩ := wordOf_step p2 hp2_ac hwj
            have hlt : j.val < i.val := by
              have := hp i; rw [hpj, Fin.val_succ] at this; exact this
            have ihj := ih j.succ.val (Nat.succ_lt_succ hlt) j.succ.isLt
            have hnj : buildNode n ∅ dir parent hp (parent i) = wordOf p2 (dir j).succ := by
              rw [hpj]
              change Fin.cases (wordOf p2 0) (fun i => wordOf p2 (dir i).succ) j.succ =
                buildNode n ∅ dir parent hp j.succ at ihj
              simpa using ihj.symm
            rw [hins, hnj, if_neg hnot]
    refine ⟨p2, hp2_mem, ?_⟩
    rw [hX_eq]
    ext x
    simp only [wordsOf, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, rfl⟩
      rcases Fin.eq_zero_or_eq_succ v with rfl | ⟨c, rfl⟩
      · exact ⟨0, by simpa using (hword_node 0).symm⟩
      · refine ⟨(dir.symm c).succ, ?_⟩
        have h1 := hword_node (dir.symm c).succ
        have hdir : dir (dir.symm c) = c := dir.apply_symm_apply c
        simpa [hdir] using h1.symm
    · rintro ⟨k, rfl⟩
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
      · exact ⟨0, by simpa using hword_node 0⟩
      · exact ⟨(dir i).succ, by simpa using hword_node i.succ⟩

-- Step 4.4: Pitman double counting for RF n!
noncomputable def RF_k (n k : ℕ) : Finset (RF n) :=
  Finset.univ.filter (fun p => isAcyclic p ∧ edgeCount p = k)

lemma roots_add_edgeCount {n : ℕ} (p : RF n) : (roots p).card + edgeCount p = n + 1 := by
  dsimp [roots, edgeCount]
  have hdisj : Disjoint (Finset.univ.filter fun v => p v = none) (Finset.univ.filter fun v => (p v).isSome) := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    have e1 := (Finset.mem_filter.mp h1).2
    have e2 := (Finset.mem_filter.mp h2).2
    rw [e1] at e2; simp at e2
  have hun : (Finset.univ.filter fun v => p v = none) ∪ (Finset.univ.filter fun v => (p v).isSome) = Finset.univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    cases p v <;> simp
  rw [← Finset.card_union_of_disjoint hdisj, hun, Finset.card_fin]

lemma roots_eq_one_iff_edgeCount_eq_n {n : ℕ} (p : RF n) :
    (roots p).card = 1 ↔ edgeCount p = n := by
  have := roots_add_edgeCount p
  omega

def swapRF {n : ℕ} (a b : Fin (n + 1)) (p : RF n) : RF n :=
  fun v => (p (Equiv.swap a b v)).map (Equiv.swap a b)

lemma iterOpt_swapRF {n : ℕ} (a b : Fin (n + 1)) (p : RF n) (k : ℕ) (v : Fin (n + 1)) :
    iterOpt (swapRF a b p) k (Equiv.swap a b v) = (iterOpt p k v).map (Equiv.swap a b) := by
  induction k with
  | zero => simp [iterOpt]
  | succ k ih =>
    rw [iterOpt, ih, iterOpt]
    cases h : iterOpt p k v <;> simp [swapRF, Equiv.swap_apply_self]

lemma swapRF_invol {n : ℕ} (a b : Fin (n + 1)) (p : RF n) :
    swapRF a b (swapRF a b p) = p := by
  funext v
  dsimp [swapRF]
  rw [Equiv.swap_apply_self]
  cases p v <;> simp

lemma swapRF_acyclic {n : ℕ} (a b : Fin (n + 1)) (p : RF n) :
    isAcyclic (swapRF a b p) ↔ isAcyclic p := by
  constructor
  · intro h v
    have hv := h (Equiv.swap a b v)
    rw [iterOpt_swapRF] at hv
    cases h1 : iterOpt p (n + 1) v with
    | none => rfl
    | some w => rw [h1] at hv; simp at hv
  · intro h v
    have hv := h (Equiv.swap a b v)
    have heq := iterOpt_swapRF a b p (n + 1) (Equiv.swap a b v)
    rw [Equiv.swap_apply_self] at heq
    rw [heq, hv, Option.map_none]

lemma swapRF_roots {n : ℕ} (a b : Fin (n + 1)) (p : RF n) :
    roots (swapRF a b p) = (roots p).image (Equiv.swap a b) := by
  ext v
  simp only [roots, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hv
    refine ⟨Equiv.swap a b v, ?_, Equiv.swap_apply_self _ _ _⟩
    dsimp [swapRF] at hv
    cases h : p (Equiv.swap a b v) <;> simp [h] at hv ⊢
  · rintro ⟨w, hw, rfl⟩
    dsimp [swapRF]
    rw [Equiv.swap_apply_self, hw]; rfl

lemma RF_n_card_eq (n : ℕ) : (RF_k n n).card = (n + 1) * (rootedTree0 n).card := by
  let S := (Finset.univ : Finset (Fin (n + 1))).sigma (fun _ => rootedTree0 n)
  have hScard : S.card = (n + 1) * (rootedTree0 n).card := by
    simp [S]
  rw [← hScard]
  symm
  apply Finset.card_bij (fun rp _ => swapRF 0 rp.1 rp.2)
  · rintro ⟨r, p⟩ hrp
    have hp := (Finset.mem_sigma.mp hrp).2
    have hac := (Finset.mem_filter.mp hp).2.1
    have hrt := (Finset.mem_filter.mp hp).2.2
    rw [RF_k, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, (swapRF_acyclic 0 r p).mpr hac, ?_⟩
    rw [← roots_eq_one_iff_edgeCount_eq_n, swapRF_roots, Finset.card_image_of_injective _ (Equiv.injective _), hrt]
    simp
  · rintro ⟨r1, p1⟩ h1 ⟨r2, p2⟩ h2 hEq
    have hrt1 := (Finset.mem_filter.mp (Finset.mem_sigma.mp h1).2).2.2
    have hrt2 := (Finset.mem_filter.mp (Finset.mem_sigma.mp h2).2).2.2
    have hr12 : roots (swapRF 0 r1 p1) = roots (swapRF 0 r2 p2) := congrArg roots hEq
    rw [swapRF_roots, hrt1, Finset.image_singleton, swapRF_roots, hrt2, Finset.image_singleton,
      Finset.singleton_inj, Equiv.swap_apply_left, Equiv.swap_apply_left] at hr12
    subst hr12
    have hp12 := congrArg (swapRF 0 r1) hEq
    rw [swapRF_invol, swapRF_invol] at hp12
    subst hp12
    rfl
  · intro q hq
    have hac := (Finset.mem_filter.mp hq).2.1
    have hcnt := (Finset.mem_filter.mp hq).2.2
    have hrc : (roots q).card = 1 := (roots_eq_one_iff_edgeCount_eq_n q).mpr hcnt
    obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hrc
    refine ⟨⟨r, swapRF 0 r q⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (swapRF_acyclic 0 r q).mpr hac, ?_⟩⟩, swapRF_invol 0 r q⟩
    rw [swapRF_roots, hr, Finset.image_singleton, Equiv.swap_apply_right]

def rootStep {n : ℕ} (p : RF n) : ℕ → Fin (n + 1) → Fin (n + 1)
  | 0, v => v
  | k + 1, v => match p v with | none => v | some w => rootStep p k w

def rootOf {n : ℕ} (p : RF n) (v : Fin (n + 1)) : Fin (n + 1) :=
  rootStep p (n + 1) v

lemma rootStep_spec {n : ℕ} (p : RF n) (k : ℕ) (v : Fin (n + 1)) (h : iterOpt p (k + 1) v = none) :
    p (rootStep p k v) = none ∧ ∃ d ≤ k, iterOpt p d v = some (rootStep p k v) := by
  induction k generalizing v with
  | zero =>
    rw [iterOpt_succ_left] at h
    cases hpv : p v with
    | none => exact ⟨hpv, 0, le_rfl, rfl⟩
    | some w => rw [hpv] at h; simp [iterOpt] at h
  | succ m ih =>
    rw [rootStep]
    cases hpv : p v with
    | none => exact ⟨hpv, 0, Nat.zero_le _, rfl⟩
    | some w =>
      rw [iterOpt_succ_left, hpv, sb] at h
      obtain ⟨hr, d, hd, hiter⟩ := ih w h
      refine ⟨hr, d + 1, Nat.succ_le_succ hd, ?_⟩
      rwa [iterOpt_succ_left, hpv, sb]

lemma rootOf_spec {n : ℕ} (p : RF n) (hp : isAcyclic p) (v : Fin (n + 1)) :
    rootOf p v ∈ roots p ∧ ∃ d ≤ n + 1, iterOpt p d v = some (rootOf p v) := by
  have h1 := iterOpt_ge_none p hp (Nat.le_succ (n + 1)) v
  obtain ⟨hr, d, hd, hi⟩ := rootStep_spec p (n + 1) v h1
  exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩, d, hd, hi⟩

lemma rootOf_eq_of_iterOpt {n : ℕ} (p : RF n) (hp : isAcyclic p) {k : ℕ} {v u : Fin (n + 1)}
    (hk : iterOpt p k v = some u) : rootOf p v = rootOf p u := by
  obtain ⟨_, d1, _, h1⟩ := rootOf_spec p hp v
  obtain ⟨_, d2, _, h2⟩ := rootOf_spec p hp u
  have hr1 : p (rootOf p v) = none := (Finset.mem_filter.mp (rootOf_spec p hp v).1).2
  have hr2 : p (rootOf p u) = none := (Finset.mem_filter.mp (rootOf_spec p hp u).1).2
  have h1' : iterOpt p (d2 + k) v = some (rootOf p u) := by
    rw [iterOpt_add, hk, sb, h2]
  have same_terminal : ∀ {a b : Fin (n + 1)} {r1 r2 : ℕ}, p a = none → p b = none →
      iterOpt p r1 v = some a → iterOpt p r2 v = some b → a = b := by
    intro a b r1 r2 ha hb ha_it hb_it
    rcases le_total r1 r2 with hle | hle
    · have hadd : iterOpt p r2 v = iterOpt p ((r2 - r1) + r1) v :=
        congrArg (fun m => iterOpt p m v) (by omega)
      rw [hadd, iterOpt_add, ha_it, sb] at hb_it
      cases hm : r2 - r1 with
      | zero => rw [hm, iterOpt] at hb_it; exact Option.some.inj hb_it
      | succ t => rw [hm, iterOpt_succ_left, ha, nb] at hb_it; cases hb_it
    · have hadd : iterOpt p r1 v = iterOpt p ((r1 - r2) + r2) v :=
        congrArg (fun m => iterOpt p m v) (by omega)
      rw [hadd, iterOpt_add, hb_it, sb] at ha_it
      cases hm : r1 - r2 with
      | zero => rw [hm, iterOpt] at ha_it; exact (Option.some.inj ha_it).symm
      | succ t => rw [hm, iterOpt_succ_left, hb, nb] at ha_it; cases ha_it
  exact same_terminal hr1 hr2 h1 h1'

def addEdge {n : ℕ} (q : RF n) (r v : Fin (n + 1)) : RF n :=
  fun u => if u = r then some v else q u

def eraseEdge {n : ℕ} (p : RF n) (r : Fin (n + 1)) : RF n :=
  fun u => if u = r then none else p u

lemma addEdge_acyclic {n : ℕ} {q : RF n} (hq : isAcyclic q) {r v : Fin (n + 1)}
    (hqr : q r = none) (hrv : r ≠ rootOf q v) : isAcyclic (addEdge q r v) := by
  intro x
  let p := addEdge q r v
  by_contra hne
  let f : Fin (n + 2) → Fin (n + 1) := fun t => (iterOpt p t.val x).get (by
    cases ht : iterOpt p t.val x with
    | some _ => rfl
    | none =>
      exfalso
      apply hne
      have hge : iterOpt p (n + 1) x = iterOpt p ((n + 1 - t.val) + t.val) x :=
        congrArg (fun m => iterOpt p m x) (by have := t.isLt; omega)
      rw [hge, iterOpt_add, ht, nb])
  obtain ⟨t1, t2, hne_t, heq_f⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have hlt : t1.val < t2.val ∨ t2.val < t1.val := by
    have : t1.val ≠ t2.val := fun h => hne_t (Fin.ext h)
    omega
  have hswap : ∀ a b : Fin (n + 2), a.val < b.val → f a = f b → False := by
    intro a b hab hfab
    have ht1_some : ∃ u, iterOpt p a.val x = some u := by
      cases ht : iterOpt p a.val x with
      | some u => exact ⟨u, rfl⟩
      | none =>
        exfalso; apply hne
        have hge : iterOpt p (n + 1) x = iterOpt p ((n + 1 - a.val) + a.val) x :=
          congrArg (fun m => iterOpt p m x) (by have := a.isLt; omega)
        rw [hge, iterOpt_add, ht, nb]
    obtain ⟨u, hu⟩ := ht1_some
    have hu_eq : f a = u := by simp [f, hu]
    have ht2_some : iterOpt p b.val x = some u := by
      cases ht : iterOpt p b.val x with
      | some w =>
        have hw : f b = w := by simp [f, ht]
        rw [← hu_eq, hfab, hw]
      | none =>
        exfalso; apply hne
        have hge : iterOpt p (n + 1) x = iterOpt p ((n + 1 - b.val) + b.val) x :=
          congrArg (fun m => iterOpt p m x) (by have := b.isLt; omega)
        rw [hge, iterOpt_add, ht, nb]
    let d := b.val - a.val
    have hd_pos : 0 < d := by omega
    have hcyc : iterOpt p d u = some u := by
      have hsum : iterOpt p b.val x = iterOpt p (d + a.val) x :=
        congrArg (fun m => iterOpt p m x) (by omega)
      rw [hsum, iterOpt_add, hu, sb] at ht2_some
      exact ht2_some
    by_cases hr_hit : ∃ t < d, iterOpt p t u = some r
    · obtain ⟨t0, ht0, htr⟩ := hr_hit
      have hcyc_r : iterOpt p d r = some r := by
        have hs1 : iterOpt p d u = iterOpt p ((d - t0) + t0) u :=
          congrArg (fun m => iterOpt p m u) (by omega)
        have h1 := hcyc
        rw [hs1, iterOpt_add, htr, sb] at h1
        have hs2 : iterOpt p d r = iterOpt p (t0 + (d - t0)) r :=
          congrArg (fun m => iterOpt p m r) (by omega)
        rw [hs2, iterOpt_add, h1, sb, htr]
      let S_r := (Finset.range d).filter (fun j => iterOpt p j r = some r)
      have hS_ne : S_r.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hd_pos, by simp [iterOpt]⟩⟩
      set j0 := S_r.max' hS_ne
      have hj0_mem := Finset.mem_filter.mp (S_r.max'_mem hS_ne)
      have hj0_lt : j0 < d := Finset.mem_range.mp hj0_mem.1
      have hj0_eq : iterOpt p j0 r = some r := hj0_mem.2
      let rem := d - j0
      have hrem_pos : 0 < rem := by omega
      have hcyc_rem : iterOpt p rem r = some r := by
        have hs := congrArg (fun m => iterOpt p m r) (show d = rem + j0 by omega)
        have hcr := hcyc_r
        rw [hs, iterOpt_add, hj0_eq, sb] at hcr
        exact hcr
      have hno_mid : ∀ m, 1 ≤ m → m < rem → iterOpt p m r ≠ some r := by
        intro m hm1 hm2 hmeq
        have hj_big : j0 + m < d := by omega
        have hmem : j0 + m ∈ S_r := by
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨hj_big, ?_⟩
          rw [show j0 + m = m + j0 by omega, iterOpt_add, hj0_eq, sb, hmeq]
        have := Finset.le_max' S_r (j0 + m) hmem
        omega
      have hpr : p r = some v := by dsimp [p, addEdge]; simp
      have hq_walk : ∀ m ≤ rem - 1, ∀ w, iterOpt p (m + 1) r = some w → iterOpt q m v = some w := by
        intro m
        induction m with
        | zero =>
          intro _ w hw
          rw [iterOpt_succ_left, hpr, sb] at hw
          simpa [iterOpt] using hw
        | succ m ihm =>
          intro hm w hw
          cases hm_prev : iterOpt p (m + 1) r with
          | none => rw [iterOpt, hm_prev, nb] at hw; cases hw
          | some u0 =>
            have hu0_ne_r : u0 ≠ r := fun h => hno_mid (m + 1) (by omega) (by omega) (h ▸ hm_prev)
            have hq_step : p u0 = q u0 := by dsimp [p, addEdge]; simp [hu0_ne_r]
            rw [iterOpt, hm_prev, sb, hq_step] at hw
            rw [iterOpt, ihm (by omega) u0 hm_prev, sb, hw]
      have hq_final : iterOpt q (rem - 1) v = some r := by
        apply hq_walk (rem - 1) le_rfl r
        have hs := congrArg (fun m => iterOpt p m r) (show rem - 1 + 1 = rem by omega)
        rw [hs]; exact hcyc_rem
      have hr_root := rootOf_eq_of_iterOpt q hq hq_final
      have hr_self : rootOf q r = r := by
        have := rootOf_spec q hq r
        rcases this.2 with ⟨k0, _, hk0⟩
        cases k0 with
        | zero => exact (Option.some.inj hk0).symm
        | succ t => rw [iterOpt_succ_left, hqr, nb] at hk0; cases hk0
      rw [hr_self] at hr_root
      exact hrv hr_root.symm
    · have hq_cyc : ∀ m ≤ d, iterOpt p m u = iterOpt q m u := by
        intro m hm
        induction m with
        | zero => rfl
        | succ m ihm =>
          rw [iterOpt, iterOpt, ihm (by omega)]
          cases hm_q : iterOpt q m u with
          | none => rfl
          | some w =>
            have hne_r : w ≠ r := fun h => hr_hit ⟨m, hm, (ihm (by omega) ▸ (h ▸ hm_q))⟩
            have : p w = q w := by dsimp [p, addEdge]; simp [hne_r]
            simpa [sb] using this
      have hq_d : iterOpt q d u = some u := by rw [← hq_cyc d le_rfl, hcyc]
      exact iterOpt_cycle_contra q hq hd_pos u hq_d
  rcases hlt with h12 | h21
  · exact hswap t1 t2 h12 heq_f
  · exact hswap t2 t1 h21 heq_f.symm

lemma eraseEdge_acyclic {n : ℕ} {p : RF n} (hp : isAcyclic p) (r : Fin (n + 1)) :
    isAcyclic (eraseEdge p r) := by
  have hsub : ∀ k v w, iterOpt (eraseEdge p r) k v = some w → iterOpt p k v = some w := by
    intro k
    induction k with
    | zero => intro v w h; simpa [iterOpt] using h
    | succ k ih =>
      intro v w h
      rw [iterOpt] at h ⊢
      cases hk : iterOpt (eraseEdge p r) k v with
      | none => rw [hk] at h; cases h
      | some u =>
        rw [hk, sb] at h
        rw [ih v u hk, sb]
        dsimp [eraseEdge] at h
        by_cases hur : u = r
        · simp [hur] at h
        · simpa [hur] using h
  intro v
  cases h : iterOpt (eraseEdge p r) (n + 1) v with
  | none => rfl
  | some w =>
    have := hsub (n + 1) v w h
    rw [hp v] at this
    simp at this

lemma eraseEdge_edgeCount {n : ℕ} {p : RF n} {r v : Fin (n + 1)} (hpr : p r = some v) :
    edgeCount (eraseEdge p r) + 1 = edgeCount p := by
  dsimp [edgeCount]
  have hmem : r ∈ Finset.univ.filter (fun u => (p u).isSome) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hpr]⟩
  have hset : Finset.univ.filter (fun u => (eraseEdge p r u).isSome) =
      (Finset.univ.filter (fun u => (p u).isSome)).erase r := by
    ext u
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [eraseEdge]
    by_cases hur : u = r <;> simp [hur]
  rw [hset, Finset.card_erase_of_mem hmem, Nat.sub_add_cancel (Finset.card_pos.mpr ⟨r, hmem⟩)]

lemma addEdge_edgeCount {n : ℕ} {q : RF n} {r v : Fin (n + 1)} (hqr : q r = none) :
    edgeCount (addEdge q r v) = edgeCount q + 1 := by
  dsimp [edgeCount]
  have hnmem : r ∉ Finset.univ.filter (fun u => (q u).isSome) := by
    simp [hqr]
  have hset : Finset.univ.filter (fun u => (addEdge q r v u).isSome) =
      insert r (Finset.univ.filter (fun u => (q u).isSome)) := by
    ext u
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [addEdge]
    by_cases hur : u = r <;> simp [hur]
  rw [hset, Finset.card_insert_of_notMem hnmem, Nat.add_comm]

lemma pitman_step (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    k * (RF_k n k).card = (n + 1) * (n + 1 - k) * (RF_k n (k - 1)).card := by
  let L := (RF_k n k).sigma (fun p => Finset.univ.filter (fun r => (p r).isSome))
  let R := (RF_k n (k - 1)).sigma (fun q =>
    (Finset.univ : Finset (Fin (n + 1))).sigma (fun v => (roots q).erase (rootOf q v)))
  have hL : L.card = k * (RF_k n k).card := by
    rw [Finset.card_sigma]
    calc ∑ p ∈ RF_k n k, (Finset.univ.filter (fun r => (p r).isSome)).card
        = ∑ _p ∈ RF_k n k, k := Finset.sum_congr rfl fun p hp => (Finset.mem_filter.mp hp).2.2
      _ = k * (RF_k n k).card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hR : R.card = (n + 1) * (n + 1 - k) * (RF_k n (k - 1)).card := by
    rw [Finset.card_sigma]
    have hinner : ∀ q ∈ RF_k n (k - 1),
        ((Finset.univ : Finset (Fin (n + 1))).sigma (fun v => (roots q).erase (rootOf q v))).card =
        (n + 1) * (n + 1 - k) := by
      intro q hq
      have hq_ac := (Finset.mem_filter.mp hq).2.1
      have hq_ec := (Finset.mem_filter.mp hq).2.2
      have hq_rc := roots_add_edgeCount q
      rw [Finset.card_sigma]
      calc ∑ v : Fin (n + 1), ((roots q).erase (rootOf q v)).card
          = ∑ _v : Fin (n + 1), (n + 1 - k) := by
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [Finset.card_erase_of_mem (rootOf_spec q hq_ac v).1]
            omega
        _ = (n + 1) * (n + 1 - k) := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin]
    calc ∑ q ∈ RF_k n (k - 1),
          ((Finset.univ : Finset (Fin (n + 1))).sigma (fun v => (roots q).erase (rootOf q v))).card
        = ∑ _q ∈ RF_k n (k - 1), ((n + 1) * (n + 1 - k)) := Finset.sum_congr rfl hinner
      _ = (n + 1) * (n + 1 - k) * (RF_k n (k - 1)).card := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  rw [← hL, ← hR]
  apply Finset.card_bij (fun pr hpr =>
    let p := pr.1; let r := pr.2
    let v := (p r).get (Finset.mem_filter.mp (Finset.mem_sigma.mp hpr).2).2
    ⟨eraseEdge p r, v, r⟩)
  · rintro ⟨p, r⟩ hpr
    have hp := (Finset.mem_sigma.mp hpr).1
    have hr := (Finset.mem_filter.mp (Finset.mem_sigma.mp hpr).2).2
    have hprv : p r = some ((p r).get hr) := (Option.some_get hr).symm
    have hq_ac := eraseEdge_acyclic (Finset.mem_filter.mp hp).2.1 r
    have hq_ec : edgeCount (eraseEdge p r) = k - 1 := by
      have hec := eraseEdge_edgeCount hprv
      have hkp : edgeCount p = k := (Finset.mem_filter.mp hp).2.2
      omega
    have hq_mem : eraseEdge p r ∈ RF_k n (k - 1) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq_ac, hq_ec⟩
    have hr_root : r ∈ roots (eraseEdge p r) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [eraseEdge]⟩
    have hne : r ≠ rootOf (eraseEdge p r) ((p r).get hr) := by
      intro hEq
      obtain ⟨_, d, _, hd⟩ := rootOf_spec (eraseEdge p r) hq_ac ((p r).get hr)
      rw [← hEq] at hd
      have hsub : ∀ m a b, iterOpt (eraseEdge p r) m a = some b → iterOpt p m a = some b := by
        intro m
        induction m with
        | zero => intro a b h; simpa [iterOpt] using h
        | succ m ih =>
          intro a b h
          rw [iterOpt] at h ⊢
          cases hm : iterOpt (eraseEdge p r) m a with
          | none => rw [hm] at h; cases h
          | some u =>
            rw [hm, sb] at h
            rw [ih a u hm, sb]
            dsimp [eraseEdge] at h
            by_cases hur : u = r
            · simp [hur] at h
            · simpa [hur] using h
      have hp_d := hsub d ((p r).get hr) r hd
      have hp_cyc : iterOpt p (d + 1) r = some r := by
        rw [iterOpt_succ_left, hprv, sb, hp_d]
      exact iterOpt_cycle_contra p (Finset.mem_filter.mp hp).2.1 (Nat.succ_pos d) r hp_cyc
    exact Finset.mem_sigma.mpr ⟨hq_mem, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_erase.mpr ⟨hne, hr_root⟩⟩⟩
  · rintro ⟨p1, r1⟩ h1 ⟨p2, r2⟩ h2 hEq
    dsimp at hEq
    have hr1 := (Finset.mem_filter.mp (Finset.mem_sigma.mp h1).2).2
    have hr2 := (Finset.mem_filter.mp (Finset.mem_sigma.mp h2).2).2
    have he1 := congrArg Sigma.fst hEq
    have hv := congrArg (fun x => x.2.1) hEq
    have hr : r1 = r2 := congrArg (fun x => x.2.2) hEq
    dsimp at he1 hv hr
    have hp12 : p1 = p2 := by
      funext u
      by_cases hu : u = r1
      · have ha1 : p1 r1 = some ((p1 r1).get hr1) := (Option.some_get hr1).symm
        have ha2 : p2 r1 = some ((p2 r2).get hr2) := by rw [hr]; exact (Option.some_get hr2).symm
        rw [hu, ha1, ha2, hv]
      · have hur2 : u ≠ r2 := fun h => hu (h.trans hr.symm)
        have hfn := congrFun he1 u
        simpa [eraseEdge, hu, hur2] using hfn
    subst hp12; subst hr; rfl
  · rintro ⟨q, v, r⟩ hqvr
    have hq := (Finset.mem_sigma.mp hqvr).1
    have hvr := (Finset.mem_sigma.mp (Finset.mem_sigma.mp hqvr).2).2
    have hne := (Finset.mem_erase.mp hvr).1
    have hr_root := (Finset.mem_erase.mp hvr).2
    have hqr : q r = none := (Finset.mem_filter.mp hr_root).2
    have hq_ac := (Finset.mem_filter.mp hq).2.1
    have hq_ec : edgeCount q = k - 1 := (Finset.mem_filter.mp hq).2.2
    let p := addEdge q r v
    have hp_ac := addEdge_acyclic hq_ac hqr hne
    have hp_ec : edgeCount p = k := by
      change edgeCount (addEdge q r v) = k
      rw [addEdge_edgeCount (r := r) (v := v) hqr, hq_ec]
      omega
    have hp_mem : p ∈ RF_k n k := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp_ac, hp_ec⟩
    have hr_some : (p r).isSome = true := by dsimp [p, addEdge]; simp
    refine ⟨⟨p, r⟩, Finset.mem_sigma.mpr ⟨hp_mem, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr_some⟩⟩, ?_⟩
    have her : eraseEdge p r = q := by
      funext u
      dsimp [eraseEdge, p, addEdge]
      split_ifs with hu
      · subst hu; exact hqr.symm
      · rfl
    have hv_eq : (p r).get hr_some = v := by
      have : p r = some v := by dsimp [p, addEdge]; simp
      simp [this]
    simp [her, hv_eq]

def ffact (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => (n - k) * ffact n k

lemma ffact_mul_factorial (n k : ℕ) (hk : k ≤ n) :
    (n - k).factorial * ffact n k = n.factorial := by
  induction k with
  | zero => simp [ffact]
  | succ k ih =>
    have hle : k ≤ n := Nat.le_of_succ_le hk
    rw [ffact, ← Nat.mul_assoc, show n - k = (n - (k + 1)) + 1 by omega]
    rw [Nat.mul_comm _ ((n - (k + 1)) + 1), ← Nat.factorial_succ]
    have hsub : n - (k + 1) + 1 = n - k := by omega
    rw [hsub]
    exact ih hle

lemma RF_k_card_formula (n k : ℕ) (hk : k ≤ n) :
    k.factorial * (RF_k n k).card = (n + 1) ^ k * ffact n k := by
  induction k with
  | zero =>
    simp only [Nat.factorial_zero, Nat.one_mul, pow_zero, ffact]
    have hrf0 : RF_k n 0 = {fun _ => none} := by
      ext p
      simp only [RF_k, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hec⟩
        dsimp [edgeCount] at hec
        rw [Finset.card_eq_zero] at hec
        funext v
        by_contra hne
        have hv : v ∈ Finset.univ.filter (fun u => (p u).isSome) := by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          cases hpv : p v with
          | none => exact absurd hpv hne
          | some _ => rfl
        rw [hec] at hv; simp at hv
      · rintro rfl
        refine ⟨fun v => by change (iterOpt (fun _ => none) n v).bind (fun _ => none) = none; cases iterOpt (fun _ => none) n v <;> rfl, ?_⟩
        simp [edgeCount]
    rw [hrf0, Finset.card_singleton]
  | succ k ih =>
    have hle : k ≤ n := Nat.le_of_succ_le hk
    have hstep := pitman_step n (k + 1) (Nat.succ_pos k) hk
    simp only [Nat.add_sub_cancel] at hstep
    calc (k + 1).factorial * (RF_k n (k + 1)).card
        = k.factorial * ((k + 1) * (RF_k n (k + 1)).card) := by rw [Nat.factorial_succ]; ring
      _ = k.factorial * ((n + 1) * (n - k) * (RF_k n k).card) := by
          rw [show n + 1 - (k + 1) = n - k by omega] at hstep
          rw [hstep]
      _ = (n + 1) * (n - k) * (k.factorial * (RF_k n k).card) := by ring
      _ = (n + 1) * (n - k) * ((n + 1) ^ k * ffact n k) := by rw [ih hle]
      _ = (n + 1) ^ (k + 1) * ffact n (k + 1) := by rw [ffact, pow_succ]; ring

theorem largest_card_formula (n : ℕ) (hn : 0 < n) :
    (n + 1) * (largest n).card = 2 ^ n * (n + 1) ^ (n - 1) := by
  have h1 : (largest n).card = (allTrees n).card := largest_card_eq_allTrees n hn
  have h2 : (n + 1) * (allTrees n).card = 2 ^ n * (treesAt0 n).card := double_count_roots n
  have h3 : (rootedTree0 n).card = (treesAt0 n).card := rootedTree0_card_eq_treesAt0 n hn
  have h4 : (RF_k n n).card = (n + 1) * (rootedTree0 n).card := RF_n_card_eq n
  have h5 := RF_k_card_formula n n le_rfl
  have hff : ffact n n = n.factorial := by
    have := ffact_mul_factorial n n le_rfl
    simpa using this
  rw [hff] at h5
  have hrf : (RF_k n n).card = (n + 1) ^ n := by
    exact Nat.mul_left_cancel (Nat.factorial_pos n) (by simpa [Nat.mul_comm] using h5)
  have hprod : (n + 1) * ((n + 1) * (largest n).card) = (n + 1) * (2 ^ n * (n + 1) ^ (n - 1)) := by
    calc (n + 1) * ((n + 1) * (largest n).card)
        = (n + 1) * (2 ^ n * (treesAt0 n).card) := by rw [h1, h2]
      _ = 2 ^ n * ((n + 1) * (rootedTree0 n).card) := by rw [← h3]; ring
      _ = 2 ^ n * (n + 1) ^ n := by rw [← h4, hrf]
      _ = 2 ^ n * ((n + 1) * (n + 1) ^ (n - 1)) := by
          have hpown : (n + 1) ^ n = (n + 1) * (n + 1) ^ (n - 1) := by
            have heq : (n + 1) ^ n = (n + 1) ^ ((n - 1) + 1) :=
              congrArg (fun e => (n + 1) ^ e) (by omega)
            rw [heq, pow_succ, Nat.mul_comm]
          rw [hpown]
      _ = (n + 1) * (2 ^ n * (n + 1) ^ (n - 1)) := by ring
  exact Nat.mul_left_cancel (Nat.succ_pos n) hprod

end Part4_Counting

end PEqualNP.Outside.L_lib_1179_aux

theorem PEqualNP.Outside.L_lib_1179 :
    ∀ (n : Nat), 0 < n →
      let Site := Fin n
      let Word := Finset Site
      let Edge := {ij : Site × Site // ij.1 < ij.2}
      let Signing := Edge → Bool × Bool
      let cube := (Finset.univ : Finset Word)
      let region := fun (s : Signing) => cube.filter (fun x =>
        ∀ e : Edge, (decide (e.val.1 ∈ x), decide (e.val.2 ∈ x)) ≠ s e)
      let tree := fun (X : Finset Word) =>
        ∃ node : Fin (n + 1) → Word, ∃ dir : Equiv.Perm Site, ∃ parent : Site → Fin (n + 1),
          X = Finset.univ.image node ∧ ∀ i : Site,
            (parent i).val ≤ i.val ∧ node i.succ =
              (if dir i ∈ node (parent i) then (node (parent i)).erase (dir i)
               else insert (dir i) (node (parent i)))
      let largest := (Finset.univ : Finset Signing).filter (fun s => (region s).card = n + 1)
      (∀ X : Finset Word, tree X ↔ ∃ s ∈ largest, region s = X) ∧
      (∀ s : Signing, ∃ u ∈ largest, region s ⊆ region u) ∧
      (∀ (k : Nat) (P : Finset Word) (w : Word → Nat) (f : Fin k → Signing),
        ∃ g : Fin k → Signing, (∀ i, g i ∈ largest) ∧
          ((P.filter (fun x => ∃ i, x ∈ region (f i))).sum w) ≤
          ((P.filter (fun x => ∃ i, x ∈ region (g i))).sum w)) ∧
      (n + 1) * largest.card = 2 ^ n * (n + 1) ^ (n - 1) := by
  intro n hn
  exact
    ⟨PEqualNP.Outside.L_lib_1179_aux.tree_iff_largest n hn,
     PEqualNP.Outside.L_lib_1179_aux.extend_to_largest n hn,
     PEqualNP.Outside.L_lib_1179_aux.weighted_cover_largest n hn,
     PEqualNP.Outside.L_lib_1179_aux.largest_card_formula n hn⟩

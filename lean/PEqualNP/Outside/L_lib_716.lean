import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_716

def ofVecNat : ∀ {k : ℕ}, (Fin k → Bool) → ℕ
  | 0, _ => 0
  | k + 1, f => (if f 0 then 1 else 0) + 2 * ofVecNat (fun i : Fin k => f i.succ)

lemma ofVecNat_lt : ∀ {k : ℕ} (f : Fin k → Bool), ofVecNat f < 2 ^ k
  | 0, _ => by simp [ofVecNat]
  | k + 1, f => by
    have ih := ofVecNat_lt (fun i : Fin k => f i.succ)
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    cases hf : f 0 <;> simp [ofVecNat, hf] <;> omega

lemma testBit_ofVecNat : ∀ {k : ℕ} (f : Fin k → Bool) (i : Fin k),
    (ofVecNat f).testBit i.val = f i
  | 0, _, i => Fin.elim0 i
  | k + 1, f, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.val_zero, Nat.testBit_zero, ofVecNat]
      cases hf : f 0
      · simp
      · simp
    · simp only [Fin.val_succ, Nat.testBit_succ, ofVecNat]
      have hdiv : ((if f 0 then 1 else 0) + 2 * ofVecNat (fun i : Fin k => f i.succ)) / 2 =
          ofVecNat (fun i : Fin k => f i.succ) := by
        cases f 0 <;> simp <;> omega
      rw [hdiv]
      exact testBit_ofVecNat (fun i : Fin k => f i.succ) j

lemma ofVecNat_toVec : ∀ {k : ℕ} (n : ℕ), n < 2 ^ k →
    ofVecNat (fun i : Fin k => n.testBit i.val) = n
  | 0, n, hn => by simp [ofVecNat]; omega
  | k + 1, n, hn => by
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have hdiv : n / 2 < 2 ^ k := by omega
    have ih := ofVecNat_toVec (n / 2) hdiv
    simp only [ofVecNat, Fin.val_zero, Fin.val_succ, Nat.testBit_succ]
    rw [ih]
    simp only [Nat.testBit_zero]
    have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hmod with h0 | h1
    · simp [h0]; omega
    · simp [h1]; omega

def toVec {k : ℕ} (v : Fin (2 ^ k)) : Fin k → Bool :=
  fun i => v.val.testBit i.val

def ofVec {k : ℕ} (f : Fin k → Bool) : Fin (2 ^ k) :=
  ⟨ofVecNat f, ofVecNat_lt f⟩

lemma toVec_ofVec {k : ℕ} (f : Fin k → Bool) : toVec (ofVec f) = f := by
  funext i; exact testBit_ofVecNat f i

lemma ofVec_toVec {k : ℕ} (v : Fin (2 ^ k)) : ofVec (toVec v) = v := by
  apply Fin.ext
  exact ofVecNat_toVec v.val v.isLt

def toVecEquiv (k : ℕ) : Fin (2 ^ k) ≃ (Fin k → Bool) where
  toFun := toVec
  invFun := ofVec
  left_inv := ofVec_toVec
  right_inv := toVec_ofVec

def vzero (k : ℕ) : Fin k → Bool := fun _ => false

def vxor {k : ℕ} (a b : Fin k → Bool) : Fin k → Bool :=
  fun i => xor (a i) (b i)

def basis {k : ℕ} (i : Fin k) : Fin k → Bool :=
  fun j => decide (j = i)

lemma vxor_self {k : ℕ} (a : Fin k → Bool) : vxor a a = vzero k := by
  funext i; simp [vxor, vzero]

lemma vxor_zero_left {k : ℕ} (a : Fin k → Bool) : vxor (vzero k) a = a := by
  funext i; simp [vxor, vzero]

lemma vxor_zero_right {k : ℕ} (a : Fin k → Bool) : vxor a (vzero k) = a := by
  funext i; simp [vxor, vzero]

lemma vxor_comm {k : ℕ} (a b : Fin k → Bool) : vxor a b = vxor b a := by
  funext i; exact Bool.xor_comm (a i) (b i)

lemma vxor_assoc {k : ℕ} (a b c : Fin k → Bool) : vxor (vxor a b) c = vxor a (vxor b c) := by
  funext i; exact Bool.xor_assoc (a i) (b i) (c i)

lemma vxor_cancel_right {k : ℕ} (a b : Fin k → Bool) : vxor (vxor a b) b = a := by
  rw [vxor_assoc, vxor_self, vxor_zero_right]

lemma vxor_eq_zero_iff {k : ℕ} (a b : Fin k → Bool) : vxor a b = vzero k ↔ a = b := by
  constructor
  · intro h
    have h1 := congrArg (fun x => vxor x b) h
    simpa [vxor_cancel_right, vxor_zero_left] using h1
  · rintro rfl; exact vxor_self a

def vdotS {k : ℕ} (S : Finset (Fin k)) (a b : Fin k → Bool) : Bool :=
  (S.filter (fun i => a i && b i)).card % 2 == 1

def vdot {k : ℕ} (a b : Fin k → Bool) : Bool :=
  vdotS Finset.univ a b

lemma vdotS_empty {k : ℕ} (a b : Fin k → Bool) : vdotS ∅ a b = false := by
  simp [vdotS]

lemma vdotS_insert {k : ℕ} {i : Fin k} {S : Finset (Fin k)} (hi : i ∉ S)
    (a b : Fin k → Bool) :
    vdotS (insert i S) a b = xor (a i && b i) (vdotS S a b) := by
  unfold vdotS
  rw [Finset.filter_insert]
  have hni : i ∉ S.filter (fun j => a j && b j) := fun hm => hi (Finset.mem_filter.mp hm).1
  cases hab : (a i && b i)
  · simp [hab]
  · simp only [hab, ↓reduceIte, Finset.card_insert_of_notMem hni]
    set m := (S.filter (fun j => a j && b j)).card
    have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
    rcases hm with h0 | h1
    · have h1' : (m + 1) % 2 = 1 := by omega
      simp [h0, h1']
    · have h0' : (m + 1) % 2 = 0 := by omega
      simp [h0', h1]

lemma vdotS_xor_left {k : ℕ} (S : Finset (Fin k)) (a b c : Fin k → Bool) :
    vdotS S (vxor a b) c = xor (vdotS S a c) (vdotS S b c) := by
  induction S using Finset.induction with
  | empty => simp [vdotS_empty]
  | insert i s hi ih =>
    rw [vdotS_insert hi, vdotS_insert hi, vdotS_insert hi, ih]
    simp only [vxor]
    have : ∀ x y z u v : Bool,
        xor (xor x y && z) (xor u v) = xor (xor (x && z) u) (xor (y && z) v) := by decide
    exact this _ _ _ _ _

lemma vdot_comm {k : ℕ} (a b : Fin k → Bool) : vdot a b = vdot b a := by
  unfold vdot vdotS
  have hfilt : (Finset.univ : Finset (Fin k)).filter (fun i => a i && b i) =
      (Finset.univ : Finset (Fin k)).filter (fun i => b i && a i) := by
    ext i; simp [Bool.and_comm]
  rw [hfilt]

lemma vdot_xor_left {k : ℕ} (a b c : Fin k → Bool) :
    vdot (vxor a b) c = xor (vdot a c) (vdot b c) :=
  vdotS_xor_left Finset.univ a b c

lemma vdot_xor_right {k : ℕ} (a b c : Fin k → Bool) :
    vdot a (vxor b c) = xor (vdot a b) (vdot a c) := by
  rw [vdot_comm, vdot_xor_left, vdot_comm b a, vdot_comm c a]

lemma vdot_zero_right {k : ℕ} (a : Fin k → Bool) : vdot a (vzero k) = false := by
  simp [vdot, vdotS, vzero]

lemma vdot_basis_right {k : ℕ} (a : Fin k → Bool) (i : Fin k) :
    vdot a (basis i) = a i := by
  unfold vdot vdotS basis
  cases hai : a i
  · have hfilt : (Finset.univ : Finset (Fin k)).filter (fun j => a j && decide (j = i)) = ∅ := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro h
      have hj : j = i := by simpa using (Bool.and_eq_true _ _).mp h |>.2
      subst hj
      have ha : a j = true := (Bool.and_eq_true _ _).mp h |>.1
      rw [hai] at ha; exact Bool.noConfusion ha
    rw [hfilt]; simp
  · have hfilt : (Finset.univ : Finset (Fin k)).filter (fun j => a j && decide (j = i)) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; simpa using (Bool.and_eq_true _ _).mp h |>.2
      · rintro rfl; simp [hai]
    rw [hfilt]; simp

lemma vdot_eq_dot {k : ℕ} (u v : Fin (2 ^ k)) :
    (((Finset.univ : Finset (Fin k)).filter (fun i => u.val.testBit i.val) ∩
      (Finset.univ : Finset (Fin k)).filter (fun i => v.val.testBit i.val)).card % 2 == 1) =
    vdot (toVec u) (toVec v) := by
  unfold vdot vdotS toVec
  have hfilt : (Finset.univ : Finset (Fin k)).filter (fun i => u.val.testBit i.val) ∩
      (Finset.univ : Finset (Fin k)).filter (fun i => v.val.testBit i.val) =
      (Finset.univ : Finset (Fin k)).filter (fun i => u.val.testBit i.val && v.val.testBit i.val) := by
    ext i; simp [Bool.and_eq_true]
  rw [hfilt]

-- Surjectivity of 2-coordinate linear functional over Fin k → Bool
lemma surj2 {k : ℕ} (u v : Fin k → Bool)
    (hu : u ≠ vzero k) (hv : v ≠ vzero k) (huv : u ≠ v) :
    ∀ p : Bool × Bool, ∃ x : Fin k → Bool, (vdot u x, vdot v x) = p := by
  have hann : ∀ α β : Bool, (α = true ∨ β = true) →
      ∃ x : Fin k → Bool, xor (α && vdot u x) (β && vdot v x) = true := by
    intro α β hab
    have hne : (fun i => xor (α && u i) (β && v i)) ≠ vzero k := by
      cases α <;> cases β
      · simp at hab
      · simpa [vzero] using hv
      · simpa [vzero] using hu
      · intro h
        apply huv
        rw [← vxor_eq_zero_iff]
        funext i
        simpa [vxor, vzero] using congrFun h i
    have hex : ∃ i : Fin k, xor (α && u i) (β && v i) = true := by
      by_contra hall
      push_neg at hall
      apply hne
      funext i
      cases h : xor (α && u i) (β && v i)
      · rfl
      · exact False.elim (hall i h)
    obtain ⟨i, hi⟩ := hex
    refine ⟨basis i, ?_⟩
    rw [vdot_basis_right, vdot_basis_right]
    exact hi
  obtain ⟨p1, hp1⟩ := hann true false (Or.inl rfl)
  simp only [Bool.true_and, Bool.false_and, Bool.xor_false] at hp1
  obtain ⟨p2, hp2⟩ := hann (vdot v p1) true (Or.inr rfl)
  simp only [Bool.true_and] at hp2
  let q2 := if vdot u p2 then vxor p2 p1 else p2
  have hq2u : vdot u q2 = false := by
    dsimp only [q2]
    cases h : vdot u p2
    · simp [h]
    · simp [h, vdot_xor_right, hp1]
  have hq2v : vdot v q2 = true := by
    dsimp only [q2]
    cases h : vdot u p2
    · simp only [h, Bool.and_false, Bool.false_xor] at hp2; simp [h, hp2]
    · simp only [h, Bool.and_true] at hp2
      simp [h, vdot_xor_right, Bool.xor_comm, hp2]
  let e1 := if vdot v p1 then vxor p1 q2 else p1
  have he1u : vdot u e1 = true := by
    dsimp only [e1]
    cases h : vdot v p1 <;> simp [h, vdot_xor_right, hp1, hq2u]
  have he1v : vdot v e1 = false := by
    dsimp only [e1]
    cases h : vdot v p1 <;> simp [h, vdot_xor_right, hq2v]
  rintro ⟨a, b⟩
  refine ⟨vxor (if a then e1 else vzero k) (if b then q2 else vzero k), ?_⟩
  refine Prod.ext ?_ ?_
  · cases a <;> cases b <;> simp [vdot_xor_right, vdot_zero_right, he1u, hq2u]
  · cases a <;> cases b <;> simp [vdot_xor_right, vdot_zero_right, he1v, hq2v]

-- Surjectivity of 3-coordinate linear functional over Fin k → Bool
lemma surj3 {k : ℕ} (u v w : Fin k → Bool)
    (hu : u ≠ vzero k) (hv : v ≠ vzero k) (hw : w ≠ vzero k)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (huvw : vxor u v ≠ w) :
    ∀ p : Bool × Bool × Bool, ∃ x : Fin k → Bool, (vdot u x, vdot v x, vdot w x) = p := by
  have hann : ∀ α β γ : Bool, (α = true ∨ β = true ∨ γ = true) →
      ∃ x : Fin k → Bool, xor (α && vdot u x) (xor (β && vdot v x) (γ && vdot w x)) = true := by
    intro α β γ habc
    have hne : (fun i => xor (α && u i) (xor (β && v i) (γ && w i))) ≠ vzero k := by
      cases α <;> cases β <;> cases γ
      · simp at habc
      · simpa [vzero] using hw
      · simpa [vzero] using hv
      · intro h; apply hvw; rw [← vxor_eq_zero_iff]; funext i
        simpa [vxor, vzero] using congrFun h i
      · simpa [vzero] using hu
      · intro h; apply huw; rw [← vxor_eq_zero_iff]; funext i
        simpa [vxor, vzero] using congrFun h i
      · intro h; apply huv; rw [← vxor_eq_zero_iff]; funext i
        simpa [vxor, vzero] using congrFun h i
      · intro h; apply huvw; rw [← vxor_eq_zero_iff]; funext i
        have hi := congrFun h i
        simp only [vxor, vzero, Bool.true_and] at hi ⊢
        rw [Bool.xor_assoc]; exact hi
    have hex : ∃ i : Fin k, xor (α && u i) (xor (β && v i) (γ && w i)) = true := by
      by_contra hall
      push_neg at hall
      apply hne
      funext i
      cases h : xor (α && u i) (xor (β && v i) (γ && w i))
      · rfl
      · exact False.elim (hall i h)
    obtain ⟨i, hi⟩ := hex
    refine ⟨basis i, ?_⟩
    rw [vdot_basis_right, vdot_basis_right, vdot_basis_right]
    exact hi
  -- Step 1: get p1 with u·p1 = true
  obtain ⟨p1, hp1⟩ := hann true false false (Or.inl rfl)
  simp only [Bool.true_and, Bool.false_and, Bool.xor_false] at hp1
  -- Step 2: get p2 with (v·p1)∧(u·p2) ⊕ (v·p2) = true
  obtain ⟨p2, hp2⟩ := hann (vdot v p1) true false (Or.inr (Or.inl rfl))
  simp only [Bool.true_and, Bool.false_and, Bool.xor_false] at hp2
  let q2 := if vdot u p2 then vxor p2 p1 else p2
  have hq2u : vdot u q2 = false := by
    dsimp only [q2]; cases h : vdot u p2 <;> simp [h, vdot_xor_right, hp1]
  have hq2v : vdot v q2 = true := by
    dsimp only [q2]; cases h : vdot u p2
    · simp only [h, Bool.and_false, Bool.false_xor] at hp2; simp [h, hp2]
    · simp only [h, Bool.and_true] at hp2; simp [h, vdot_xor_right, Bool.xor_comm, hp2]
  let q1 := if vdot v p1 then vxor p1 q2 else p1
  have hq1u : vdot u q1 = true := by
    dsimp only [q1]; cases h : vdot v p1 <;> simp [h, vdot_xor_right, hp1, hq2u]
  have hq1v : vdot v q1 = false := by
    dsimp only [q1]; cases h : vdot v p1 <;> simp [h, vdot_xor_right, hq2v]
  -- Step 3: get p3 with (w·q1)∧(u·p3) ⊕ (w·q2)∧(v·p3) ⊕ (w·p3) = true
  obtain ⟨p3, hp3⟩ := hann (vdot w q1) (vdot w q2) true (Or.inr (Or.inr rfl))
  simp only [Bool.true_and] at hp3
  let e3 := vxor (if vdot u p3 then q1 else vzero k)
              (vxor (if vdot v p3 then q2 else vzero k) p3)
  have he3u : vdot u e3 = false := by
    dsimp only [e3]; rw [vdot_xor_right, vdot_xor_right]
    cases hu3 : vdot u p3 <;> cases hv3 : vdot v p3 <;>
      simp [hu3, hv3, vdot_zero_right, hq1u, hq2u]
  have he3v : vdot v e3 = false := by
    dsimp only [e3]; rw [vdot_xor_right, vdot_xor_right]
    cases hu3 : vdot u p3 <;> cases hv3 : vdot v p3 <;>
      simp [hu3, hv3, vdot_zero_right, hq1v, hq2v]
  have he3w : vdot w e3 = true := by
    dsimp only [e3]; rw [vdot_xor_right, vdot_xor_right]
    cases hu3 : vdot u p3 <;> cases hv3 : vdot v p3 <;>
      simp [hu3, hv3, vdot_zero_right] at hp3 ⊢ <;> exact hp3
  let e1 := if vdot w q1 then vxor q1 e3 else q1
  have he1u : vdot u e1 = true := by
    dsimp only [e1]; cases h : vdot w q1 <;> simp [h, vdot_xor_right, hq1u, he3u]
  have he1v : vdot v e1 = false := by
    dsimp only [e1]; cases h : vdot w q1 <;> simp [h, vdot_xor_right, hq1v, he3v]
  have he1w : vdot w e1 = false := by
    dsimp only [e1]; cases h : vdot w q1 <;> simp [h, vdot_xor_right, he3w]
  let e2 := if vdot w q2 then vxor q2 e3 else q2
  have he2u : vdot u e2 = false := by
    dsimp only [e2]; cases h : vdot w q2 <;> simp [h, vdot_xor_right, hq2u, he3u]
  have he2v : vdot v e2 = true := by
    dsimp only [e2]; cases h : vdot w q2 <;> simp [h, vdot_xor_right, hq2v, he3v]
  have he2w : vdot w e2 = false := by
    dsimp only [e2]; cases h : vdot w q2 <;> simp [h, vdot_xor_right, he3w]
  rintro ⟨a, b, c⟩
  refine ⟨vxor (if a then e1 else vzero k)
            (vxor (if b then e2 else vzero k) (if c then e3 else vzero k)), ?_⟩
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · cases a <;> cases b <;> cases c <;> simp [vdot_xor_right, vdot_zero_right, he1u, he2u, he3u]
  · cases a <;> cases b <;> cases c <;> simp [vdot_xor_right, vdot_zero_right, he1v, he2v, he3v]
  · cases a <;> cases b <;> cases c <;> simp [vdot_xor_right, vdot_zero_right, he1w, he2w, he3w]

lemma card_vec (k : ℕ) : (Finset.univ : Finset (Fin k → Bool)).card = 2 ^ k := by
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

lemma card_fiber2 {k : ℕ} (u v : Fin k → Bool)
    (hu : u ≠ vzero k) (hv : v ≠ vzero k) (huv : u ≠ v) (r1 r2 : Bool) :
    4 * (Finset.univ.filter (fun x : Fin k → Bool => vdot u x = r1 ∧ vdot v x = r2)).card = 2 ^ k := by
  let φ : (Fin k → Bool) → Bool × Bool := fun x => (vdot u x, vdot v x)
  have heq : ∀ p : Bool × Bool,
      (Finset.univ.filter (fun x : Fin k → Bool => φ x = p)).card =
      (Finset.univ.filter (fun x : Fin k → Bool => φ x = (false, false))).card := by
    intro p
    obtain ⟨y, hy⟩ := surj2 u v hu hv huv p
    refine Finset.card_bij (fun x _ => vxor x y) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have hx1 : vdot u x = p.1 := by simpa [φ] using congrArg Prod.fst hx
      have hx2 : vdot v x = p.2 := by simpa [φ] using congrArg Prod.snd hx
      have hy1 : vdot u y = p.1 := congrArg Prod.fst hy
      have hy2 : vdot v y = p.2 := congrArg Prod.snd hy
      simp [φ, vdot_xor_right, hx1, hx2, hy1, hy2]
    · intro x1 _ x2 _ h
      have := congrArg (fun z => vxor z y) h
      simpa [vxor_cancel_right] using this
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      refine ⟨vxor z y, ?_, vxor_cancel_right z y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hz1 : vdot u z = false := by simpa [φ] using congrArg Prod.fst hz
      have hz2 : vdot v z = false := by simpa [φ] using congrArg Prod.snd hz
      have hy1 : vdot u y = p.1 := congrArg Prod.fst hy
      have hy2 : vdot v y = p.2 := congrArg Prod.snd hy
      simp [φ, vdot_xor_right, hz1, hz2, hy1, hy2]
  have hpart : (Finset.univ : Finset (Fin k → Bool)).card =
      ∑ p : Bool × Bool, (Finset.univ.filter (fun x : Fin k → Bool => φ x = p)).card := by
    simpa using (Finset.card_eq_sum_card_fiberwise (f := φ) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _))
  rw [card_vec] at hpart
  have hsum : ∑ p : Bool × Bool, (Finset.univ.filter (fun x : Fin k → Bool => φ x = p)).card =
      4 * (Finset.univ.filter (fun x : Fin k → Bool => φ x = (false, false))).card := by
    simp_rw [heq]
    simp [Finset.sum_const]
  have htarget : (Finset.univ.filter (fun x : Fin k → Bool => vdot u x = r1 ∧ vdot v x = r2)).card =
      (Finset.univ.filter (fun x : Fin k → Bool => φ x = (r1, r2))).card := by
    have hset : Finset.univ.filter (fun x : Fin k → Bool => vdot u x = r1 ∧ vdot v x = r2) =
        Finset.univ.filter (fun x : Fin k → Bool => φ x = (r1, r2)) := by
      ext x; simp [φ, Prod.ext_iff]
    rw [hset]
  rw [htarget, heq (r1, r2), ← hsum, ← hpart]

lemma card_fiber3 {k : ℕ} (u v w : Fin k → Bool)
    (hu : u ≠ vzero k) (hv : v ≠ vzero k) (hw : w ≠ vzero k)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (huvw : vxor u v ≠ w)
    (r1 r2 r3 : Bool) :
    8 * (Finset.univ.filter (fun x : Fin k → Bool =>
        vdot u x = r1 ∧ vdot v x = r2 ∧ vdot w x = r3)).card = 2 ^ k := by
  let φ : (Fin k → Bool) → Bool × Bool × Bool := fun x => (vdot u x, vdot v x, vdot w x)
  have heq : ∀ p : Bool × Bool × Bool,
      (Finset.univ.filter (fun x : Fin k → Bool => φ x = p)).card =
      (Finset.univ.filter (fun x : Fin k → Bool => φ x = (false, false, false))).card := by
    intro p
    obtain ⟨y, hy⟩ := surj3 u v w hu hv hw huv huw hvw huvw p
    refine Finset.card_bij (fun x _ => vxor x y) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have hx1 : vdot u x = p.1 := by simpa [φ] using congrArg Prod.fst hx
      have hx2 : vdot v x = p.2.1 := by simpa [φ] using congrArg (fun q => q.2.1) hx
      have hx3 : vdot w x = p.2.2 := by simpa [φ] using congrArg (fun q => q.2.2) hx
      have hy1 : vdot u y = p.1 := congrArg Prod.fst hy
      have hy2 : vdot v y = p.2.1 := congrArg (fun q => q.2.1) hy
      have hy3 : vdot w y = p.2.2 := congrArg (fun q => q.2.2) hy
      simp [φ, vdot_xor_right, hx1, hx2, hx3, hy1, hy2, hy3]
    · intro x1 _ x2 _ h
      have := congrArg (fun z => vxor z y) h
      simpa [vxor_cancel_right] using this
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      refine ⟨vxor z y, ?_, vxor_cancel_right z y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hz1 : vdot u z = false := by simpa [φ] using congrArg Prod.fst hz
      have hz2 : vdot v z = false := by simpa [φ] using congrArg (fun q => q.2.1) hz
      have hz3 : vdot w z = false := by simpa [φ] using congrArg (fun q => q.2.2) hz
      have hy1 : vdot u y = p.1 := congrArg Prod.fst hy
      have hy2 : vdot v y = p.2.1 := congrArg (fun q => q.2.1) hy
      have hy3 : vdot w y = p.2.2 := congrArg (fun q => q.2.2) hy
      simp [φ, vdot_xor_right, hz1, hz2, hz3, hy1, hy2, hy3]
  have hpart : (Finset.univ : Finset (Fin k → Bool)).card =
      ∑ p : Bool × Bool × Bool, (Finset.univ.filter (fun x : Fin k → Bool => φ x = p)).card := by
    simpa using (Finset.card_eq_sum_card_fiberwise (f := φ) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _))
  rw [card_vec] at hpart
  have hsum : ∑ p : Bool × Bool × Bool, (Finset.univ.filter (fun x : Fin k → Bool => φ x = p)).card =
      8 * (Finset.univ.filter (fun x : Fin k → Bool => φ x = (false, false, false))).card := by
    simp_rw [heq]
    simp [Finset.sum_const]
  have htarget : (Finset.univ.filter (fun x : Fin k → Bool =>
      vdot u x = r1 ∧ vdot v x = r2 ∧ vdot w x = r3)).card =
      (Finset.univ.filter (fun x : Fin k → Bool => φ x = (r1, r2, r3))).card := by
    have hset : Finset.univ.filter (fun x : Fin k → Bool =>
        vdot u x = r1 ∧ vdot v x = r2 ∧ vdot w x = r3) =
        Finset.univ.filter (fun x : Fin k → Bool => φ x = (r1, r2, r3)) := by
      ext x; simp [φ, Prod.ext_iff]
    rw [hset]
  rw [htarget, heq (r1, r2, r3), ← hsum, ← hpart]

-- Core pair forcing lemma on Fin k → Bool
lemma pair_forced {k tol : ℕ} (hk : 3 ≤ k) (htol : 2 * tol < 2 ^ (k - 3))
    (r off' : (Fin k → Bool) → Bool)
    (a b c d : Fin k → Bool)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hEa : (Finset.univ.filter (fun x =>
        xor (vdot a x) (r a) ≠ xor (vdot b x) (r b) ∧
        xor (vdot a x) (r a) ≠ off' x)).card ≤ tol)
    (hEc : (Finset.univ.filter (fun x =>
        xor (vdot c x) (r c) ≠ xor (vdot d x) (r d) ∧
        xor (vdot c x) (r c) ≠ off' x)).card ≤ tol) :
    vxor a b = vxor c d ∧ xor (r a) (r b) ≠ xor (r c) (r d) := by
  let g := fun (v x : Fin k → Bool) => xor (vdot v x) (r v)
  have hneq_iff : ∀ u v x : Fin k → Bool,
      g u x ≠ g v x ↔ vdot (vxor u v) x = !(xor (r u) (r v)) := by
    intro u v x
    simp only [g, vdot_xor_left]
    have : ∀ a1 a2 b1 b2 : Bool,
        (xor a1 b1 ≠ xor a2 b2) ↔ (xor a1 a2 = !(xor b1 b2)) := by decide
    exact this _ _ _ _
  let Split := Finset.univ.filter (fun x : Fin k → Bool =>
      g a x ≠ g b x ∧ g c x ≠ g d x ∧ g a x ≠ g c x)
  let Ea := Finset.univ.filter (fun x : Fin k → Bool => g a x ≠ g b x ∧ g a x ≠ off' x)
  let Ec := Finset.univ.filter (fun x : Fin k → Bool => g c x ≠ g d x ∧ g c x ≠ off' x)
  have hsub : Split ⊆ Ea ∪ Ec := by
    intro x hx
    simp only [Split, Ea, Ec, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    by_cases h1 : g a x = off' x
    · right; exact ⟨hx.2.1, fun h2 => hx.2.2 (h1.trans h2.symm)⟩
    · left; exact ⟨hx.1, h1⟩
  have hSplit_lt : Split.card < 2 ^ (k - 3) := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le Ea Ec
    have hEa' : Ea.card ≤ tol := hEa
    have hEc' : Ec.card ≤ tol := hEc
    omega
  have hpow : 2 ^ k = 8 * 2 ^ (k - 3) := by
    have : k = (k - 3) + 3 := by omega
    conv_lhs => rw [this, pow_add]
    ring
  set u1 := vxor a b
  set u2 := vxor c d
  set u3 := vxor a c
  have hu1 : u1 ≠ vzero k := fun h => hab ((vxor_eq_zero_iff a b).mp h)
  have hu2 : u2 ≠ vzero k := fun h => hcd ((vxor_eq_zero_iff c d).mp h)
  have hu3 : u3 ≠ vzero k := fun h => hac ((vxor_eq_zero_iff a c).mp h)
  have h13 : u1 ≠ u3 := by
    intro h; apply hbc
    have h' : vxor u1 u3 = vzero k := (vxor_eq_zero_iff u1 u3).mpr h
    have hcalc : vxor u1 u3 = vxor b c := by
      funext i; simp only [u1, u3, vxor]
      have : ∀ x y z : Bool, xor (xor x y) (xor x z) = xor y z := by decide
      exact this _ _ _
    rw [hcalc] at h'; exact (vxor_eq_zero_iff b c).mp h'
  have h23 : u2 ≠ u3 := by
    intro h; apply had
    have h' : vxor u2 u3 = vzero k := (vxor_eq_zero_iff u2 u3).mpr h
    have hcalc : vxor u2 u3 = vxor a d := by
      funext i; simp only [u2, u3, vxor]
      have : ∀ x y z : Bool, xor (xor y z) (xor x y) = xor x z := by decide
      exact this _ _ _
    rw [hcalc] at h'; exact (vxor_eq_zero_iff a d).mp h'
  have h123 : vxor u1 u2 ≠ u3 := by
    intro h; apply hbd
    have h' : vxor (vxor u1 u2) u3 = vzero k := (vxor_eq_zero_iff _ _).mpr h
    have hcalc : vxor (vxor u1 u2) u3 = vxor b d := by
      funext i; simp only [u1, u2, u3, vxor]
      have : ∀ x y z w : Bool, xor (xor (xor x y) (xor z w)) (xor x z) = xor y w := by decide
      exact this _ _ _ _
    rw [hcalc] at h'; exact (vxor_eq_zero_iff b d).mp h'
  have hu12 : u1 = u2 := by
    by_contra h12
    have hS : Split = Finset.univ.filter (fun x : Fin k → Bool =>
        vdot u1 x = !(xor (r a) (r b)) ∧
        vdot u2 x = !(xor (r c) (r d)) ∧
        vdot u3 x = !(xor (r a) (r c))) := by
      ext x; simp only [Split, Finset.mem_filter, Finset.mem_univ, true_and, hneq_iff]; rfl
    have h8 := card_fiber3 u1 u2 u3 hu1 hu2 hu3 h12 h13 h23 h123
      (!(xor (r a) (r b))) (!(xor (r c) (r d))) (!(xor (r a) (r c)))
    rw [← hS] at h8
    omega
  refine ⟨hu12, ?_⟩
  intro hr
  have hS : Split = Finset.univ.filter (fun x : Fin k → Bool =>
      vdot u1 x = !(xor (r a) (r b)) ∧
      vdot u3 x = !(xor (r a) (r c))) := by
    ext x
    simp only [Split, Finset.mem_filter, Finset.mem_univ, true_and, hneq_iff]
    change (vdot u1 x = !(xor (r a) (r b)) ∧ vdot u2 x = !(xor (r c) (r d)) ∧
        vdot u3 x = !(xor (r a) (r c))) ↔ _
    rw [← hu12, hr]
    tauto
  have h4 := card_fiber2 u1 u3 hu1 hu3 h13 (!(xor (r a) (r b))) (!(xor (r a) (r c)))
  rw [← hS] at h4
  omega

-- Weight of a Boolean vector
def wt {k : ℕ} (x : Fin k → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin k => x i = true)).card

lemma wt_eq_zero_iff {k : ℕ} (x : Fin k → Bool) : wt x = 0 ↔ x = vzero k := by
  unfold wt vzero
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h; funext i
    cases hx : x i
    · rfl
    · exact False.elim (h (Finset.mem_univ i) hx)
  · rintro rfl i _; simp

lemma wt_eq_one_iff {k : ℕ} (x : Fin k → Bool) : wt x = 1 ↔ ∃ i : Fin k, x = basis i := by
  unfold wt basis
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    funext j
    have hm : j ∈ Finset.univ.filter (fun t : Fin k => x t = true) ↔ j = i := by
      rw [hi, Finset.mem_singleton]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
    by_cases hji : j = i
    · subst hji; simp [hm.mpr rfl]
    · simp only [hji, decide_false]
      cases hx : x j
      · rfl
      · exact False.elim (hji (hm.mp hx))
  · rintro ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    ext j; simp

lemma wt_flip_true {k : ℕ} (x : Fin k → Bool) (i : Fin k) (hi : x i = true) :
    wt (vxor x (basis i)) + 1 = wt x := by
  unfold wt
  have hsub : Finset.univ.filter (fun j : Fin k => vxor x (basis i) j = true) =
      (Finset.univ.filter (fun j : Fin k => x j = true)).erase i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, vxor, basis]
    by_cases hji : j = i
    · subst hji; simp [hi]
    · simp [hji]
  rw [hsub]
  have hmem : i ∈ Finset.univ.filter (fun j : Fin k => x j = true) := by simp [hi]
  exact Finset.card_erase_add_one hmem

lemma nonaffine_quad {k : ℕ} (r : (Fin k → Bool) → Bool)
    (hnot : ¬ ∃ (h : Bool) (u : Fin k → Bool), ∀ v, r v = xor h (vdot u v)) :
    ∃ (a b c d : Fin k → Bool),
      a ≠ b ∧ c ≠ d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
      vxor a b = vxor c d ∧ xor (r a) (r b) ≠ xor (r c) (r d) := by
  let h0 : Bool := r (vzero k)
  let u0 : Fin k → Bool := fun i => xor h0 (r (basis i))
  let aff : (Fin k → Bool) → Bool := fun x => xor h0 (vdot u0 x)
  have haff0 : aff (vzero k) = r (vzero k) := by
    simp [aff, h0, vdot_zero_right]
  have haff_basis : ∀ i : Fin k, aff (basis i) = r (basis i) := by
    intro i
    simp only [aff, u0, vdot_basis_right]
    have : ∀ a b : Bool, xor a (xor a b) = b := by decide
    exact this _ _
  let bad := Finset.univ.filter (fun x : Fin k → Bool => r x ≠ aff x)
  have hne : bad.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hnot
    refine ⟨h0, u0, fun v => ?_⟩
    by_contra hdiff
    have hv : v ∈ bad := by
      simp only [bad, aff, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hdiff
    rw [hemp] at hv; exact Finset.notMem_empty v hv
  obtain ⟨x, hxbad, hxmin⟩ := Finset.exists_min_image bad wt hne
  have hrx : r x ≠ aff x := (Finset.mem_filter.mp hxbad).2
  have hwt0 : wt x ≠ 0 := by
    intro h0'; rw [wt_eq_zero_iff] at h0'; subst h0'; exact hrx haff0.symm
  have hwt1 : wt x ≠ 1 := by
    intro h1'; obtain ⟨i, rfl⟩ := (wt_eq_one_iff x).mp h1'; exact hrx (haff_basis i).symm
  have hwt2 : 2 ≤ wt x := by omega
  have hex_i : ∃ i : Fin k, x i = true := by
    have hpos : 0 < (Finset.univ.filter (fun i : Fin k => x i = true)).card := by
      dsimp [wt] at hwt2; omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  obtain ⟨i, hi⟩ := hex_i
  let y := basis i
  let z := vxor x y
  have hwtz : wt z + 1 = wt x := wt_flip_true x i hi
  have hrz : r z = aff z := by
    by_contra hne_z
    have hzbad : z ∈ bad := by simp [bad, hne_z]
    have hle := hxmin z hzbad
    omega
  have hyi : y i = true := by simp [y, basis]
  have hzi : z i = false := by simp [z, vxor, hi, hyi]
  have h0i : vzero k i = false := rfl
  have h0y : vzero k ≠ y := fun h => by have := congrFun h i; rw [h0i, hyi] at this; exact Bool.noConfusion this
  have hzx : z ≠ x := fun h => by have := congrFun h i; rw [hzi, hi] at this; exact Bool.noConfusion this
  have h0z : vzero k ≠ z := fun h => by
    have hwz0 : wt z = 0 := (wt_eq_zero_iff z).mpr h.symm
    omega
  have h0x : vzero k ≠ x := fun h => by have := congrFun h i; rw [h0i, hi] at this; exact Bool.noConfusion this
  have hyz : y ≠ z := fun h => by have := congrFun h i; rw [hyi, hzi] at this; exact Bool.noConfusion this
  have hyx : y ≠ x := fun h => by
    have hwy : wt y = 1 := (wt_eq_one_iff y).mpr ⟨i, rfl⟩
    rw [h] at hwy; omega
  have hdir : vxor (vzero k) y = vxor z x := by
    rw [vxor_zero_left]
    funext j; simp only [z, vxor]
    have : ∀ a b : Bool, b = xor (xor a b) a := by decide
    exact this _ _
  have hderiv : xor (r (vzero k)) (r y) ≠ xor (r z) (r x) := by
    rw [← haff0, ← haff_basis i, hrz]
    have haff_eq : xor (aff (vzero k)) (aff y) = xor (aff z) (aff x) := by
      simp only [aff]
      have h1 : ∀ h a b : Bool, xor (xor h a) (xor h b) = xor a b := by decide
      rw [h1, h1, ← vdot_xor_right, ← vdot_xor_right, hdir]
    rw [haff_eq]
    intro heq
    apply hrx
    have : ∀ a b c : Bool, xor a b = xor a c → b = c := by decide
    exact (this (aff z) (aff x) (r x) heq).symm
  exact ⟨vzero k, y, z, x, h0y, hzx, h0z, h0x, hyz, hyx, hdir, hderiv⟩

end PEqualNP.Outside.L_lib_716

open PEqualNP.Outside.L_lib_716 in
theorem PEqualNP.Outside.L_lib_716 : ∀ (k tol : ℕ) (rowFlip colFlip : Fin (2^k) → Bool), 3 ≤ k → 2*tol < 2^(k-3) →
  let N := 2 ^ k
  let bits := fun (v : Fin N) =>
    (Finset.univ : Finset (Fin k)).filter (fun i => v.val.testBit i.val)
  let dot := fun (u v : Fin N) => ((bits u ∩ bits v).card % 2 == 1)
  let G := fun (u v : Fin N) => (dot u v != rowFlip u) != colFlip v
  let good := fun (T : Fin N → Fin N → Bool) (off : Fin N → Bool)
      (F : Finset (Fin N × Fin N)) =>
    (∀ e ∈ F, e.1 ≠ e.2 ∧
      (Finset.univ.filter (fun j => T e.1 j ≠ T e.2 j ∧ T e.1 j ≠ off j)).card ≤ tol) ∧
    (∀ e ∈ F, ∀ f ∈ F, e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2)
  let affine := ∃ (h : Bool) (u : Fin N), ∀ v : Fin N, rowFlip v = (h != dot u v)
  let price := if affine then 1 else 2
  (∀ (off : Fin N → Bool) (F : Finset (Fin N × Fin N)), good G off F → F.card ≤ price) ∧
  ∃ (off : Fin N → Bool) (F : Finset (Fin N × Fin N)), good G off F ∧ F.card = price := by
  intro k tol rowFlip colFlip hk htol
  intro N bits dot G good affine price
  let r : (Fin k → Bool) → Bool := fun x => rowFlip (ofVec x)
  have hdot_eq : ∀ u v : Fin N, dot u v = vdot (toVec u) (toVec v) := fun u v => vdot_eq_dot u v
  have hG_eq : ∀ u v : Fin N, G u v = xor (xor (vdot (toVec u) (toVec v)) (r (toVec u))) (colFlip v) := by
    intro u v
    simp only [G, r, ofVec_toVec, hdot_eq]
  have haff_iff : affine ↔ ∃ (h : Bool) (u : Fin k → Bool), ∀ v, r v = xor h (vdot u v) := by
    constructor
    · rintro ⟨h, u, hu⟩
      refine ⟨h, toVec u, fun v => ?_⟩
      have hv := hu (ofVec v)
      simp only [r, hdot_eq, toVec_ofVec] at hv ⊢
      simpa [bne] using hv
    · rintro ⟨h, u, hu⟩
      refine ⟨h, ofVec u, fun v => ?_⟩
      have hv := hu (toVec v)
      simp only [r, ofVec_toVec, hdot_eq, toVec_ofVec] at hv ⊢
      simpa [bne] using hv
  have herr_transport : ∀ (off : Fin N → Bool) (u v : Fin N),
      (Finset.univ.filter (fun x : Fin k → Bool =>
        xor (vdot (toVec u) x) (r (toVec u)) ≠ xor (vdot (toVec v) x) (r (toVec v)) ∧
        xor (vdot (toVec u) x) (r (toVec u)) ≠ xor (off (ofVec x)) (colFlip (ofVec x)))).card =
      (Finset.univ.filter (fun j : Fin N => G u j ≠ G v j ∧ G u j ≠ off j)).card := by
    intro off u v
    refine Finset.card_bij (fun x _ => ofVec x) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [hG_eq, hG_eq, toVec_ofVec]
      constructor
      · intro heq; apply hx.1
        have : ∀ a b c : Bool, xor a c = xor b c → a = b := by decide
        exact this _ _ _ heq
      · intro heq; apply hx.2
        have : ∀ a b c : Bool, xor a c = b → a = xor b c := by decide
        exact this _ _ _ heq
    · intro x1 _ x2 _ h
      have := congrArg toVec h
      simpa [toVec_ofVec] using this
    · intro j hj
      refine ⟨toVec j, ?_, ofVec_toVec j⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      rw [hG_eq, hG_eq] at hj
      rw [ofVec_toVec]
      constructor
      · intro heq; apply hj.1; rw [heq]
      · intro heq; apply hj.2
        have : ∀ a b c : Bool, a = xor b c → xor a c = b := by decide
        exact this _ _ _ heq
  have hpair : ∀ (off : Fin N → Bool) (F : Finset (Fin N × Fin N)), good G off F →
      ∀ e ∈ F, ∀ f ∈ F, e ≠ f →
        vxor (toVec e.1) (toVec e.2) = vxor (toVec f.1) (toVec f.2) ∧
        xor (rowFlip e.1) (rowFlip e.2) ≠ xor (rowFlip f.1) (rowFlip f.2) := by
    intro off F hgood e he f hf hef
    have he1 := hgood.1 e he
    have hf1 := hgood.1 f hf
    have hdisj := hgood.2 e he f hf hef
    have hinj : Function.Injective (toVec (k := k)) := (toVecEquiv k).injective
    let off' : (Fin k → Bool) → Bool := fun x => xor (off (ofVec x)) (colFlip (ofVec x))
    have hEa : (Finset.univ.filter (fun x : Fin k → Bool =>
        xor (vdot (toVec e.1) x) (r (toVec e.1)) ≠ xor (vdot (toVec e.2) x) (r (toVec e.2)) ∧
        xor (vdot (toVec e.1) x) (r (toVec e.1)) ≠ off' x)).card ≤ tol := by
      rw [herr_transport off e.1 e.2]; exact he1.2
    have hEc : (Finset.univ.filter (fun x : Fin k → Bool =>
        xor (vdot (toVec f.1) x) (r (toVec f.1)) ≠ xor (vdot (toVec f.2) x) (r (toVec f.2)) ∧
        xor (vdot (toVec f.1) x) (r (toVec f.1)) ≠ off' x)).card ≤ tol := by
      rw [herr_transport off f.1 f.2]; exact hf1.2
    have hres := pair_forced hk htol r off'
      (toVec e.1) (toVec e.2) (toVec f.1) (toVec f.2)
      (fun h => he1.1 (hinj h)) (fun h => hf1.1 (hinj h))
      (fun h => hdisj.1 (hinj h)) (fun h => hdisj.2.1 (hinj h))
      (fun h => hdisj.2.2.1 (hinj h)) (fun h => hdisj.2.2.2 (hinj h))
      hEa hEc
    simpa [r, ofVec_toVec] using hres
  constructor
  · -- Upper bound: F.card ≤ price
    intro off F hgood
    by_cases haff : affine
    · simp only [price, if_pos haff]
      obtain ⟨h, u, hu⟩ := haff_iff.mp haff
      refine Finset.card_le_one.mpr fun e he f hf => ?_
      by_contra hef
      obtain ⟨hdir, hneq⟩ := hpair off F hgood e he f hf hef
      apply hneq
      have hr_eq : ∀ v : Fin N, rowFlip v = xor h (vdot u (toVec v)) := fun v => by
        have := hu (toVec v); simpa [r, ofVec_toVec] using this
      rw [hr_eq, hr_eq, hr_eq, hr_eq]
      have hcancel : ∀ a b c : Bool, xor (xor a b) (xor a c) = xor b c := by decide
      rw [hcancel, hcancel, ← vdot_xor_right, ← vdot_xor_right, hdir]
    · simp only [price, if_neg haff]
      let ψ : Fin N × Fin N → Bool := fun e => xor (rowFlip e.1) (rowFlip e.2)
      have hinj : Set.InjOn ψ F := by
        intro e he f hf hψ
        by_contra hef
        exact (hpair off F hgood e he f hf hef).2 hψ
      calc F.card = (F.image ψ).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.univ : Finset Bool).card := Finset.card_le_univ _
        _ = 2 := by decide
  · -- Witness achieving F.card = price
    by_cases haff : affine
    · simp only [price, if_pos haff]
      have hN2 : 2 ≤ N := by
        have h8 : 8 ≤ 2 ^ k := by
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
        dsimp only [N]; omega
      let a0 : Fin N := ⟨0, by omega⟩
      let b0 : Fin N := ⟨1, by omega⟩
      refine ⟨fun j => G a0 j, {(a0, b0)}, ⟨?_, ?_⟩, Finset.card_singleton _⟩
      · intro e he
        rw [Finset.mem_singleton] at he; subst he
        refine ⟨by intro h; have := congrArg Fin.val h; simp [a0, b0] at this, ?_⟩
        have hemp : (Finset.univ.filter (fun j : Fin N => G a0 j ≠ G b0 j ∧ G a0 j ≠ G a0 j)) = ∅ := by
          ext j; simp
        rw [hemp]; simp
      · intro e he f hf hef
        rw [Finset.mem_singleton] at he hf; exact False.elim (hef (he.trans hf.symm))
    · simp only [price, if_neg haff]
      have hnot : ¬ ∃ (h : Bool) (u : Fin k → Bool), ∀ v, r v = xor h (vdot u v) :=
        fun h => haff (haff_iff.mpr h)
      obtain ⟨a, b, c, d, hab, hcd, hac, had, hbc, hbd, hdir, hderiv⟩ := nonaffine_quad r hnot
      let a0 := ofVec a
      let b0 := ofVec b
      let c0 := ofVec c
      let d0 := ofVec d
      have hinj : Function.Injective (ofVec (k := k)) := (toVecEquiv k).symm.injective
      have ha0b0 : a0 ≠ b0 := fun h => hab (hinj h)
      have hc0d0 : c0 ≠ d0 := fun h => hcd (hinj h)
      have ha0c0 : a0 ≠ c0 := fun h => hac (hinj h)
      have ha0d0 : a0 ≠ d0 := fun h => had (hinj h)
      have hb0c0 : b0 ≠ c0 := fun h => hbc (hinj h)
      have hb0d0 : b0 ≠ d0 := fun h => hbd (hinj h)
      have hne_pair : (a0, b0) ≠ (c0, d0) := fun h => ha0c0 (congrArg Prod.fst h)
      let off : Fin N → Bool := fun j => if G a0 j ≠ G b0 j then G a0 j else G c0 j
      refine ⟨off, {(a0, b0), (c0, d0)}, ⟨?_, ?_⟩, Finset.card_pair hne_pair⟩
      · intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · refine ⟨ha0b0, ?_⟩
          have hemp : (Finset.univ.filter (fun j : Fin N => G a0 j ≠ G b0 j ∧ G a0 j ≠ off j)) = ∅ := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, off]
            rintro ⟨h1, h2⟩
            rw [if_pos h1] at h2
            exact h2 rfl
          rw [hemp]; simp
        · refine ⟨hc0d0, ?_⟩
          have hemp : (Finset.univ.filter (fun j : Fin N => G c0 j ≠ G d0 j ∧ G c0 j ≠ off j)) = ∅ := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, off]
            rintro ⟨h1, h2⟩
            have hnot1 : ¬ (G a0 j ≠ G b0 j) := by
              intro habj
              rw [hG_eq, hG_eq, toVec_ofVec, toVec_ofVec] at habj h1
              have hcancel : ∀ x1 x2 y1 y2 z : Bool,
                  xor (xor x1 y1) z ≠ xor (xor x2 y2) z → xor x1 x2 = !(xor y1 y2) := by decide
              have eq1 := hcancel _ _ _ _ _ habj
              have eq2 := hcancel _ _ _ _ _ h1
              rw [← vdot_xor_left] at eq1 eq2
              rw [hdir] at eq1
              have eq3 := eq1.symm.trans eq2
              have : ∀ x y : Bool, (!x) = (!y) → x = y := by decide
              exact hderiv (this _ _ eq3)
            rw [if_neg hnot1] at h2
            exact h2 rfl
          rw [hemp]; simp
      · intro e he f hf hef
        simp only [Finset.mem_insert, Finset.mem_singleton] at he hf
        rcases he with rfl | rfl <;> rcases hf with rfl | rfl
        · exact False.elim (hef rfl)
        · exact ⟨ha0c0, ha0d0, hb0c0, hb0d0⟩
        · exact ⟨ha0c0.symm, hb0c0.symm, ha0d0.symm, hb0d0.symm⟩
        · exact False.elim (hef rfl)

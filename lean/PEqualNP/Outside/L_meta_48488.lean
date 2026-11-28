import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48488

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def fullMask : Nat := 0xffffffffffffffff

abbrev Masked (mask w : Nat) : Prop := w &&& mask = w

def bsel {α : Type} (c : Bool) (t f : α) : α := Bool.rec f t c

theorem bsel_true {α : Type} (t f : α) : bsel true t f = t := rfl
theorem bsel_false {α : Type} (t f : α) : bsel false t f = f := rfl

theorem beq_false_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem ne_of_beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro e; subst e; rw [Nat.beq_refl] at h; exact Bool.noConfusion h

theorem masked_self (mask : Nat) : Masked mask mask := by
  unfold Masked; simp

theorem masked_land_right (mask w : Nat) : Masked mask (w &&& mask) := by
  unfold Masked; apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and]

theorem xor_cancel_left (mask v : Nat) : mask ^^^ (mask ^^^ v) = v := by
  apply Nat.eq_of_testBit_eq; intro i; simp

theorem masked_sub_and {mask cut w : Nat} (sub : mask &&& cut = cut) :
    (w &&& mask) &&& cut = w &&& cut := by
  apply Nat.eq_of_testBit_eq; intro i
  have es := congrArg (fun x => x.testBit i) sub
  simp only [Nat.testBit_and] at es ⊢
  cases hc : cut.testBit i <;> simp_all

theorem masked_sub_xor {mask cut w : Nat} (sub : mask &&& cut = cut) :
    (mask ^^^ w) &&& cut = cut ^^^ (w &&& cut) := by
  apply Nat.eq_of_testBit_eq; intro i
  have es := congrArg (fun x => x.testBit i) sub
  simp only [Nat.testBit_and, Nat.testBit_xor] at es ⊢
  cases hc : cut.testBit i <;> simp_all

def canon (mask w : Nat) : Nat :=
  let v := w &&& mask
  bsel (Nat.beq v 0 || Nat.beq v mask) 0
    (let iv := mask ^^^ v; bsel (Nat.blt v iv) v iv)

theorem canon_zero (mask : Nat) : canon mask 0 = 0 := by
  unfold canon; simp [bsel]

theorem canon_self (mask : Nat) : canon mask mask = 0 := by
  unfold canon; simp [bsel]

theorem canon_land (mask w : Nat) : canon mask (w &&& mask) = canon mask w := by
  unfold canon; dsimp only; rw [masked_land_right mask w]

theorem canon_cases (mask w : Nat) :
    (canon mask w = 0 ∧ (w &&& mask = 0 ∨ w &&& mask = mask)) ∨
    (canon mask w ≠ 0 ∧ (canon mask w = w &&& mask ∨ canon mask w = mask ^^^ (w &&& mask))) := by
  unfold canon; dsimp only
  set v := w &&& mask
  by_cases hv0 : v = 0
  · left; rw [hv0]; simp [bsel]
  · by_cases hvm : v = mask
    · left; rw [hvm]; simp [bsel]
    · right
      rw [beq_false_ne hv0, beq_false_ne hvm]
      simp only [Bool.or_false, bsel_false]
      cases hlt : Nat.blt v (mask ^^^ v)
      · rw [bsel_false]
        refine ⟨?_, Or.inr rfl⟩
        intro hz
        have e := congrArg (fun x => mask ^^^ x) hz
        rw [xor_cancel_left] at e
        exact hvm (by simpa using e)
      · rw [bsel_true]; exact ⟨hv0, Or.inl rfl⟩

theorem canon_xor_mask (mask w : Nat) : canon mask (mask ^^^ w) = canon mask w := by
  have hsub : (mask ^^^ w) &&& mask = mask ^^^ (w &&& mask) := masked_sub_xor (masked_self mask)
  unfold canon; dsimp only
  rw [hsub]
  generalize hv : w &&& mask = v
  set iv := mask ^^^ v
  have hiv : mask ^^^ iv = v := xor_cancel_left mask v
  rw [hiv]
  by_cases hv0 : v = 0
  · have hivm : iv = mask := by simp [iv, hv0]
    rw [hv0, hivm]; simp [bsel]
  · by_cases hvm : v = mask
    · have hiv0 : iv = 0 := by simp [iv, hvm]
      rw [hvm, hiv0]; simp [bsel]
    · have hiv0 : iv ≠ 0 := by
        intro h; apply hvm
        have e := congrArg (fun x => mask ^^^ x) h
        rw [hiv] at e; simpa using e
      have hivm : iv ≠ mask := by
        intro h; apply hv0
        have e := congrArg (fun x => mask ^^^ x) h
        rw [hiv] at e; simpa using e
      rw [beq_false_ne hv0, beq_false_ne hvm, beq_false_ne hiv0, beq_false_ne hivm]
      simp only [Bool.or_false, bsel_false]
      have hne : v ≠ iv := by
        intro h
        have hm0 : mask = 0 := by
          apply Nat.eq_of_testBit_eq; intro i
          have ei := congrArg (fun x => x.testBit i) h
          simp only [iv, Nat.testBit_xor] at ei
          cases hv' : v.testBit i <;> cases hm' : mask.testBit i <;> simp_all
        have : v = 0 := by rw [← hv, hm0]; simp
        exact hv0 this
      by_cases hlt : v < iv
      · have h1 : Nat.blt v iv = true := Nat.blt_eq.mpr hlt
        have h2 : Nat.blt iv v = false := by cases h : Nat.blt iv v; rfl; have := Nat.blt_eq.mp h; omega
        rw [h1, h2, bsel_true, bsel_false]
      · have hgt : iv < v := by omega
        have h1 : Nat.blt v iv = false := by cases h : Nat.blt v iv; rfl; have := Nat.blt_eq.mp h; omega
        have h2 : Nat.blt iv v = true := Nat.blt_eq.mpr hgt
        rw [h1, h2, bsel_false, bsel_true]

theorem canon_idem (mask w : Nat) : canon mask (canon mask w) = canon mask w := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · rw [h0, canon_zero]
  · calc canon mask (canon mask w) = canon mask (w &&& mask) := by rw [h1]
      _ = canon mask w := canon_land mask w
  · calc canon mask (canon mask w) = canon mask (mask ^^^ (w &&& mask)) := by rw [h2]
      _ = canon mask (w &&& mask) := canon_xor_mask mask (w &&& mask)
      _ = canon mask w := canon_land mask w

theorem canon_submask {mask cut w : Nat} (sub : mask &&& cut = cut) (hc : canon mask w ≠ 0) :
    canon cut (canon mask w) = canon cut w := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · exact absurd h0 hc
  · rw [h1, ← canon_land cut (w &&& mask), masked_sub_and sub, canon_land]
  · rw [h2, ← canon_land cut (mask ^^^ (w &&& mask)), masked_sub_xor sub, masked_sub_and sub]
    rw [← masked_sub_xor (masked_self cut), canon_land, canon_xor_mask]

theorem canon_submask_zero {mask cut w : Nat} (sub : mask &&& cut = cut) (hc : canon mask w = 0) :
    canon cut w = 0 := by
  rcases canon_cases mask w with ⟨_, h0 | hm⟩ | ⟨hne, _⟩
  · rw [← canon_land cut w, ← masked_sub_and sub, h0]; simp [canon_zero]
  · rw [← canon_land cut w, ← masked_sub_and sub, hm, sub, canon_self]
  · exact absurd hc hne

theorem canon_testBit_eq {mask w p n : Nat} (hp : mask.testBit p = true) (hn : mask.testBit n = true) :
    ((canon mask w).testBit p = (canon mask w).testBit n) ↔ (w.testBit p = w.testBit n) := by
  rcases canon_cases mask w with ⟨h0, h1 | h2⟩ | ⟨_, h1 | h2⟩
  · rw [h0]
    have e1 := congrArg (fun x => x.testBit p) h1
    have e2 := congrArg (fun x => x.testBit n) h1
    simp [Nat.testBit_and, hp, hn] at e1 e2 ⊢; simp [e1, e2]
  · rw [h0]
    have e1 := congrArg (fun x => x.testBit p) h2
    have e2 := congrArg (fun x => x.testBit n) h2
    simp [Nat.testBit_and, hp, hn] at e1 e2 ⊢; simp [e1, e2]
  · rw [h1]; simp [Nat.testBit_and, hp, hn]
  · rw [h2]; simp [Nat.testBit_xor, Nat.testBit_and, hp, hn]

def binOp (mask op a b : Nat) : Nat :=
  bsel (Nat.beq op 0) (canon mask (a &&& b))
    (bsel (Nat.beq op 1) (canon mask (a ||| b))
      (bsel (Nat.beq op 2) (canon mask (a &&& (mask ^^^ b)))
        (canon mask ((mask ^^^ a) &&& b))))

theorem binOp_canon (mask op a b : Nat) : canon mask (binOp mask op a b) = binOp mask op a b := by
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false] <;> exact canon_idem mask _

theorem binOp_comm (mask op a b : Nat) (hop : op < 4) :
    ∃ op' < 4, binOp mask op a b = binOp mask op' b a := by
  have hland : a &&& b = b &&& a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  have hlor : a ||| b = b ||| a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_or, Bool.or_comm]
  have h23 : a &&& (mask ^^^ b) = (mask ^^^ b) &&& a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  have h32 : (mask ^^^ a) &&& b = b &&& (mask ^^^ a) := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  rcases (show op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 by omega) with rfl | rfl | rfl | rfl
  · exact ⟨0, by omega, by change canon mask (a &&& b) = canon mask (b &&& a); rw [hland]⟩
  · exact ⟨1, by omega, by change canon mask (a ||| b) = canon mask (b ||| a); rw [hlor]⟩
  · exact ⟨3, by omega, by change canon mask (a &&& (mask ^^^ b)) = canon mask ((mask ^^^ b) &&& a); rw [h23]⟩
  · exact ⟨2, by omega, by change canon mask ((mask ^^^ a) &&& b) = canon mask (b &&& (mask ^^^ a)); rw [h32]⟩

theorem binOp_zero_left (mask op b : Nat) : binOp mask op 0 b = 0 ∨ binOp mask op 0 b = canon mask b := by
  unfold binOp
  have hmb : (mask ^^^ 0) &&& b = b &&& mask := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · right; rw [hmb, canon_land]
  · left; simp [canon_zero]
  · right; simp
  · right; simp
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]

theorem binOp_zero_right (mask op a : Nat) : binOp mask op a 0 = 0 ∨ binOp mask op a 0 = canon mask a := by
  unfold binOp
  have hma : a &&& (mask ^^^ 0) = a &&& mask := by simp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · left; simp [canon_zero]
  · right; rw [hma, canon_land]
  · right; simp
  · right; simp
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]

theorem binOp_self (mask op a : Nat) : binOp mask op a a = 0 ∨ binOp mask op a a = canon mask a := by
  have h2 : canon mask (a &&& (mask ^^^ a)) = 0 := by
    rw [← canon_land]
    have : (a &&& (mask ^^^ a)) &&& mask = 0 := by
      apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
      cases a.testBit i <;> cases mask.testBit i <;> rfl
    rw [this, canon_zero]
  have h3 : canon mask ((mask ^^^ a) &&& a) = 0 := by
    rw [← canon_land]
    have : ((mask ^^^ a) &&& a) &&& mask = 0 := by
      apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
      cases a.testBit i <;> cases mask.testBit i <;> rfl
    rw [this, canon_zero]
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · left; exact h3
  · left; exact h2
  · right; simp
  · right; simp
  · right; simp
  · right; simp
  · right; simp
  · right; simp

theorem deMorgan_or_mask {mask a b : Nat} (ha : Masked mask a) (hb : Masked mask b) :
    mask ^^^ (a &&& b) = (mask ^^^ a) ||| (mask ^^^ b) := by
  unfold Masked at ha hb
  apply Nat.eq_of_testBit_eq; intro i
  have ea := congrArg (fun x => x.testBit i) ha
  have eb := congrArg (fun x => x.testBit i) hb
  simp only [Nat.testBit_and] at ea eb
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
  cases hm : mask.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all

theorem canon_and_in_binOp (mask x y : Nat) :
    canon mask (x &&& y) = 0 ∨
    canon mask (x &&& y) = canon mask x ∨
    canon mask (x &&& y) = canon mask y ∨
    ∃ op < 4, canon mask (x &&& y) = binOp mask op (canon mask x) (canon mask y) := by
  have hxy : canon mask (x &&& y) = canon mask ((x &&& mask) &&& (y &&& mask)) := by
    rw [← canon_land mask (x &&& y), ← canon_land mask ((x &&& mask) &&& (y &&& mask))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and]
    cases x.testBit i <;> cases y.testBit i <;> cases mask.testBit i <;> rfl
  rw [hxy]
  have hvxm : Masked mask (x &&& mask) := masked_land_right mask x
  have hvym : Masked mask (y &&& mask) := masked_land_right mask y
  rcases canon_cases mask x with ⟨hx0, hx1 | hx2⟩ | ⟨_, hx1 | hx2⟩
  · left; rw [hx1]; simp [canon_zero]
  · right; right; left; rw [hx2]
    have : mask &&& (y &&& mask) = y &&& mask := by
      apply Nat.eq_of_testBit_eq; intro i
      have e := congrArg (fun t => t.testBit i) hvym
      simp only [Nat.testBit_and] at e ⊢; rw [Bool.and_comm]; exact e
    rw [this, canon_land]
  · rcases canon_cases mask y with ⟨hy0, hy1 | hy2⟩ | ⟨_, hy1 | hy2⟩
    · left; rw [hy1]; simp [canon_zero]
    · right; left; rw [hy2, hvxm, canon_land]
    · right; right; right; refine ⟨0, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x &&& canon mask y)
      rw [hx1, hy1]
    · right; right; right; refine ⟨2, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x &&& (mask ^^^ canon mask y))
      rw [hx1, hy2, xor_cancel_left]
  · rcases canon_cases mask y with ⟨hy0, hy1 | hy2⟩ | ⟨_, hy1 | hy2⟩
    · left; rw [hy1]; simp [canon_zero]
    · right; left; rw [hy2, hvxm, canon_land]
    · right; right; right; refine ⟨3, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask ((mask ^^^ canon mask x) &&& canon mask y)
      rw [hx2, hy1, xor_cancel_left]
    · right; right; right; refine ⟨1, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x ||| canon mask y)
      rw [hx2, hy2, ← deMorgan_or_mask hvxm hvym, canon_xor_mask]

theorem canon_or_in_binOp (mask x y : Nat) :
    canon mask (x ||| y) = 0 ∨
    canon mask (x ||| y) = canon mask x ∨
    canon mask (x ||| y) = canon mask y ∨
    ∃ op < 4, canon mask (x ||| y) = binOp mask op (canon mask x) (canon mask y) := by
  have hxy : canon mask (x ||| y) = canon mask ((mask ^^^ x) &&& (mask ^^^ y)) := by
    rw [← canon_xor_mask mask (x ||| y), ← canon_land mask (mask ^^^ (x ||| y))]
    rw [← canon_land mask ((mask ^^^ x) &&& (mask ^^^ y))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
    cases mask.testBit i <;> cases x.testBit i <;> cases y.testBit i <;> rfl
  rw [hxy]
  have h := canon_and_in_binOp mask (mask ^^^ x) (mask ^^^ y)
  rwa [canon_xor_mask, canon_xor_mask] at h

theorem canon_sub_binOp {mask cut op a b : Nat} (sub : mask &&& cut = cut) :
    canon cut (binOp mask op a b) = 0 ∨
    canon cut (binOp mask op a b) = canon cut a ∨
    canon cut (binOp mask op a b) = canon cut b ∨
    ∃ op' < 4, canon cut (binOp mask op a b) = binOp cut op' (canon cut a) (canon cut b) := by
  have go (u : Nat) : canon cut (canon mask u) = canon cut u := by
    by_cases h : canon mask u = 0
    · rw [h, canon_zero, (canon_submask_zero sub h).symm]
    · exact canon_submask sub h
  have hmx1 : canon cut ((mask ^^^ a) &&& b) = canon cut ((cut ^^^ a) &&& b) := by
    rw [← canon_land cut ((mask ^^^ a) &&& b), ← canon_land cut ((cut ^^^ a) &&& b)]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    have es := congrArg (fun t => t.testBit i) sub
    simp only [Nat.testBit_and] at es
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases hc : cut.testBit i
    · simp
    · simp only [hc, Bool.and_true] at es ⊢; rw [es]
  have hmx2 : canon cut (a &&& (mask ^^^ b)) = canon cut (a &&& (cut ^^^ b)) := by
    rw [← canon_land cut (a &&& (mask ^^^ b)), ← canon_land cut (a &&& (cut ^^^ b))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    have es := congrArg (fun t => t.testBit i) sub
    simp only [Nat.testBit_and] at es
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases hc : cut.testBit i
    · simp
    · simp only [hc, Bool.and_true] at es ⊢; rw [es]
  have hsub_case1 : canon cut ((cut ^^^ a) &&& b) = 0 ∨ canon cut ((cut ^^^ a) &&& b) = canon cut a ∨
      canon cut ((cut ^^^ a) &&& b) = canon cut b ∨
      ∃ op' < 4, canon cut ((cut ^^^ a) &&& b) = binOp cut op' (canon cut a) (canon cut b) := by
    have h := canon_and_in_binOp cut (cut ^^^ a) b
    rwa [canon_xor_mask] at h
  have hsub_case2 : canon cut (a &&& (cut ^^^ b)) = 0 ∨ canon cut (a &&& (cut ^^^ b)) = canon cut a ∨
      canon cut (a &&& (cut ^^^ b)) = canon cut b ∨
      ∃ op' < 4, canon cut (a &&& (cut ^^^ b)) = binOp cut op' (canon cut a) (canon cut b) := by
    have h := canon_and_in_binOp cut a (cut ^^^ b)
    rwa [canon_xor_mask] at h
  have hbin_eq : binOp mask op a b = canon mask (a &&& b) ∨ binOp mask op a b = canon mask (a ||| b) ∨
      binOp mask op a b = canon mask (a &&& (mask ^^^ b)) ∨ binOp mask op a b = canon mask ((mask ^^^ a) &&& b) := by
    unfold binOp
    cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp [bsel]
  rcases hbin_eq with h | h | h | h <;> rw [h, go]
  · exact canon_and_in_binOp cut a b
  · exact canon_or_in_binOp cut a b
  · rw [hmx2]; exact hsub_case2
  · rw [hmx1]; exact hsub_case1

def Avail (bank : List Nat) (w : Nat) : Prop := w = 0 ∨ w ∈ bank

def GateBin (mask : Nat) (bank : List Nat) (v : Nat) : Prop :=
  ∃ a b op, op < 4 ∧ Avail bank a ∧ Avail bank b ∧ v = binOp mask op a b

def BuildsBin (mask : Nat) (bank : List Nat) : List Nat → Prop
  | [] => True
  | v :: vs => GateBin mask bank v ∧ BuildsBin mask (v :: bank) vs

def LowerBin (mask : Nat) (stock : List Nat) (goal m : Nat) : Prop :=
  ∀ vs, BuildsBin mask stock vs → Avail (vs ++ stock) goal → m ≤ vs.length

theorem avail_weaken {b1 b2 : List Nat} (sub : ∀ w ∈ b1, w ∈ b2) {w : Nat} (h : Avail b1 w) :
    Avail b2 w := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (sub w h)

theorem gate_weaken {mask : Nat} {b1 b2 : List Nat} (sub : ∀ w ∈ b1, w ∈ b2) {v : Nat}
    (h : GateBin mask b1 v) : GateBin mask b2 v := by
  obtain ⟨a, b, op, hop, ha, hb, hv⟩ := h
  exact ⟨a, b, op, hop, avail_weaken sub ha, avail_weaken sub hb, hv⟩

theorem builds_weaken {mask : Nat} {b1 b2 vs : List Nat} (sub : ∀ w ∈ b1, w ∈ b2)
    (h : BuildsBin mask b1 vs) : BuildsBin mask b2 vs := by
  induction vs generalizing b1 b2 with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gate_weaken sub h.1, ih ?_ h.2⟩
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (sub w hw)

theorem builds_append {mask : Nat} {roots first second : List Nat}
    (h1 : BuildsBin mask roots first) (h2 : BuildsBin mask (first ++ roots) second) :
    BuildsBin mask roots (first ++ second) := by
  induction first generalizing roots with
  | nil => exact h2
  | cons v vs ih =>
    refine ⟨h1.1, ih h1.2 ?_⟩
    exact builds_weaken (fun w hw => by simp only [List.mem_append, List.mem_cons] at hw ⊢; tauto) h2

def dropIf (drop : Bool) (x : Nat) (S : Finset Nat) : Finset Nat :=
  if drop then S.erase x else S

theorem dropIf_subset (drop : Bool) (x : Nat) (S : Finset Nat) : dropIf drop x S ⊆ S := by
  unfold dropIf; split; exact Finset.erase_subset _ _; exact Finset.Subset.refl _

theorem dropIf_card_le (drop : Bool) (x : Nat) (S : Finset Nat) :
    S.card ≤ (dropIf drop x S).card + 1 := by
  unfold dropIf; split
  · by_cases hx : x ∈ S
    · have := Finset.card_erase_add_one hx; omega
    · rw [Finset.erase_eq_of_notMem hx]; omega
  · omega

inductive LiveBin (mask goal : Nat) : Nat → Finset Nat → Prop
  | done : LiveBin mask goal 0 {goal}
  | step {k : Nat} {S : Finset Nat} {a b op : Nat}
      (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hop : op < 4)
      (hz : binOp mask op a b ≠ 0) (hf : binOp mask op a b ∉ S)
      (keepA keepB : Bool) :
      LiveBin mask goal k (insert (binOp mask op a b) (dropIf (!keepA) a (dropIf (!keepB) b S))) →
      LiveBin mask goal (k + 1) S

theorem liveBin_zero_not_mem {mask goal k : Nat} {S : Finset Nat} (hg : goal ≠ 0)
    (h : LiveBin mask goal k S) : 0 ∉ S := by
  induction h with
  | done => simp [hg.symm]
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    intro h0; apply ih
    apply Finset.mem_insert_of_mem
    unfold dropIf
    split
    · apply Finset.mem_erase.mpr; refine ⟨ha0.symm, ?_⟩
      split
      · exact Finset.mem_erase.mpr ⟨hb0.symm, h0⟩
      · exact h0
    · split
      · exact Finset.mem_erase.mpr ⟨hb0.symm, h0⟩
      · exact h0

theorem liveBin_card_le {mask goal k : Nat} {S : Finset Nat} (h : LiveBin mask goal k S) :
    S.card ≤ k + 1 := by
  induction h with
  | done => simp
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    set z := binOp mask op a b
    have h1 := dropIf_card_le (!keepB) b S
    have h2 := dropIf_card_le (!keepA) a (dropIf (!keepB) b S)
    have hz' : z ∉ dropIf (!keepA) a (dropIf (!keepB) b S) := fun hm =>
      hf (dropIf_subset _ _ _ (dropIf_subset _ _ _ hm))
    have h3 : (insert z (dropIf (!keepA) a (dropIf (!keepB) b S))).card =
        (dropIf (!keepA) a (dropIf (!keepB) b S)).card + 1 := Finset.card_insert_of_notMem hz'
    omega

theorem extractLiveBin_aux {mask goal : Nat} (hg : goal ≠ 0) :
    ∀ (vs bank : List Nat) (k : Nat) (L : Finset Nat),
      BuildsBin mask bank vs → (∀ w ∈ bank, canon mask w = w) →
      L ⊆ (vs ++ bank).toFinset → LiveBin mask goal k L →
      ∃ k' S, k' ≤ k + vs.length ∧ S ⊆ bank.toFinset ∧ LiveBin mask goal k' S
  | [], bank, k, L, _, _, hsub, hlive => ⟨k, L, by simp, hsub, hlive⟩
  | v :: vs, bank, k, L, hbuild, hcb, hsub, hlive => by
    have hcv : canon mask v = v := by
      obtain ⟨a, b, op, _, _, _, rfl⟩ := hbuild.1; exact binOp_canon mask op a b
    have hcb' : ∀ w ∈ v :: bank, canon mask w = w := by
      intro w hw; rcases List.mem_cons.mp hw with rfl | hw; exact hcv; exact hcb w hw
    have hsub' : L ⊆ (vs ++ (v :: bank)).toFinset := by
      intro w hw
      have := hsub hw
      simp only [List.toFinset_append, List.toFinset_cons, Finset.mem_union, Finset.mem_insert] at this ⊢
      tauto
    obtain ⟨k1, L1, hk1, hL1sub, hlive1⟩ := extractLiveBin_aux hg vs (v :: bank) k L hbuild.2 hcb' hsub' hlive
    by_cases hv : v ∈ L1 ∧ v ∉ bank
    · obtain ⟨hvL, hvb⟩ := hv
      have hv0 : v ≠ 0 := fun h0 => liveBin_zero_not_mem hg hlive1 (h0 ▸ hvL)
      obtain ⟨a, b, op, hop, haA, hbA, hvEq⟩ := hbuild.1
      have ha0 : a ≠ 0 := by
        intro h0; subst h0
        rcases binOp_zero_left mask op b with h | h
        · exact hv0 (hvEq.trans h)
        · rcases hbA with rfl | hbM
          · rw [canon_zero] at h; exact hv0 (hvEq.trans h)
          · rw [hcb b hbM] at h; exact hvb ((hvEq.trans h) ▸ hbM)
      have hb0 : b ≠ 0 := by
        intro h0; subst h0
        rcases binOp_zero_right mask op a with h | h
        · exact hv0 (hvEq.trans h)
        · rcases haA with rfl | haM
          · rw [canon_zero] at h; exact hv0 (hvEq.trans h)
          · rw [hcb a haM] at h; exact hvb ((hvEq.trans h) ▸ haM)
      have haM : a ∈ bank := haA.resolve_left ha0
      have hbM : b ∈ bank := hbA.resolve_left hb0
      have hab : a ≠ b := by
        intro h; subst h
        rcases binOp_self mask op a with h0 | ha'
        · exact hv0 (hvEq.trans h0)
        · rw [hcb a haM] at ha'; exact hvb ((hvEq.trans ha') ▸ haM)
      set R := L1.erase v
      set S := insert a (insert b R)
      have hSsub : S ⊆ bank.toFinset := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact List.mem_toFinset.mpr haM
        · rcases Finset.mem_insert.mp hw with rfl | hw
          · exact List.mem_toFinset.mpr hbM
          · have h1 := hL1sub (Finset.mem_of_mem_erase hw)
            simp only [List.toFinset_cons, Finset.mem_insert] at h1
            exact h1.resolve_left (Finset.ne_of_mem_erase hw)
      have hvNotS : v ∉ S := by
        intro hm
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact hvb haM
        · rcases Finset.mem_insert.mp hm with rfl | hm
          · exact hvb hbM
          · exact (Finset.notMem_erase v L1) hm
      have hL1eq : insert v (dropIf (!(decide (a ∈ R))) a (dropIf (!(decide (b ∈ R))) b S)) = L1 := by
        ext w
        by_cases haR : a ∈ R <;> by_cases hbR : b ∈ R
        · simp only [haR, hbR, decide_true, Bool.not_true, Bool.false_eq_true, dropIf, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | rfl | rfl | ⟨_, hw⟩); exact hvL; exact (Finset.mem_erase.mp haR).2; exact (Finset.mem_erase.mp hbR).2; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h; exact Or.inr (Or.inr (Or.inr ⟨h, hw⟩))
        · simp only [haR, hbR, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, dropIf, ite_true, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwb, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact (Finset.mem_erase.mp haR).2; exact absurd rfl hwb; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            intro hwb; subst hwb; exact hbR (Finset.mem_erase.mpr ⟨h, hw⟩)
        · simp only [haR, hbR, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, dropIf, ite_true, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwa, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact absurd rfl hwa; exact (Finset.mem_erase.mp hbR).2; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            intro hwa; subst hwa; exact haR (Finset.mem_erase.mpr ⟨h, hw⟩)
        · simp only [haR, hbR, decide_false, Bool.not_false, dropIf, ite_true, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwa, hwb, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact absurd rfl hwa; exact absurd rfl hwb; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, ?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            · intro hwa; subst hwa; exact haR (Finset.mem_erase.mpr ⟨h, hw⟩)
            · intro hwb; subst hwb; exact hbR (Finset.mem_erase.mpr ⟨h, hw⟩)
      refine ⟨k1 + 1, S, by simp only [List.length_cons]; omega, hSsub, ?_⟩
      apply LiveBin.step (a := a) (b := b) (op := op)
        (Finset.mem_insert_self a _) (Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
        hab ha0 hb0 hop (hvEq ▸ hv0) (hvEq ▸ hvNotS) (decide (a ∈ R)) (decide (b ∈ R))
      rw [← hvEq, hL1eq]; exact hlive1
    · refine ⟨k1, L1, by simp only [List.length_cons]; omega, ?_, hlive1⟩
      intro w hw
      have h1 := hL1sub hw
      simp only [List.toFinset_cons, Finset.mem_insert] at h1
      rcases h1 with rfl | h1
      · have hvb : w ∈ bank := by by_contra hnb; exact hv ⟨hw, hnb⟩
        exact List.mem_toFinset.mpr hvb
      · exact h1

theorem extractLiveBin {mask goal : Nat} {stock vs : List Nat}
    (hg : goal ≠ 0) (hcs : ∀ w ∈ stock, canon mask w = w)
    (hbuild : BuildsBin mask stock vs) (hhit : Avail (vs ++ stock) goal) :
    ∃ k S, k ≤ vs.length ∧ S ⊆ stock.toFinset ∧ LiveBin mask goal k S := by
  have hmem : goal ∈ vs ++ stock := hhit.resolve_left hg
  have hsub : ({goal} : Finset Nat) ⊆ (vs ++ stock).toFinset := by
    intro w hw; rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hmem
  obtain ⟨k, S, hk, hS, hL⟩ := extractLiveBin_aux hg vs stock 0 {goal} hbuild hcs hsub LiveBin.done
  exact ⟨k, S, by omega, hS, hL⟩

theorem liveBin_agrees {mask goal k p n : Nat} {S : Finset Nat}
    (hp : mask.testBit p = true) (hn : mask.testBit n = true)
    (h : LiveBin mask goal k S) (hag : ∀ w ∈ S, w.testBit p = w.testBit n) :
    goal.testBit p = goal.testBit n := by
  induction h with
  | done => exact hag goal (Finset.mem_singleton_self goal)
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    apply ih; intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · have ea := hag a ha
      have eb := hag b hb
      unfold binOp
      cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
      all_goals rw [canon_testBit_eq hp hn]
      all_goals simp [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, hp, hn, ea, eb]
    · exact hag w (dropIf_subset _ _ _ (dropIf_subset _ _ _ hw))

def forceW {α : Type} (w : Nat) (k : Nat → α) : α :=
  Nat.rec (k 0) (fun m _ => k (m + 1)) w

theorem forceW_eq {α : Type} (w : Nat) (k : Nat → α) : forceW w k = k w := by
  cases w <;> rfl

def forceWs (ws : List Nat) (k : List Nat → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun w _ next k => forceW w (fun v => next (fun rest => k (v :: rest)))) ws) k

theorem forceWs_eq (ws : List Nat) (k : List Nat → Bool) : forceWs ws k = k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceW w (fun v => forceWs ws (fun rest => k (v :: rest))) = _
    rw [forceW_eq, ih]

def dagPart (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      (Nat.beq p 0 || Nat.beq n 0) ||
        forceW (p &&& w) (fun up =>
          forceW (n &&& w) (fun down =>
            rest up down &&
              forceW (p ^^^ up) (fun offP =>
                forceW (n ^^^ down) (rest offP))))) ws

theorem offBits {v w i : Nat} (h : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor, Nat.testBit_and] at h
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv, hw] at h ⊢

theorem dagPart_sound {ws : List Nat} {pos neg : Nat} (fail : dagPart ws pos neg = false) :
    ∃ p n, pos.testBit p = true ∧ neg.testBit n = true ∧ ∀ w ∈ ws, w.testBit p = w.testBit n := by
  have nonempty {w : Nat} (hn : w ≠ 0) : ∃ j, w.testBit j = true := by
    by_contra! all; apply hn; apply Nat.eq_of_testBit_eq; intro i; simp [all i]
  induction ws generalizing pos neg with
  | nil =>
    change (Nat.beq pos 0 || Nat.beq neg 0) = false at fail
    simp only [Bool.or_eq_false_iff] at fail
    obtain ⟨p, hp⟩ := nonempty (ne_of_beq_false fail.1)
    obtain ⟨n, hn⟩ := nonempty (ne_of_beq_false fail.2)
    exact ⟨p, n, hp, hn, by simp⟩
  | cons w ws ih =>
    change ((Nat.beq pos 0 || Nat.beq neg 0) ||
      forceW (pos &&& w) (fun up =>
        forceW (neg &&& w) (fun down =>
          dagPart ws up down &&
            forceW (pos ^^^ up) (fun offP =>
              forceW (neg ^^^ down) (dagPart ws offP))))) = false at fail
    simp only [forceW_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p, n, hp, hn, ag⟩ := ih on
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hn
      refine ⟨p, n, hp.1, hn.1, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [hp.2, hn.2]
      · exact ag a ha
    · obtain ⟨p, n, hp, hn, ag⟩ := ih off
      have hp' := offBits hp
      have hn' := offBits hn
      refine ⟨p, n, hp'.1, hn'.1, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [hp'.2, hn'.2]
      · exact ag a ha

theorem dagPart_live {mask goal k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset) :
    dagPart ws goal (mask ^^^ goal) = true := by
  by_contra hf
  have hfalse : dagPart ws goal (mask ^^^ goal) = false := by
    cases h : dagPart ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p, n, hp, hn, ag⟩ := dagPart_sound hfalse
  have hpm : mask.testBit p = true := by
    have e := congrArg (fun x => x.testBit p) hgm
    simp only [Nat.testBit_and, hp, Bool.true_and] at e; exact e
  have hnm : mask.testBit n = true ∧ goal.testBit n = false := by
    rw [Nat.testBit_xor] at hn
    have imp : goal.testBit n = true → mask.testBit n = true := by
      intro hg
      have e := congrArg (fun x => x.testBit n) hgm
      simp only [Nat.testBit_and, hg, Bool.true_and] at e; exact e
    cases hm : mask.testBit n <;> cases hg : goal.testBit n <;> simp_all
  have eq := liveBin_agrees hpm hnm.1 hlive (fun w hw => ag w (List.mem_toFinset.mp hw))
  rw [hp, hnm.2] at eq; exact Bool.noConfusion eq

def flatSet (cut : Nat) (S : Finset Nat) : Finset Nat :=
  S.filter (fun w => Nat.beq (canon cut w) 0)

theorem flatSet_insert_notMem {cut w : Nat} {S : Finset Nat} (hw : w ∉ S) :
    (flatSet cut (insert w S)).card =
      if canon cut w = 0 then (flatSet cut S).card + 1 else (flatSet cut S).card := by
  unfold flatSet
  rw [Finset.filter_insert]
  by_cases hc : canon cut w = 0
  · simp only [hc, Nat.beq_refl, ite_true]
    exact Finset.card_insert_of_notMem (fun h => hw (Finset.mem_filter.mp h).1)
  · simp only [beq_false_ne hc, Bool.false_eq_true, ite_false, hc]

theorem flatSet_erase {cut w : Nat} {S : Finset Nat} :
    (flatSet cut S).card ≤ (flatSet cut (S.erase w)).card + (if canon cut w = 0 then 1 else 0) := by
  unfold flatSet
  rw [Finset.filter_erase]
  by_cases hm : w ∈ S.filter (fun x => Nat.beq (canon cut x) 0)
  · have hcw : canon cut w = 0 := Nat.eq_of_beq_eq_true (Finset.mem_filter.mp hm).2
    have hcard := Finset.card_erase_add_one hm
    simp only [hcw, ite_true]; omega
  · rw [Finset.erase_eq_of_notMem hm]; omega

theorem maskedBuildBin {mask cut goal k : Nat} {S : Finset Nat}
    (sub : mask &&& cut = cut) (hgnf : canon cut goal ≠ 0)
    (h : LiveBin mask goal k S) :
    ∀ (bank : List Nat), (∀ w ∈ S, Avail bank (canon cut w)) →
      ∃ vs, vs.length + (flatSet cut S).card ≤ k ∧ BuildsBin cut bank vs ∧
        Avail (vs ++ bank) (canon cut goal) := by
  induction h with
  | done =>
    intro bank hsup
    have hfl : (flatSet cut {goal}).card = 0 := by
      unfold flatSet
      simp [hgnf]
    exact ⟨[], by simp [hfl], trivial, hsup goal (Finset.mem_singleton_self goal)⟩
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB tail ih =>
    intro bank hsup
    set z := binOp mask op a b
    set S1 := dropIf (!keepB) b S
    set S2 := dropIf (!keepA) a S1
    set S' := insert z S2
    have hS2sub : S2 ⊆ S := Finset.Subset.trans (dropIf_subset _ _ _) (dropIf_subset _ _ _)
    have hzNotS2 : z ∉ S2 := fun hm => hf (hS2sub hm)
    have hfl1 : (flatSet cut S).card ≤ (flatSet cut S1).card + (if canon cut b = 0 then 1 else 0) := by
      unfold S1 dropIf; split; exact flatSet_erase; omega
    have hfl2 : (flatSet cut S1).card ≤ (flatSet cut S2).card + (if canon cut a = 0 then 1 else 0) := by
      unfold S2 dropIf; split; exact flatSet_erase; omega
    have hfl3 : (flatSet cut S').card =
        if canon cut z = 0 then (flatSet cut S2).card + 1 else (flatSet cut S2).card :=
      flatSet_insert_notMem hzNotS2
    have hcz : canon cut z = 0 ∨ canon cut z = canon cut a ∨ canon cut z = canon cut b ∨
        ∃ op' < 4, canon cut z = binOp cut op' (canon cut a) (canon cut b) :=
      canon_sub_binOp sub
    by_cases hfa : canon cut a = 0
    · by_cases hfb : canon cut b = 0
      · have hfz : canon cut z = 0 := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact h
          · exact h.trans hfa
          · exact h.trans hfb
          · rw [hfa, hfb] at h
            rcases binOp_zero_left cut op' 0 with h0 | h0
            · exact h.trans h0
            · exact h.trans (h0.trans (canon_zero cut))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact Or.inl hfz
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, hfz, ite_true] at hfl1 hfl2 hfl3
        exact ⟨vs, by omega, hbd, hhit⟩
      · have hfz : canon cut z = 0 ∨ canon cut z = canon cut b := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact Or.inl h
          · exact Or.inl (h.trans hfa)
          · exact Or.inr h
          · rw [hfa] at h
            rcases binOp_zero_left cut op' (canon cut b) with h0 | h0
            · exact Or.inl (h.trans h0)
            · exact Or.inr (h.trans (h0.trans (canon_idem cut b)))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rcases hfz with h0 | hb'
            · exact Or.inl h0
            · rw [hb']; exact hsup b hb
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, ite_true, ite_false] at hfl1 hfl2
        have : (flatSet cut S2).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        exact ⟨vs, by omega, hbd, hhit⟩
    · by_cases hfb : canon cut b = 0
      · have hfz : canon cut z = 0 ∨ canon cut z = canon cut a := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact Or.inl h
          · exact Or.inr h
          · exact Or.inl (h.trans hfb)
          · rw [hfb] at h
            rcases binOp_zero_right cut op' (canon cut a) with h0 | h0
            · exact Or.inl (h.trans h0)
            · exact Or.inr (h.trans (h0.trans (canon_idem cut a)))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rcases hfz with h0 | ha'
            · exact Or.inl h0
            · rw [ha']; exact hsup a ha
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, ite_true, ite_false] at hfl1 hfl2
        have : (flatSet cut S2).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        exact ⟨vs, by omega, hbd, hhit⟩
      · simp only [hfa, hfb, ite_false] at hfl1 hfl2
        have hfl_le : (flatSet cut S).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        rcases hcz with h0 | ha' | hb' | ⟨op', hop', hbin⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Or.inl h0
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · rw [ha']; exact hsup a ha
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · rw [hb']; exact hsup b hb
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · set cz := canon cut z
          have hgate : GateBin cut bank cz := ⟨canon cut a, canon cut b, op', hop', hsup a ha, hsup b hb, hbin⟩
          have hsup' : ∀ w ∈ S', Avail (cz :: bank) (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Or.inr List.mem_cons_self
            · exact avail_weaken (fun u hu => List.mem_cons_of_mem _ hu) (hsup w (hS2sub hw))
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih (cz :: bank) hsup'
          refine ⟨cz :: vs, by simp only [List.length_cons]; omega, ⟨hgate, hbd⟩, ?_⟩
          exact avail_weaken (fun u hu => by simp only [List.mem_append, List.mem_cons] at hu ⊢; tauto) hhit

def flatCount (cut : Nat) (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ cnt => bsel (Nat.beq (canon cut w) 0) (cnt + 1) cnt) ws

theorem flatCount_card (cut : Nat) {ws : List Nat} (nd : ws.Nodup) :
    flatCount cut ws = (flatSet cut ws.toFinset).card := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hnd := List.nodup_cons.mp nd
    have fresh : w ∉ ws.toFinset := by simpa using hnd.1
    change bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws) = _
    rw [List.toFinset_cons, flatSet_insert_notMem fresh, ih hnd.2]
    by_cases hc : canon cut w = 0
    · simp [hc, bsel]
    · rw [beq_false_ne hc, bsel_false]; simp [hc]

def availB (bank : List Nat) (w : Nat) : Bool :=
  Nat.beq w 0 || bank.contains w

theorem availB_spec {bank : List Nat} {w : Nat} : availB bank w = true ↔ Avail bank w := by
  unfold availB Avail; simp [Nat.beq_eq]

def recipeGateBin (cut : Nat) (bank : List Nat) (vc ac bc : Nat) : Bool :=
  availB bank ac && availB bank bc &&
    (Nat.beq vc (binOp cut 0 ac bc) || Nat.beq vc (binOp cut 1 ac bc) ||
     Nat.beq vc (binOp cut 2 ac bc) || Nat.beq vc (binOp cut 3 ac bc))

theorem recipeGateBin_spec {cut : Nat} {bank : List Nat} {vc ac bc : Nat}
    (h : recipeGateBin cut bank vc ac bc = true) : GateBin cut bank vc := by
  unfold recipeGateBin at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, availB_spec] at h
  obtain ⟨⟨ha, hb⟩, ((h0 | h1) | h2) | h3⟩ := h
  · exact ⟨ac, bc, 0, by omega, ha, hb, h0⟩
  · exact ⟨ac, bc, 1, by omega, ha, hb, h1⟩
  · exact ⟨ac, bc, 2, by omega, ha, hb, h2⟩
  · exact ⟨ac, bc, 3, by omega, ha, hb, h3⟩

def addUniq (w : Nat) (l : List Nat) : List Nat :=
  if l.contains w then l else w :: l

def recipeStart (cut : Nat) (stock ws : List Nat) : List Nat :=
  List.rec [] (fun w _ acc =>
    let v := canon cut w
    if availB stock v then acc else addUniq v acc) ws

def recipeClose (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      let v := canon cut w
      if acc.contains v then
        let va := canon cut a
        let vb := canon cut b
        let acc1 := if availB stock va then acc else addUniq va acc
        let acc2 := if availB stock vb then acc1 else addUniq vb acc1
        next acc2
      else next acc) hist needed

def replayRec (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := canon cut w
      if needed.contains v && !(availB bank v) && recipeGateBin cut bank v (canon cut a) (canon cut b) then
        v :: next (v :: bank)
      else next bank) hist bank

theorem replayRec_builds (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) :
    BuildsBin cut bank (replayRec cut needed hist bank) := by
  induction hist generalizing bank with
  | nil => trivial
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    change BuildsBin cut bank
      (if needed.contains (canon cut w) && !(availB bank (canon cut w)) &&
          recipeGateBin cut bank (canon cut w) (canon cut a) (canon cut b) then
        canon cut w :: replayRec cut needed hist (canon cut w :: bank)
      else replayRec cut needed hist bank)
    split
    · rename_i hyes
      exact ⟨recipeGateBin_spec (Bool.and_eq_true_iff.mp hyes).2, ih _⟩
    · exact ih _

def directRecipe (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat))
    (start : List Nat) : Bool :=
  start.all fun v => hist.any fun (z, a, b) =>
    Nat.beq (canon cut z) v && recipeGateBin cut stock v (canon cut a) (canon cut b)

theorem directRecipe_builds {cut : Nat} {stock start : List Nat}
    {hist : List (Nat × Nat × Nat)} (h : directRecipe cut stock hist start = true) :
    BuildsBin cut stock start := by
  have gates : ∀ v ∈ start, GateBin cut stock v := by
    intro v hv
    obtain ⟨⟨z,a,b⟩,_,ha⟩ :=
      List.any_eq_true.mp (List.all_eq_true.mp h v hv)
    exact recipeGateBin_spec (Bool.and_eq_true_iff.mp ha).2
  clear h
  induction start generalizing stock with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gates v List.mem_cons_self, ih ?_⟩
    intro w hw
    exact gate_weaken (fun x hx => List.mem_cons_of_mem _ hx)
      (gates w (List.mem_cons_of_mem _ hw))

theorem mem_addUniq {v w : Nat} {xs : List Nat} : w ∈ addUniq v xs ↔ w = v ∨ w ∈ xs := by
  unfold addUniq
  split
  · rename_i h
    exact ⟨Or.inr, fun h' => h'.elim (fun e => e ▸ List.contains_iff_mem.mp h) id⟩
  · simp

theorem recipeStart_covers (cut : Nat) (stock ws : List Nat) :
    ∀ w ∈ ws, Avail (recipeStart cut stock ws ++ stock) (canon cut w) := by
  induction ws with
  | nil => simp
  | cons v vs ih =>
    intro w hw
    have mono : ∀ t ∈ recipeStart cut stock vs ++ stock, t ∈ recipeStart cut stock (v :: vs) ++ stock := by
      intro t ht
      rw [List.mem_append] at ht ⊢
      refine ht.imp_left ?_
      intro ht
      unfold recipeStart
      dsimp only
      split
      · exact ht
      · exact mem_addUniq.mpr (Or.inr ht)
    rcases List.mem_cons.mp hw with rfl | hw
    · unfold recipeStart
      dsimp only
      split
      · exact avail_weaken (fun t ht => List.mem_append_right _ ht) (availB_spec.mp (by assumption))
      · exact Or.inr (List.mem_append_left _ (mem_addUniq.mpr (Or.inl rfl)))
    · exact avail_weaken mono (ih w hw)

def boundCloses (target : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, stock, lower, goal) := bound
  let (fuel, ws, hist) := state
  Nat.beq (canon cut target) goal && !(Nat.beq goal 0) &&
    forceW (fuel - flatCount cut ws) (fun rem =>
      if Nat.blt rem lower then
        forceWs (recipeStart cut stock ws) (fun start =>
          if Nat.blt (start.length + rem) lower then
            if directRecipe cut stock hist start then true else
            forceWs (recipeClose cut stock hist start) (fun needed =>
              if Nat.blt (needed.length + rem) lower then
                forceWs (replayRec cut needed hist.reverse stock) (fun replay =>
                  Nat.blt (replay.length + rem) lower &&
                    ws.all (fun w => availB (replay ++ stock) (canon cut w)))
              else false)
          else false)
      else false)

def knownCloses (target : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  List.rec false (fun b _ rest => boundCloses target state b || rest) bounds

def KnownBin (bounds : List (Nat × List Nat × Nat × Nat)) : Prop :=
  ∀ b ∈ bounds, LowerBin b.1 b.2.1 b.2.2.2 b.2.2.1

theorem boundCloses_sound {mask goal : Nat} {state : Nat × List Nat × List (Nat × Nat × Nat)}
    {bound : Nat × List Nat × Nat × Nat}
    (hlow : LowerBin bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (sub : mask &&& bound.1 = bound.1)
    (nd : state.2.1.Nodup) {k : Nat} (hk : k ≤ state.1)
    (hlive : LiveBin mask goal k state.2.1.toFinset) :
    boundCloses goal state bound = false := by
  obtain ⟨fuel, ws, hist⟩ := state
  obtain ⟨cut, stock, lower, bgoal⟩ := bound
  dsimp only at hlow sub nd hk hlive
  apply Bool.eq_false_iff.mpr
  intro hc
  unfold boundCloses at hc
  simp only [forceW_eq, forceWs_eq, Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hc
  obtain ⟨⟨hgeq, hgnz⟩, scan⟩ := hc
  have hgnz' : bgoal ≠ 0 := ne_of_beq_false hgnz
  have hgnf : canon cut goal ≠ 0 := hgeq.symm ▸ hgnz'
  have finish (xs : List Nat) (hbuild : BuildsBin cut stock xs)
      (hsrc : ∀ w ∈ ws, Avail (xs ++ stock) (canon cut w))
      (hlen : xs.length + (fuel - flatCount cut ws) < lower) : False := by
    obtain ⟨ys, hylen, hybd, hyhit⟩ :=
      maskedBuildBin sub hgnf hlive (xs ++ stock) (fun w hw => hsrc w (List.mem_toFinset.mp hw))
    rw [← flatCount_card cut nd] at hylen
    have hfinal : Avail ((xs ++ ys) ++ stock) bgoal := by
      rw [← hgeq]
      exact avail_weaken (fun u hu => by simp only [List.mem_append] at hu ⊢; tauto) hyhit
    have heno := hlow (xs ++ ys) (builds_append hbuild hybd) hfinal
    simp only [List.length_append] at heno
    omega
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  rename_i hlen
  split at scan
  · rename_i hDirect
    exact finish _ (directRecipe_builds hDirect) (recipeStart_covers cut stock ws) (Nat.blt_eq.mp hlen)
  · split at scan <;> try contradiction
    simp only [Bool.and_eq_true, Nat.blt_eq] at scan
    exact finish _ (replayRec_builds cut _ hist.reverse stock)
      (fun w hw => availB_spec.mp (List.all_eq_true.mp scan.2 w hw)) scan.1

theorem knownCloses_sound {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {state : Nat × List Nat × List (Nat × Nat × Nat)}
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (nd : state.2.1.Nodup) {k : Nat} (hk : k ≤ state.1)
    (hlive : LiveBin mask goal k state.2.1.toFinset) :
    knownCloses goal bounds state = false := by
  induction bounds with
  | nil => rfl
  | cons b bs ih =>
    change (boundCloses goal state b || knownCloses goal bs state) = false
    rw [boundCloses_sound (hknown b List.mem_cons_self) (hsub b List.mem_cons_self) nd hk hlive]
    exact ih (fun x hx => hknown x (List.mem_cons_of_mem _ hx)) (fun x hx => hsub x (List.mem_cons_of_mem _ hx))

def insertSorted (x : Nat) (l : List Nat) : List Nat :=
  List.rec [x] (fun y ys ih => bsel (Nat.ble x y) (x :: y :: ys) (y :: ih)) l

theorem insertSorted_mem {x w : Nat} {l : List Nat} :
    w ∈ insertSorted x l ↔ w = x ∨ w ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    change w ∈ bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys) ↔ _
    cases Nat.ble x y
    · rw [bsel_false]; simp only [List.mem_cons, ih]; tauto
    · rw [bsel_true]; simp only [List.mem_cons]

theorem insertSorted_nodup {x : Nat} {l : List Nat} (hx : x ∉ l) (nd : l.Nodup) :
    (insertSorted x l).Nodup := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    have hnd := List.nodup_cons.mp nd
    have hxy : x ≠ y := fun h => hx (h ▸ List.mem_cons_self)
    have hxs : x ∉ ys := fun h => hx (List.mem_cons_of_mem _ h)
    change (bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys)).Nodup
    cases Nat.ble x y
    · rw [bsel_false]
      apply List.nodup_cons.mpr
      refine ⟨fun hm => ?_, ih hxs hnd.2⟩
      rcases insertSorted_mem.mp hm with h | h
      · exact hxy h.symm
      · exact hnd.1 h
    · rw [bsel_true]; exact List.nodup_cons.mpr ⟨hx, nd⟩

def dropVal (drop : Bool) (x : Nat) (l : List Nat) : List Nat :=
  bsel drop (List.rec [] (fun y _ ih => bsel (Nat.beq y x) ih (y :: ih)) l) l

theorem dropVal_mem {drop : Bool} {x w : Nat} {l : List Nat} :
    w ∈ dropVal drop x l ↔ w ∈ l ∧ (drop = true → w ≠ x) := by
  cases drop
  · simp [dropVal, bsel]
  · induction l with
    | nil => simp [dropVal, bsel]
    | cons y ys ih =>
      change w ∈ bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys) ↔ _
      cases hb : Nat.beq y x
      · rw [bsel_false]
        have hne : y ≠ x := ne_of_beq_false hb
        simp only [List.mem_cons, ih, true_implies]
        constructor
        · rintro (rfl | ⟨hw, hwx⟩); exact ⟨Or.inl rfl, hne⟩; exact ⟨Or.inr hw, hwx⟩
        · rintro ⟨rfl | hw, hwx⟩; exact Or.inl rfl; exact Or.inr ⟨hw, hwx⟩
      · rw [bsel_true]
        have heq : y = x := Nat.eq_of_beq_eq_true hb
        subst heq
        simp only [List.mem_cons, ih, true_implies]
        constructor
        · rintro ⟨hw, hwx⟩; exact ⟨Or.inr hw, hwx⟩
        · rintro ⟨rfl | hw, hwx⟩; exact absurd rfl hwx; exact ⟨hw, hwx⟩

theorem dropVal_nodup {drop : Bool} {x : Nat} {l : List Nat} (nd : l.Nodup) :
    (dropVal drop x l).Nodup := by
  cases drop
  · exact nd
  · induction l with
    | nil => simp [dropVal, bsel]
    | cons y ys ih =>
      have hnd := List.nodup_cons.mp nd
      change (bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys)).Nodup
      cases Nat.beq y x
      · rw [bsel_false]
        exact List.nodup_cons.mpr ⟨fun hm => hnd.1 (dropVal_mem.mp hm).1, ih hnd.2⟩
      · rw [bsel_true]; exact ih hnd.2

theorem dropVal_toFinset (drop : Bool) (x : Nat) (l : List Nat) :
    (dropVal drop x l).toFinset = dropIf drop x l.toFinset := by
  ext w; simp only [List.mem_toFinset, dropVal_mem, dropIf]
  cases drop <;> simp [Finset.mem_erase, and_comm]

def subsetWords (stock : List Nat) (bits : Nat) : List Nat :=
  (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih b =>
      let rest := ih (b >>> 1)
      bsel (Nat.beq (b &&& 1) 1) (insertSorted w rest) rest) stock) bits

theorem subsetWords_subset (stock : List Nat) (bits : Nat) :
    ∀ w ∈ subsetWords stock bits, w ∈ stock := by
  induction stock generalizing bits with
  | nil => intro w hw; simp [subsetWords] at hw
  | cons x xs ih =>
    intro w hw
    change w ∈ bsel (Nat.beq (bits &&& 1) 1)
      (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1)) at hw
    cases hb : Nat.beq (bits &&& 1) 1
    · rw [hb, bsel_false] at hw; exact List.mem_cons_of_mem _ (ih _ w hw)
    · rw [hb, bsel_true] at hw
      rcases insertSorted_mem.mp hw with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ w hm)

theorem subsetWords_nodup {stock : List Nat} (nd : stock.Nodup) (bits : Nat) :
    (subsetWords stock bits).Nodup := by
  induction stock generalizing bits with
  | nil => simp [subsetWords]
  | cons x xs ih =>
    have hnd := List.nodup_cons.mp nd
    change (bsel (Nat.beq (bits &&& 1) 1)
      (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1))).Nodup
    cases Nat.beq (bits &&& 1) 1
    · rw [bsel_false]; exact ih hnd.2 _
    · rw [bsel_true]; exact insertSorted_nodup (fun hm => hnd.1 (subsetWords_subset xs _ x hm)) (ih hnd.2 _)

theorem exists_subsetToken (stock : List Nat) (S : Finset Nat) :
    ∃ bits < 2 ^ stock.length, (subsetWords stock bits).toFinset = S ∩ stock.toFinset := by
  induction stock with
  | nil => exact ⟨0, by simp, by simp [subsetWords]⟩
  | cons x xs ih =>
    obtain ⟨b, hb, heq⟩ := ih
    by_cases hx : x ∈ S
    · refine ⟨2 * b + 1, by simp only [List.length_cons, Nat.pow_succ]; omega, ?_⟩
      have hdiv : (2 * b + 1) >>> 1 = b := by change (2 * b + 1) / 2 = b; omega
      have hmod : ((2 * b + 1) &&& 1) = 1 := by rw [Nat.and_one_is_mod]; omega
      change (bsel (Nat.beq ((2 * b + 1) &&& 1) 1)
        (insertSorted x (subsetWords xs ((2 * b + 1) >>> 1)))
        (subsetWords xs ((2 * b + 1) >>> 1))).toFinset = _
      rw [hdiv, hmod, Nat.beq_refl, bsel_true]
      ext w; simp only [List.mem_toFinset, insertSorted_mem, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert]
      have hw : w ∈ subsetWords xs b ↔ w ∈ S ∧ w ∈ xs := by
        have e := congrArg (fun t => w ∈ t) heq; simpa [List.mem_toFinset] using e
      rw [hw]; constructor
      · rintro (rfl | ⟨hs, hxs⟩); exact ⟨hx, Or.inl rfl⟩; exact ⟨hs, Or.inr hxs⟩
      · rintro ⟨hs, rfl | hxs⟩; exact Or.inl rfl; exact Or.inr ⟨hs, hxs⟩
    · refine ⟨2 * b, by simp only [List.length_cons, Nat.pow_succ]; omega, ?_⟩
      have hdiv : (2 * b) >>> 1 = b := by change (2 * b) / 2 = b; omega
      have hmod : ((2 * b) &&& 1) = 0 := by rw [Nat.and_one_is_mod]; omega
      change (bsel (Nat.beq ((2 * b) &&& 1) 1)
        (insertSorted x (subsetWords xs ((2 * b) >>> 1)))
        (subsetWords xs ((2 * b) >>> 1))).toFinset = _
      rw [hdiv, hmod]
      change (subsetWords xs b).toFinset = _
      ext w; simp only [List.mem_toFinset, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert]
      have hw : w ∈ subsetWords xs b ↔ w ∈ S ∧ w ∈ xs := by
        have e := congrArg (fun t => w ∈ t) heq; simpa [List.mem_toFinset] using e
      rw [hw]; constructor
      · rintro ⟨hs, hxs⟩; exact ⟨hs, Or.inr hxs⟩
      · rintro ⟨hs, rfl | hxs⟩; exact absurd hs hx; exact ⟨hs, hxs⟩

def rootState (stock : List Nat) (fuel token : Nat) : Nat × List Nat × List (Nat × Nat × Nat) :=
  (fuel, subsetWords stock token, [])

def makeToken (a b op keep : Nat) : Nat := ((a * 16 + b) * 4 + op) * 4 + keep

def childState (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, hist) := state
  let keep := token &&& 3
  let op := (token >>> 2) &&& 3
  let b := (token >>> 4) &&& 15
  let a := token >>> 8
  if Nat.beq fuel 0 || !(Nat.blt a b) || !(Nat.blt b ws.length) then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let z := binOp mask op x y
    if Nat.beq z 0 || ws.contains z then none
    else
      let keepA := Nat.beq (keep &&& 1) 1
      let keepB := Nat.beq ((keep >>> 1) &&& 1) 1
      let rest := dropVal (!keepA) x (dropVal (!keepB) y ws)
      some (fuel - 1, insertSorted z rest, (z, x, y) :: hist)

theorem childState_wf {mask token : Nat} {st ch : Nat × List Nat × List (Nat × Nat × Nat)}
    (nd : st.2.1.Nodup) (h : childState mask token st = some ch) :
    ch.1 < st.1 ∧ ch.2.1.Nodup := by
  obtain ⟨fuel, ws, hist⟩ := st
  dsimp only at nd
  unfold childState at h; dsimp only at h
  split at h
  · contradiction
  · rename_i hok
    split at h
    · contradiction
    · rename_i hfresh
      have heq := Option.some.inj h
      subst ch
      simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hok hfresh
      have hfpos : fuel ≠ 0 := fun hf => hok (Or.inl (Or.inl hf))
      have hznot : ¬(ws.contains (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0)
          (ws.getD ((token >>> 4) &&& 15) 0)) = true) := fun hm => hfresh (Or.inr hm)
      refine ⟨by dsimp; omega, ?_⟩
      apply insertSorted_nodup
      · intro hm
        have hmem := (dropVal_mem.mp (dropVal_mem.mp hm).1).1
        exact hznot (List.contains_iff_mem.mpr hmem)
      · exact dropVal_nodup (dropVal_nodup nd)

def dagTrace (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ prev j =>
      let (parent, token) := forest j
      if Nat.beq parent 0 then
        if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
      else (prev (parent - 1)).bind (childState mask token)) (fuel + 1)) i

theorem dagTrace_nodup {mask fuel : Nat} {stock : List Nat} {forest : Nat → Nat × Nat}
    (nd : stock.Nodup) {i : Nat} {st : Nat × List Nat × List (Nat × Nat × Nat)}
    (h : dagTrace mask stock fuel forest i = some st) : st.2.1.Nodup := by
  unfold dagTrace at h
  suffices ∀ steps j s,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j = some s → s.2.1.Nodup from
    this (fuel + 1) i st h
  intro steps
  induction steps with
  | zero => intro j s h; contradiction
  | succ n ih =>
    intro j s h; dsimp only at h
    split at h
    · split at h
      · have e := Option.some.inj h; subst s; exact subsetWords_nodup nd _
      · contradiction
    · cases hp : (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) n) ((forest j).1 - 1) with
      | none => rw [hp] at h; contradiction
      | some p => rw [hp] at h; exact (childState_wf (ih _ _ hp) h).2

def dagLocal (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, _) := state
  Nat.blt (fuel + 1) ws.length ||
    !(dagPart ws goal (mask ^^^ goal)) ||
    knownCloses goal bounds state

theorem dagLocal_open {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {state : Nat × List Nat × List (Nat × Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (nd : state.2.1.Nodup) {k : Nat} (hk : k ≤ state.1)
    (hlive : LiveBin mask goal k state.2.1.toFinset) :
    dagLocal mask goal bounds state = false := by
  obtain ⟨fuel, ws, hist⟩ := state
  dsimp only at nd hk hlive
  unfold dagLocal
  have hcard : ws.length ≤ fuel + 1 := by
    have := liveBin_card_le hlive
    rw [List.toFinset_card_of_nodup nd] at this; omega
  have h1 : Nat.blt (fuel + 1) ws.length = false := by
    cases h : Nat.blt (fuel + 1) ws.length; rfl; have := Nat.blt_eq.mp h; omega
  have h2 : dagPart ws goal (mask ^^^ goal) = true := dagPart_live hgm hlive
  have h3 : knownCloses goal bounds (fuel, ws, hist) = false :=
    knownCloses_sound hknown hsub nd hk hlive
  simp [h1, h2, h3]

def treeBlock (lo hi : Nat) (f : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      if Nat.blt a b then
        let m := (a + b) / 2
        if Nat.beq a m then f a else next a m && next m b
      else true) (hi - lo + 1)) lo hi

theorem treeBlock_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlock lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  unfold treeBlock at h
  suffices ∀ steps a b, b - a ≤ steps →
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b = true →
      ∀ i, a ≤ i → i < b → f i = true by
    intro i h1 h2; exact this (hi - lo + 1) lo hi (by omega) h i h1 h2
  intro steps
  induction steps with
  | zero => intro a b hba _ i h1 h2; omega
  | succ s ih =>
    intro a b hba h i h1 h2
    dsimp only at h
    have hab : Nat.blt a b = true := Nat.blt_eq.mpr (by omega)
    simp only [hab, ite_true] at h
    set m := (a + b) / 2
    by_cases ham : a = m
    · have hbm : Nat.beq a m = true := Nat.beq_eq.mpr ham
      simp only [hbm, ite_true] at h
      have hia : i = a := by omega
      subst hia; exact h
    · have hbm : Nat.beq a m = false := beq_false_ne ham
      simp only [hbm, Bool.false_eq_true, ite_false] at h
      rcases Bool.and_eq_true_iff.mp h with ⟨hl, hr⟩
      by_cases him : i < m
      · exact ih a m (by omega) hl i h1 him
      · exact ih m b (by omega) hr i (by omega) h2

def dagCheckChildren (mask goal : Nat) (bounds : Nat → List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, hist) := state
  let n := ws.length
  !(ws.contains goal) &&
    (Nat.beq fuel 0 ||
      (Nat.blt n 17 &&
        treeBlock 0 n (fun a =>
          let x := ws.getD a 0
          treeBlock (a + 1) n (fun b =>
            let y := ws.getD b 0
            treeBlock 0 4 (fun op =>
              forceW (binOp mask op x y) (fun z =>
                Nat.beq z 0 || ws.contains z ||
                  treeBlock 0 4 (fun keep =>
                    let keepA := Nat.beq (keep &&& 1) 1
                    let keepB := Nat.beq ((keep >>> 1) &&& 1) 1
                    let newLen := n - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0)
                    Nat.blt fuel newLen ||
                      forceWs (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))) (fun ws' =>
                        let ch := (fuel - 1, ws', (z, x, y) :: hist)
                        dagLocal mask goal (bounds (makeToken a b op keep)) ch || ref (makeToken a b op keep) ch))))))))

def dagCheckRoots (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (stock : List Nat) (fuel : Nat) : Bool :=
  treeBlock 0 (2 ^ stock.length) (fun token =>
    forceWs (subsetWords stock token) (fun ws =>
      let st := (fuel, ws, [])
      dagLocal mask goal bounds st || ref token st))

theorem getElem_index_lt {l : List Nat} {x : Nat} (hx : x ∈ l) :
    ∃ i < l.length, l.getD i 0 = x := by
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hx
  refine ⟨i, hi, ?_⟩
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, heq]

theorem list_len_child {x y z : Nat} {ws : List Nat} {keepA keepB : Bool}
    (nd : ws.Nodup) (hx : x ∈ ws) (hy : y ∈ ws) (hxy : x ≠ y) (hz : z ∉ ws) :
    (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).length =
      ws.length - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0) := by
  have nd' : (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).Nodup :=
    insertSorted_nodup (fun hm => hz (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
  have h1 := List.toFinset_card_of_nodup nd'
  have h2 := List.toFinset_card_of_nodup nd
  have hset : (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).toFinset =
      insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
    ext w
    simp only [List.mem_toFinset, insertSorted_mem, Finset.mem_insert, ← dropVal_toFinset]
  rw [hset] at h1
  have hz' : z ∉ dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset) :=
    fun hm => hz (List.mem_toFinset.mp (dropIf_subset _ _ _ (dropIf_subset _ _ _ hm)))
  rw [Finset.card_insert_of_notMem hz'] at h1
  set T := dropIf (!keepB) y ws.toFinset
  have hxb : x ∈ T := by
    unfold T dropIf; split
    · exact Finset.mem_erase.mpr ⟨hxy, List.mem_toFinset.mpr hx⟩
    · exact List.mem_toFinset.mpr hx
  have hcb : T.card = ws.toFinset.card - (if keepB then 0 else 1) := by
    unfold T dropIf; cases keepB
    · have := Finset.card_erase_add_one (List.mem_toFinset.mpr hy); simp; omega
    · simp
  have hca : (dropIf (!keepA) x T).card = T.card - (if keepA then 0 else 1) := by
    unfold dropIf; cases keepA
    · have := Finset.card_erase_add_one hxb; simp only [Bool.not_false, Bool.false_eq_true, ite_true, ite_false]; omega
    · simp
  have hlen2 : 2 ≤ ws.toFinset.card := by
    have hsub : ({x, y} : Finset Nat) ⊆ ws.toFinset := by
      intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
      · exact List.mem_toFinset.mpr hx
      · rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hy
    have hpair : ({x, y} : Finset Nat).card = 2 := Finset.card_pair hxy
    have := Finset.card_le_card hsub; omega
  rw [← h1, hca, hcb, h2]
  cases keepA <;> cases keepB <;> simp <;> omega

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true

def binaryCost (gs : List Gate) : Nat := (gs.filter isBinary).length

def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def evalBit (k : Nat) (w : Nat) : Bool := w.testBit k

def stepBool (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def actionWord (w : List Nat) (g : Gate) : Nat := match g.op with
  | .not => fullMask ^^^ ((g.inputs.head?.map (fun i => w.getD i 0)).getD 0)
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) fullMask
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

theorem fullMask_eq : fullMask = 2 ^ 64 - 1 := by decide

theorem fullMask_bit {k : Nat} (hk : k < 64) : fullMask.testBit k = true := by
  rw [fullMask_eq, Nat.testBit_two_pow_sub_one]; simp [hk]

theorem readBit (w : List Nat) (i k : Nat) :
    (w.map (evalBit k)).getD i false = evalBit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), evalBit]

theorem actionWord_spec (w : List Nat) (g : Gate) (hg : legal g) {k : Nat} (hk : k < 64) :
    stepBool (w.map (evalBit k)) g = (w ++ [actionWord w g]).map (evalBit k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hcap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hcap
  have hfm := fullMask_bit hk
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at hcap
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [stepBool, List.map_cons, List.map_nil, readBit, List.map_append, actionWord,
      GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some,
      Option.getD_none, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
      Bool.and_true, Bool.or_false, evalBit, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
      Nat.zero_testBit, hfm, Bool.true_xor]

def rawVars : List Nat :=
  [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

def rootStock : List Nat :=
  [0x5555555555555555, 0x3333333333333333, 0x0f0f0f0f0f0f0f0f,
   0x00ff00ff00ff00ff, 0x0000ffff0000ffff, 0x00000000ffffffff]

theorem rawVars_avail : ∀ u ∈ rawVars, Avail rootStock (canon fullMask u) := by
  intro u hu
  simp only [rawVars, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Or.inr (by decide)

theorem compileBin_aux (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w bank : List Nat)
    (hw : ∀ u ∈ w, Avail bank (canon fullMask u)) :
    ∃ vs, vs.length ≤ binaryCost gs ∧ BuildsBin fullMask bank vs ∧
      ∀ u ∈ gs.foldl (fun acc g => acc ++ [actionWord acc g]) w, Avail (vs ++ bank) (canon fullMask u) := by
  induction gs generalizing w bank with
  | nil => exact ⟨[], Nat.le_refl _, trivial, by simpa using hw⟩
  | cons g gs ih =>
    have hg0 := hg g List.mem_cons_self
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    set z := actionWord w g
    have hread (i : Nat) : Avail bank (canon fullMask (w.getD i 0)) := by
      by_cases hi : i < w.length
      · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi), canon_zero]; exact Or.inl rfl
    have hstep : Avail bank (canon fullMask z) ∨ (isBinary g = true ∧ GateBin fullMask bank (canon fullMask z)) := by
      obtain ⟨op, args⟩ := g
      obtain ⟨hop, hcap⟩ := hg0
      change op = .and ∨ op = .or ∨ op = .not at hop
      change args.length ≤ 2 at hcap
      rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at hcap
      · rcases hop with rfl | rfl | rfl
        · left; simp [z, actionWord, canon_self]; exact Or.inl rfl
        · left; simp [z, actionWord, canon_zero]; exact Or.inl rfl
        · left; simp [z, actionWord, canon_self]; exact Or.inl rfl
      · rcases hop with rfl | rfl | rfl
        · left; simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          rw [canon_land]; exact hread i
        · left; simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero]
          exact hread i
        · left; simp only [z, actionWord, List.head?_cons, Option.map_some, Option.getD_some]
          rw [canon_xor_mask]; exact hread i
      · rcases hop with rfl | rfl | rfl
        · simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          have h1 : canon fullMask (w.getD i 0 &&& (w.getD j 0 &&& fullMask)) =
              canon fullMask (w.getD i 0 &&& w.getD j 0) := by
            rw [← canon_land fullMask (w.getD i 0 &&& (w.getD j 0 &&& fullMask))]
            rw [← canon_land fullMask (w.getD i 0 &&& w.getD j 0)]
            congr 1; apply Nat.eq_of_testBit_eq; intro k; simp only [Nat.testBit_and]
            cases (w.getD i 0).testBit k <;> cases (w.getD j 0).testBit k <;> cases fullMask.testBit k <;> rfl
          rw [h1]
          rcases canon_and_in_binOp fullMask (w.getD i 0) (w.getD j 0) with h0 | hi' | hj' | ⟨op', hop', hbin⟩
          · left; exact Or.inl h0
          · left; rw [hi']; exact hread i
          · left; rw [hj']; exact hread j
          · right; exact ⟨rfl, canon fullMask (w.getD i 0), canon fullMask (w.getD j 0), op', hop', hread i, hread j, hbin⟩
        · simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero]
          rcases canon_or_in_binOp fullMask (w.getD i 0) (w.getD j 0) with h0 | hi' | hj' | ⟨op', hop', hbin⟩
          · left; exact Or.inl h0
          · left; rw [hi']; exact hread i
          · left; rw [hj']; exact hread j
          · right; exact ⟨rfl, canon fullMask (w.getD i 0), canon fullMask (w.getD j 0), op', hop', hread i, hread j, hbin⟩
        · left; simp only [z, actionWord, List.head?_cons, Option.map_some, Option.getD_some]
          rw [canon_xor_mask]; exact hread i
    rcases hstep with hav | ⟨hbin, hgate⟩
    · have hw' : ∀ u ∈ w ++ [z], Avail bank (canon fullMask u) := by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact hw u hu
        · rw [List.mem_singleton.mp hu]; exact hav
      obtain ⟨vs, hlen, hbd, hall⟩ := ih hgs (w ++ [z]) bank hw'
      have hbc : binaryCost gs ≤ binaryCost (g :: gs) := by
        unfold binaryCost; simp only [List.filter]; cases isBinary g <;> simp
      exact ⟨vs, Nat.le_trans hlen hbc, hbd, hall⟩
    · set cz := canon fullMask z
      have hw' : ∀ u ∈ w ++ [z], Avail (cz :: bank) (canon fullMask u) := by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact avail_weaken (fun a ha => List.mem_cons_of_mem _ ha) (hw u hu)
        · rw [List.mem_singleton.mp hu]; exact Or.inr List.mem_cons_self
      obtain ⟨vs, hlen, hbd, hall⟩ := ih hgs (w ++ [z]) (cz :: bank) hw'
      have hbc : binaryCost (g :: gs) = binaryCost gs + 1 := by
        unfold binaryCost; simp [hbin]
      refine ⟨cz :: vs, by simp only [List.length_cons, hbc]; omega, ⟨hgate, hbd⟩, ?_⟩
      intro u hu
      exact avail_weaken (fun a ha => by simp only [List.mem_append, List.mem_cons] at ha ⊢; tauto) (hall u hu)

theorem foldl_evalBit (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w : List Nat) {k : Nat} (hk : k < 64) :
    gs.foldl stepBool (w.map (evalBit k)) =
      (gs.foldl (fun acc g => acc ++ [actionWord acc g]) w).map (evalBit k) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [actionWord_spec w g (hg g List.mem_cons_self) hk]
    exact ih (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (w ++ [actionWord w g])

theorem rawVars_ofFn (x : Fin 6 → Bool) :
    List.ofFn x = rawVars.map (evalBit (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) := by
  have hx : ∀ (b0 b1 b2 b3 b4 b5 : Bool),
      [b0, b1, b2, b3, b4, b5] =
      rawVars.map (evalBit ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
        (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0))) := by
    decide +kernel
  have hsum : (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) =
      (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) +
      (if x 3 then 8 else 0) + (if x 4 then 16 else 0) + (if x 5 then 32 else 0) := by
    simp [Fin.sum_univ_six]
  rw [hsum, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  exact hx (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

theorem sum_bits_6 (n : Nat) (hn : n < 64) :
    (∑ i : Fin 6, if n.testBit i.val then 2 ^ (i : Nat) else 0) = n := by
  simp only [Fin.sum_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two]
  change (if n.testBit 0 then 1 else 0) + (if n.testBit 1 then 2 else 0) +
    (if n.testBit 2 then 4 else 0) + (if n.testBit 3 then 8 else 0) +
    (if n.testBit 4 then 16 else 0) + (if n.testBit 5 then 32 else 0) = n
  revert n; decide +kernel

theorem table2_from_lowerBin (target m : Nat)
    (hlow : LowerBin fullMask rootStock (canon fullMask target) (m - 1))
    (wg : List Gate) (wout : Nat) (hsz : wg.length = m)
    (hmono : Monotone2 ⟨wg, wout⟩)
    (heval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, wout⟩ (List.ofFn x) =
      Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) :
    ∀ s : Nat, HasCircuitSize 6 (fun x : Fin 6 → Bool =>
      Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) s →
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool,
      C.eval (List.ofFn x) = Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) := by
  intro s ⟨C, hfan, hsize, hC⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, hgm, hgop⟩ := hasNot
    have hshort : binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g, hgm, by simp [isBinary, hgop]⟩
    have hleg : ∀ g ∈ C.gates, legal g := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hfan g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      exact ⟨hop, hlen⟩
    obtain ⟨vs, hvlen, hvbd, hvhit⟩ := compileBin_aux C.gates hleg rawVars rootStock rawVars_avail
    set finalW := C.gates.foldl (fun acc g => acc ++ [actionWord acc g]) rawVars
    have hout_eq : finalW.getD C.output 0 &&& fullMask = target &&& fullMask := by
      apply Nat.eq_of_testBit_eq; intro k
      by_cases hk : k < 64
      · have hfm := fullMask_bit hk
        simp only [Nat.testBit_and, hfm, Bool.and_true]
        let x : Fin 6 → Bool := fun i => k.testBit i.val
        have hxidx : (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) = k := sum_bits_6 k hk
        have h1 := hC x
        dsimp only at h1
        rw [hxidx, rawVars_ofFn x, hxidx] at h1
        change (C.gates.foldl stepBool (rawVars.map (evalBit k))).getD C.output false = target.testBit k at h1
        rw [foldl_evalBit C.gates hleg rawVars hk, readBit] at h1
        exact h1
      · have hfm0 : fullMask.testBit k = false := by
          rw [fullMask_eq, Nat.testBit_two_pow_sub_one]; simp [hk]
        simp [Nat.testBit_and, hfm0]
    have hout_avail : Avail (vs ++ rootStock) (canon fullMask target) := by
      rw [← canon_land fullMask target, ← hout_eq, canon_land]
      by_cases hi : C.output < finalW.length
      · exact hvhit _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi), canon_zero]; exact Or.inl rfl
    have hge := hlow vs hvbd hout_avail
    have hcsz : C.size = C.gates.length := rfl
    have hwsz : (⟨wg, wout⟩ : Circuit).size = m := hsz
    exact ⟨⟨wg, wout⟩, hmono, by omega, heval⟩
  · refine ⟨C, ?_, hsize, hC⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim

def memN (z : Nat) (l : List Nat) : Bool :=
  List.rec false (fun w _ ih => Bool.rec ih true (Nat.beq z w)) l

theorem memN_eq (z : Nat) (l : List Nat) : memN z l = l.contains z := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem]
  induction l with
  | nil => simp [memN]
  | cons w ws ih =>
    change Bool.rec (memN z ws) true (Nat.beq z w) = true ↔ z ∈ w :: ws
    cases h : Nat.beq z w
    · have hne : z ≠ w := ne_of_beq_false h
      simp [ih, hne]
    · have heq : z = w := Nat.eq_of_beq_eq_true h
      simp [heq]

def allN (p : Nat → Bool) (l : List Nat) : Bool :=
  List.rec true (fun w _ ih => Bool.rec false ih (p w)) l

theorem allN_eq (p : Nat → Bool) (l : List Nat) : allN p l = l.all p := by
  induction l with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec false (allN p ws) (p w) = (p w && ws.all p)
    rw [ih]; cases p w <;> rfl

def lenN (l : List Nat) : Nat :=
  List.rec 0 (fun _ _ ih => Nat.add ih 1) l

theorem lenN_eq (l : List Nat) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons _ ws ih => change Nat.add (lenN ws) 1 = ws.length + 1; rw [ih]

def appN (l r : List Nat) : List Nat :=
  List.rec r (fun w _ ih => w :: ih) l

theorem appN_eq (l r : List Nat) : appN l r = l ++ r := by
  induction l with
  | nil => rfl
  | cons w ws ih => change w :: appN ws r = w :: (ws ++ r); rw [ih]

def revAccN {α : Type} (l acc : List α) : List α :=
  (List.rec (motive := fun _ => List α → List α) (fun a => a) (fun w _ ih a => ih (w :: a)) l) acc

theorem revAccN_eq {α : Type} (l acc : List α) : revAccN l acc = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons w ws ih =>
    change revAccN ws (w :: acc) = (w :: ws).reverse ++ acc
    rw [ih, List.reverse_cons, List.append_assoc]; rfl

def getDN (l : List Nat) (i : Nat) : Nat :=
  (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun w _ ih k => Nat.rec w (fun m _ => ih m) k) l) i

theorem getDN_eq (l : List Nat) (i : Nat) : getDN l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons w ws ih =>
    cases i with
    | zero => rfl
    | succ m => change getDN ws m = (w :: ws).getD (m + 1) 0; rw [ih]; rfl

def eqListN (l1 : List Nat) : List Nat → Bool :=
  List.rec
    (fun l2 => List.rec true (fun _ _ _ => false) l2)
    (fun x _ ih l2 => List.rec false (fun y ys _ => Bool.rec false (ih ys) (Nat.beq x y)) l2) l1

theorem eqListN_eq (l1 l2 : List Nat) : eqListN l1 l2 = (l1 == l2) := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> rfl
  | cons x xs ih =>
    cases l2 with
    | nil => rfl
    | cons y ys =>
      change Bool.rec false (eqListN xs ys) (Nat.beq x y) = ((x :: xs) == (y :: ys))
      rw [ih]
      by_cases h : x = y
      · subst h; simp [Nat.beq_refl]
      · have h1 : Nat.beq x y = false := beq_false_ne h
        have h2 : (x == y) = false := beq_false_of_ne h
        simp [h1, h2]

def canonF (mask w : Nat) : Nat :=
  let v := Nat.land w mask
  Bool.rec
    (Bool.rec
      (let iv := Nat.xor mask v
       Bool.rec iv v (Nat.blt v iv))
      0 (Nat.beq v mask))
    0 (Nat.beq v 0)

theorem canonF_eq (mask w : Nat) : canonF mask w = canon mask w := by
  unfold canonF canon bsel; dsimp only
  change (Bool.rec (Bool.rec (Bool.rec (mask ^^^ (w &&& mask)) (w &&& mask) ((w &&& mask).blt (mask ^^^ (w &&& mask)))) 0 ((w &&& mask).beq mask)) 0 ((w &&& mask).beq 0) : Nat) = _
  cases Nat.beq (w &&& mask) 0 <;> cases Nat.beq (w &&& mask) mask <;> rfl

def binOpF (mask op a b : Nat) : Nat :=
  Bool.rec
    (Bool.rec
      (Bool.rec (canonF mask (Nat.land (Nat.xor mask a) b))
        (canonF mask (Nat.land a (Nat.xor mask b))) (Nat.beq op 2))
      (canonF mask (Nat.lor a b)) (Nat.beq op 1))
    (canonF mask (Nat.land a b)) (Nat.beq op 0)

theorem binOpF_eq (mask op a b : Nat) : binOpF mask op a b = binOp mask op a b := by
  unfold binOpF binOp bsel
  simp only [canonF_eq]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> rfl

def dagPartF (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Bool.rec (Nat.beq n 0) true (Nat.beq p 0))
    (fun w _ rest p n =>
      Bool.rec
        (Bool.rec
          (forceW (Nat.land p w) (fun up =>
            forceW (Nat.land n w) (fun down =>
              Bool.rec false
                (forceW (Nat.xor p up) (fun offP =>
                  forceW (Nat.xor n down) (rest offP)))
                (rest up down))))
          true (Nat.beq n 0))
        true (Nat.beq p 0)) ws

theorem dagPartF_eq (ws : List Nat) (p n : Nat) : dagPartF ws p n = dagPart ws p n := by
  induction ws generalizing p n with
  | nil =>
    change Bool.rec (Nat.beq n 0) true (Nat.beq p 0) = (Nat.beq p 0 || Nat.beq n 0)
    cases Nat.beq p 0 <;> rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (forceW (Nat.land p w) (fun up =>
      forceW (Nat.land n w) (fun down =>
        Bool.rec false (forceW (Nat.xor p up) (fun offP => forceW (Nat.xor n down) (dagPartF ws offP)))
          (dagPartF ws up down)))) true (Nat.beq n 0)) true (Nat.beq p 0) =
      ((Nat.beq p 0 || Nat.beq n 0) || forceW (p &&& w) (fun up =>
        forceW (n &&& w) (fun down => dagPart ws up down &&
          forceW (p ^^^ up) (fun offP => forceW (n ^^^ down) (dagPart ws offP)))))
    simp only [forceW_eq]
    cases Nat.beq p 0
    · cases Nat.beq n 0
      · change Bool.rec false (dagPartF ws _ _) (dagPartF ws _ _) = (dagPart ws _ _ && dagPart ws _ _)
        rw [ih, ih]; cases dagPart ws (p &&& w) (n &&& w) <;> rfl
      · rfl
    · rfl

def flatCountF (cut : Nat) (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ cnt =>
    let v := Nat.land w cut
    Bool.rec (Bool.rec cnt (Nat.add cnt 1) (Nat.beq v cut)) (Nat.add cnt 1) (Nat.beq v 0)) ws

theorem flatCountF_eq (cut : Nat) (ws : List Nat) : flatCountF cut ws = flatCount cut ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (flatCountF cut ws) (Nat.add (flatCountF cut ws) 1) (Nat.beq (Nat.land w cut) cut))
      (Nat.add (flatCountF cut ws) 1) (Nat.beq (Nat.land w cut) 0) =
      bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws)
    rw [ih]
    rcases canon_cases cut w with ⟨h0, h1 | h2⟩ | ⟨hne, _⟩
    · have hb : Nat.beq (Nat.land w cut) 0 = true := Nat.beq_eq.mpr h1
      rw [h0, hb, Nat.beq_refl]; rfl
    · have hb : Nat.beq (Nat.land w cut) cut = true := Nat.beq_eq.mpr h2
      rw [h0, hb, Nat.beq_refl]; cases Nat.beq (Nat.land w cut) 0 <;> rfl
    · have h1 : Nat.beq (Nat.land w cut) 0 = false := beq_false_ne (fun e => by
        change w &&& cut = 0 at e; exact hne (by unfold canon; dsimp only; rw [e]; simp [bsel]))
      have h2 : Nat.beq (Nat.land w cut) cut = false := beq_false_ne (fun e => by
        change w &&& cut = cut at e; exact hne (by unfold canon; dsimp only; rw [e]; simp [bsel]))
      rw [h1, h2, beq_false_ne hne]; rfl

def availBF (bank : List Nat) (w : Nat) : Bool :=
  Bool.rec (memN w bank) true (Nat.beq w 0)

theorem availBF_eq (bank : List Nat) (w : Nat) : availBF bank w = availB bank w := by
  unfold availBF availB; rw [memN_eq]; cases Nat.beq w 0 <;> rfl

def recipeGateBinF (cut : Nat) (bank : List Nat) (vc ac bc : Nat) : Bool :=
  Bool.rec false
    (Bool.rec false
      (Bool.rec
        (Bool.rec
          (Bool.rec (Nat.beq vc (binOpF cut 3 ac bc)) true (Nat.beq vc (binOpF cut 2 ac bc)))
          true (Nat.beq vc (binOpF cut 1 ac bc)))
        true (Nat.beq vc (binOpF cut 0 ac bc)))
      (availBF bank bc))
    (availBF bank ac)

theorem recipeGateBinF_eq (cut : Nat) (bank : List Nat) (vc ac bc : Nat) :
    recipeGateBinF cut bank vc ac bc = recipeGateBin cut bank vc ac bc := by
  unfold recipeGateBinF recipeGateBin
  simp only [availBF_eq, binOpF_eq]
  cases availB bank ac <;> cases availB bank bc <;>
    cases Nat.beq vc (binOp cut 0 ac bc) <;> cases Nat.beq vc (binOp cut 1 ac bc) <;>
    cases Nat.beq vc (binOp cut 2 ac bc) <;> cases Nat.beq vc (binOp cut 3 ac bc) <;> rfl

def addUniqF (w : Nat) (l : List Nat) : List Nat :=
  Bool.rec (w :: l) l (memN w l)

theorem addUniqF_eq (w : Nat) (l : List Nat) : addUniqF w l = addUniq w l := by
  unfold addUniqF addUniq; rw [memN_eq]; cases l.contains w <;> rfl

def recipeStartF (cut : Nat) (stock ws : List Nat) : List Nat :=
  List.rec [] (fun w _ acc =>
    let v := canonF cut w
    Bool.rec (addUniqF v acc) acc (availBF stock v)) ws

theorem recipeStartF_eq (cut : Nat) (stock ws : List Nat) : recipeStartF cut stock ws = recipeStart cut stock ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (addUniqF (canonF cut w) (recipeStartF cut stock ws)) (recipeStartF cut stock ws) (availBF stock (canonF cut w)) =
      (if availB stock (canon cut w) then recipeStart cut stock ws else addUniq (canon cut w) (recipeStart cut stock ws))
    rw [ih, canonF_eq, availBF_eq, addUniqF_eq]; cases availB stock (canon cut w) <;> rfl

def recipeCloseF (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      let v := canonF cut w
      Bool.rec (next acc)
        (let va := canonF cut a
         let vb := canonF cut b
         let acc1 := Bool.rec (addUniqF va acc) acc (availBF stock va)
         let acc2 := Bool.rec (addUniqF vb acc1) acc1 (availBF stock vb)
         next acc2)
        (memN v acc)) hist needed

theorem recipeCloseF_eq (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) :
    recipeCloseF cut stock hist needed = recipeClose cut stock hist needed := by
  induction hist generalizing needed with
  | nil => rfl
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    have hL : recipeCloseF cut stock ((w, a, b) :: hist) needed =
        Bool.rec (recipeCloseF cut stock hist needed)
          (let va := canonF cut a; let vb := canonF cut b
           let acc1 := Bool.rec (addUniqF va needed) needed (availBF stock va)
           let acc2 := Bool.rec (addUniqF vb acc1) acc1 (availBF stock vb)
           recipeCloseF cut stock hist acc2)
          (memN (canonF cut w) needed) := rfl
    have hR : recipeClose cut stock ((w, a, b) :: hist) needed =
        (if needed.contains (canon cut w) then
          let va := canon cut a; let vb := canon cut b
          let acc1 := if availB stock va then needed else addUniq va needed
          let acc2 := if availB stock vb then acc1 else addUniq vb acc1
          recipeClose cut stock hist acc2
        else recipeClose cut stock hist needed) := rfl
    rw [hL, hR]; dsimp only
    simp only [canonF_eq, memN_eq, availBF_eq, addUniqF_eq]
    cases needed.contains (canon cut w)
    · exact ih needed
    · dsimp only; rw [ih]
      cases availB stock (canon cut a) <;> cases availB stock (canon cut b) <;> rfl

def replayRecF (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := canonF cut w
      Bool.rec (next bank)
        (Bool.rec
          (Bool.rec (next bank) (v :: next (v :: bank))
            (recipeGateBinF cut bank v (canonF cut a) (canonF cut b)))
          (next bank) (availBF bank v))
        (memN v needed)) hist bank

theorem replayRecF_eq (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) :
    replayRecF cut needed hist bank = replayRec cut needed hist bank := by
  induction hist generalizing bank with
  | nil => rfl
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    have hL : replayRecF cut needed ((w, a, b) :: hist) bank =
        let v := canonF cut w
        Bool.rec (replayRecF cut needed hist bank)
          (Bool.rec
            (Bool.rec (replayRecF cut needed hist bank) (v :: replayRecF cut needed hist (v :: bank))
              (recipeGateBinF cut bank v (canonF cut a) (canonF cut b)))
            (replayRecF cut needed hist bank) (availBF bank v))
          (memN v needed) := rfl
    have hR : replayRec cut needed ((w, a, b) :: hist) bank =
        (let v := canon cut w
         if needed.contains v && !(availB bank v) && recipeGateBin cut bank v (canon cut a) (canon cut b) then
           v :: replayRec cut needed hist (v :: bank)
         else replayRec cut needed hist bank) := rfl
    rw [hL, hR]; dsimp only
    simp only [canonF_eq, memN_eq, availBF_eq, recipeGateBinF_eq]
    rw [ih bank, ih (canon cut w :: bank)]
    cases needed.contains (canon cut w) <;> cases availB bank (canon cut w) <;>
      cases recipeGateBin cut bank (canon cut w) (canon cut a) (canon cut b) <;> rfl

def boundClosesF (state : Nat × List Nat × List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, stock, lower, _) := bound
  let (fuel, ws, hist) := state
  forceW (Nat.sub fuel (flatCountF cut ws)) (fun rem =>
    Bool.rec false
      (forceWs (recipeStartF cut stock ws) (fun start =>
        Bool.rec false
          (Bool.rec (forceWs (recipeCloseF cut stock hist start) (fun needed =>
            Bool.rec false
              (forceWs (replayRecF cut needed (revAccN hist []) stock) (fun replay =>
                Bool.rec false
                  (allN (fun w => availBF (appN replay stock) (canonF cut w)) ws)
                  (Nat.blt (Nat.add (lenN replay) rem) lower)))
              (Nat.blt (Nat.add (lenN needed) rem) lower))) true
            (directRecipe cut stock hist start))
          (Nat.blt (Nat.add (lenN start) rem) lower)))
      (Nat.blt rem lower))

theorem boundClosesF_eq {target : Nat} {state : Nat × List Nat × List (Nat × Nat × Nat)}
    {bound : Nat × List Nat × Nat × Nat}
    (hg : canon bound.1 target = bound.2.2.2) (hnz : bound.2.2.2 ≠ 0) :
    boundClosesF state bound = boundCloses target state bound := by
  obtain ⟨fuel, ws, hist⟩ := state
  obtain ⟨cut, stock, lower, bgoal⟩ := bound
  dsimp only at hg hnz
  unfold boundClosesF boundCloses
  simp only [forceW_eq, forceWs_eq, flatCountF_eq, recipeStartF_eq, recipeCloseF_eq,
    replayRecF_eq, revAccN_eq, List.append_nil, lenN_eq, allN_eq, appN_eq, availBF_eq, canonF_eq,
    hg, Nat.beq_refl, beq_false_ne hnz, Bool.not_false, Bool.and_true, Bool.true_and]
  cases Nat.blt (fuel - flatCount cut ws) lower
  · rfl
  · cases Nat.blt ((recipeStart cut stock ws).length + (fuel - flatCount cut ws)) lower
    · rfl
    · cases directRecipe cut stock hist (recipeStart cut stock ws)
      · cases Nat.blt ((recipeClose cut stock hist (recipeStart cut stock ws)).length + (fuel - flatCount cut ws)) lower
        · rfl
        · cases Nat.blt ((replayRec cut (recipeClose cut stock hist (recipeStart cut stock ws)) hist.reverse stock).length + (fuel - flatCount cut ws)) lower <;> rfl
      · rfl

theorem recipeCloseF_nil (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) :
    recipeCloseF cut stock hist [] = [] := by
  induction hist with
  | nil => rfl
  | cons triple hist ih =>
    obtain ⟨z,x,y⟩ := triple
    exact ih

theorem replayRecF_nil (cut : Nat) (hist : List (Nat × Nat × Nat)) (stock : List Nat) :
    replayRecF cut [] hist stock = [] := by
  induction hist with
  | nil => rfl
  | cons triple hist ih =>
    obtain ⟨z,x,y⟩ := triple
    exact ih

def quickFlat (cut : Nat) (stock ws : List Nat) : Option Nat :=
  List.rec (some 0) (fun w _ rest =>
    let v := canonF cut w
    Bool.rec (Bool.rec none rest (memN v stock))
      (Option.rec none (fun n => some (Nat.add n 1)) rest) (Nat.beq v 0)) ws

private theorem quickFlat_cons (cut w : Nat) (stock ws : List Nat) :
    quickFlat cut stock (w :: ws) =
      Bool.rec none
        (Option.rec none (fun n => some (Bool.rec n (Nat.add n 1) (Nat.beq (canonF cut w) 0)))
          (quickFlat cut stock ws)) (availBF stock (canonF cut w)) := by
  let v := canonF cut w
  change Bool.rec (motive := fun _ => Option Nat)
    (Bool.rec none (quickFlat cut stock ws) (memN v stock))
    (Option.rec none (fun n => some (Nat.add n 1)) (quickFlat cut stock ws)) (Nat.beq v 0) =
      Bool.rec (motive := fun _ => Option Nat) none
        (Option.rec none (fun n => some (Bool.rec n (Nat.add n 1) (Nat.beq v 0)))
          (quickFlat cut stock ws)) (availBF stock v)
  unfold availBF
  cases Nat.beq v 0
  · cases memN v stock <;> cases quickFlat cut stock ws <;> rfl
  · rfl

private theorem quickFlat_count_cons (cut w : Nat) (ws : List Nat) :
    flatCountF cut (w :: ws) =
      Bool.rec (flatCountF cut ws) (Nat.add (flatCountF cut ws) 1) (Nat.beq (canonF cut w) 0) := by
  simp only [flatCountF_eq, canonF_eq]
  change bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws) = _
  cases Nat.beq (canon cut w) 0 <;> rfl

theorem quickFlat_eq (cut : Nat) (stock ws : List Nat) :
    quickFlat cut stock ws = Bool.rec none (some (flatCountF cut ws))
      (allN (fun w => availBF stock (canonF cut w)) ws) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [quickFlat_cons, ih, quickFlat_count_cons]
    change Bool.rec (motive := fun _ => Option Nat) none
      (Option.rec none (fun n => some (Bool.rec n (Nat.add n 1) (Nat.beq (canonF cut w) 0)))
        (Bool.rec none (some (flatCountF cut ws)) (allN (fun v => availBF stock (canonF cut v)) ws)))
      (availBF stock (canonF cut w)) =
        Bool.rec (motive := fun _ => Option Nat) none
          (some (Bool.rec (flatCountF cut ws) (Nat.add (flatCountF cut ws) 1)
            (Nat.beq (canonF cut w) 0)))
          (Bool.rec false (allN (fun v => availBF stock (canonF cut v)) ws) (availBF stock (canonF cut w)))
    generalize h : allN (fun v => availBF stock (canonF cut v)) ws = fits
    cases availBF stock (canonF cut w) <;> cases fits <;> rfl

private theorem quickFlat_start_nil (cut : Nat) (stock ws : List Nat)
    (fits : allN (fun w => availBF stock (canonF cut w)) ws = true) :
    recipeStartF cut stock ws = [] := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec false (allN (fun w => availBF stock (canonF cut w)) ws)
      (availBF stock (canonF cut w)) = true at fits
    change Bool.rec (addUniqF (canonF cut w) (recipeStartF cut stock ws))
      (recipeStartF cut stock ws) (availBF stock (canonF cut w)) = []
    cases hav : availBF stock (canonF cut w)
    · rw [hav] at fits
      contradiction
    · rw [hav] at fits
      exact ih fits

def boundClosesQuickF (state : Nat × List Nat × List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, stock, lower, _) := bound
  let (fuel, ws, _) := state
  Option.rec (boundClosesF state bound) (fun flat => Nat.blt (Nat.sub fuel flat) lower)
    (quickFlat cut stock ws)

theorem boundClosesQuickF_eq (state : Nat × List Nat × List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) :
    boundClosesQuickF state bound = boundClosesF state bound := by
  obtain ⟨fuel, ws, hist⟩ := state
  obtain ⟨cut, stock, lower, goal⟩ := bound
  unfold boundClosesQuickF
  dsimp only
  rw [quickFlat_eq]
  cases fits : allN (fun w => availBF stock (canonF cut w)) ws
  · rfl
  · have empty := quickFlat_start_nil cut stock ws fits
    have zeroAdd : Nat.add 0 (Nat.sub fuel (flatCountF cut ws)) =
        Nat.sub fuel (flatCountF cut ws) := Nat.zero_add _
    unfold boundClosesF
    simp only [forceW_eq, forceWs_eq, empty, recipeCloseF_nil, replayRecF_nil,
      lenN, appN, zeroAdd, fits, directRecipe, List.all_nil]
    cases Nat.blt (Nat.sub fuel (flatCountF cut ws)) lower <;> rfl

def knownClosesF (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  List.rec false (fun b _ rest => Bool.rec rest true (boundClosesQuickF state b)) bounds

theorem knownClosesF_eq {target : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 target = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    knownClosesF bounds state = knownCloses target bounds state := by
  induction bounds with
  | nil => rfl
  | cons b bs ih =>
    change Bool.rec (knownClosesF bs state) true (boundClosesQuickF state b) =
      (boundCloses target state b || knownCloses target bs state)
    have h0 := hgoals b List.mem_cons_self
    rw [boundClosesQuickF_eq, boundClosesF_eq h0.1 h0.2, ih (fun x hx => hgoals x (List.mem_cons_of_mem _ hx))]
    cases boundCloses target state b <;> rfl

def insertSortedF (x : Nat) (l : List Nat) : List Nat :=
  List.rec [x] (fun y ys ih => Bool.rec (y :: ih) (x :: y :: ys) (Nat.ble x y)) l

theorem insertSortedF_eq (x : Nat) (l : List Nat) : insertSortedF x l = insertSorted x l := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    change Bool.rec (y :: insertSortedF x ys) (x :: y :: ys) (Nat.ble x y) =
      bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys)
    rw [ih]; cases Nat.ble x y <;> rfl

def dropValF (drop : Bool) (x : Nat) (l : List Nat) : List Nat :=
  Bool.rec l (List.rec [] (fun y _ ih => Bool.rec (y :: ih) ih (Nat.beq y x)) l) drop

theorem dropValF_eq (drop : Bool) (x : Nat) (l : List Nat) : dropValF drop x l = dropVal drop x l := by
  cases drop
  · rfl
  · induction l with
    | nil => rfl
    | cons y ys ih =>
      change Bool.rec (y :: dropValF true x ys) (dropValF true x ys) (Nat.beq y x) =
        bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys)
      rw [ih]; cases Nat.beq y x <;> rfl

def subsetWordsF (stock : List Nat) (bits : Nat) : List Nat :=
  (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih b =>
      let rest := ih (Nat.shiftRight b 1)
      Bool.rec rest (insertSortedF w rest) (Nat.beq (Nat.land b 1) 1)) stock) bits

theorem subsetWordsF_eq (stock : List Nat) (bits : Nat) : subsetWordsF stock bits = subsetWords stock bits := by
  induction stock generalizing bits with
  | nil => rfl
  | cons x xs ih =>
    change Bool.rec (subsetWordsF xs (Nat.shiftRight bits 1))
      (insertSortedF x (subsetWordsF xs (Nat.shiftRight bits 1))) (Nat.beq (Nat.land bits 1) 1) =
      bsel (Nat.beq (bits &&& 1) 1) (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1))
    rw [ih, insertSortedF_eq]; cases Nat.beq (bits &&& 1) 1 <;> rfl

def childStateF (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, hist) := state
  let keep := Nat.land token 3
  let op := Nat.land (Nat.shiftRight token 2) 3
  let b := Nat.land (Nat.shiftRight token 4) 15
  let a := Nat.shiftRight token 8
  Bool.rec
    (Bool.rec none
      (Bool.rec none
        (let x := getDN ws a
         let y := getDN ws b
         let z := binOpF mask op x y
         Bool.rec
           (Bool.rec
             (let keepA := Nat.beq (Nat.land keep 1) 1
              let keepB := Nat.beq (Nat.land (Nat.shiftRight keep 1) 1) 1
              let rest := dropValF (Bool.rec true false keepA) x (dropValF (Bool.rec true false keepB) y ws)
              some (Nat.sub fuel 1, insertSortedF z rest, (z, x, y) :: hist))
             none (memN z ws))
           none (Nat.beq z 0))
        (Nat.blt b (lenN ws)))
      (Nat.blt a b))
    none (Nat.beq fuel 0)

theorem childStateF_eq (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    childStateF mask token state = childState mask token state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold childStateF childState
  simp only [lenN_eq, getDN_eq, binOpF_eq, memN_eq, dropValF_eq, insertSortedF_eq]
  cases Nat.beq fuel 0
  · cases Nat.blt (token >>> 8) ((token >>> 4) &&& 15)
    · rfl
    · cases Nat.blt ((token >>> 4) &&& 15) ws.length
      · rfl
      · cases Nat.beq (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0) (ws.getD ((token >>> 4) &&& 15) 0)) 0
        · cases ws.contains (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0) (ws.getD ((token >>> 4) &&& 15) 0))
          · cases Nat.beq ((token &&& 3) &&& 1) 1 <;> cases Nat.beq (((token &&& 3) >>> 1) &&& 1) 1 <;> rfl
          · rfl
        · rfl
  · rfl

def dagTraceF (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ prev j =>
      let (parent, token) := forest j
      Bool.rec
        (match prev (Nat.sub parent 1) with
         | none => none
         | some st => childStateF mask token st)
        (Bool.rec none (some (fuel, subsetWordsF stock token, []))
          (Nat.blt token (Nat.shiftLeft 1 (lenN stock))))
        (Nat.beq parent 0)) (Nat.add fuel 1)) i

theorem dagTraceF_eq (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    dagTraceF mask stock fuel forest i = dagTrace mask stock fuel forest i := by
  unfold dagTraceF dagTrace
  suffices ∀ steps j,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          Bool.rec
            (match prev (Nat.sub parent 1) with
             | none => none
             | some st => childStateF mask token st)
            (Bool.rec none (some (fuel, subsetWordsF stock token, []))
              (Nat.blt token (Nat.shiftLeft 1 (lenN stock))))
            (Nat.beq parent 0)) steps) j =
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j from
    this (fuel + 1) i
  intro steps
  induction steps with
  | zero => intro j; rfl
  | succ n ih =>
    intro j
    dsimp only
    have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
      rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
    cases Nat.beq (forest j).1 0
    · dsimp only
      rw [ih]
      cases (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          if Nat.beq (forest k).1 0 then
            if Nat.blt (forest k).2 (2 ^ stock.length) then some (rootState stock fuel (forest k).2) else none
          else (prev ((forest k).1 - 1)).bind (childState mask (forest k).2)) n) ((forest j).1 - 1)
      · rfl
      · exact childStateF_eq mask (forest j).2 _
    · dsimp only
      rw [hpow, subsetWordsF_eq]
      cases Nat.blt (forest j).2 (2 ^ stock.length) <;> rfl

def dagLocalF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, _) := state
  Bool.rec
    (Bool.rec true
      (knownClosesF bounds state)
      (dagPartF ws goal (Nat.xor mask goal)))
    true (Nat.blt (Nat.add fuel 1) (lenN ws))

theorem dagLocalF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    dagLocalF mask goal bounds state = dagLocal mask goal bounds state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold dagLocalF dagLocal; dsimp only
  rw [lenN_eq, dagPartF_eq, knownClosesF_eq hgoals]
  cases Nat.blt (fuel + 1) ws.length <;> cases dagPart ws goal (mask ^^^ goal) <;> rfl

def dagRefF (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (parent token : Nat)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  match links parent token with
  | none => false
  | some dest =>
    Bool.rec false
      (match states dest with
       | none => false
       | some saved => Bool.rec false (eqListN saved.2.1 state.2.1) (Nat.beq saved.1 state.1))
      (Nat.blt dest count)

def treeBlockF (lo hi : Nat) (f : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      Bool.rec true
        (let m := Nat.shiftRight (Nat.add a b) 1
         Bool.rec (Bool.rec false (next m b) (next a m)) (f a) (Nat.beq a m))
        (Nat.blt a b)) (Nat.add (Nat.sub hi lo) 1)) lo hi

abbrev BlockChecked (f : Nat → Bool) (lo hi : Nat) : Prop :=
  treeBlockF lo hi f = true

theorem treeBlockF_eq (lo hi : Nat) (f : Nat → Bool) : treeBlockF lo hi f = treeBlock lo hi f := by
  unfold treeBlockF treeBlock
  suffices ∀ steps a b,
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          Bool.rec true
            (let m := Nat.shiftRight (Nat.add x y) 1
             Bool.rec (Bool.rec false (next m y) (next x m)) (f x) (Nat.beq x m))
            (Nat.blt x y)) steps) a b =
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b from
    this (hi - lo + 1) lo hi
  intro steps
  induction steps with
  | zero => intro a b; rfl
  | succ s ih =>
    intro a b
    dsimp only
    have hdiv : Nat.shiftRight (Nat.add a b) 1 = (a + b) / 2 := by
      change (a + b) >>> 1 = (a + b) / 2; rw [Nat.shiftRight_eq_div_pow]
    rw [hdiv]
    cases Nat.blt a b
    · rfl
    · cases Nat.beq a ((a + b) / 2)
      · rw [ih, ih]
        change Bool.rec false _ _ = (_ && _)
        cases (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true) _ s) a ((a + b) / 2) <;> rfl
      · rfl

theorem dagPart_false_of_agreement {ws : List Nat} {pos neg p n : Nat}
    (hp : pos.testBit p = true) (hn : neg.testBit n = true)
    (ag : ∀ w ∈ ws, w.testBit p = w.testBit n) : dagPart ws pos neg = false := by
  have nonzero {v i : Nat} (h : v.testBit i = true) : v ≠ 0 := by
    rintro rfl
    simp at h
  induction ws generalizing pos neg with
  | nil => simp [dagPart, beq_false_ne (nonzero hp), beq_false_ne (nonzero hn)]
  | cons w ws ih =>
    change ((Nat.beq pos 0 || Nat.beq neg 0) ||
      forceW (pos &&& w) (fun up => forceW (neg &&& w) (fun down =>
        dagPart ws up down && forceW (pos ^^^ up) (fun offP =>
          forceW (neg ^^^ down) (dagPart ws offP))))) = false
    simp only [forceW_eq, beq_false_ne (nonzero hp), beq_false_ne (nonzero hn), Bool.false_or,
      Bool.and_eq_false_iff]
    have tail : ∀ v ∈ ws, v.testBit p = v.testBit n := fun v hv => ag v (List.mem_cons_of_mem _ hv)
    have wh := ag w List.mem_cons_self
    cases h : w.testBit p
    · right
      have h' : w.testBit n = false := wh.symm.trans h
      exact ih (by simp [Nat.testBit_and, Nat.testBit_xor, hp, h])
        (by simp [Nat.testBit_and, Nat.testBit_xor, hn, h']) tail
    · left
      have h' : w.testBit n = true := wh.symm.trans h
      exact ih (by simp [Nat.testBit_and, hp, h]) (by simp [Nat.testBit_and, hn, h']) tail


def wireSig : List Nat → Nat → Nat
  | [], _ => 0
  | w :: ws, row => (w.testBit row).toNat ||| (wireSig ws row <<< 1)

theorem wireSig_testBit (ws : List Nat) (row i : Nat) :
    (wireSig ws row).testBit i = (ws.getD i 0).testBit row := by
  induction ws generalizing i with
  | nil => simp [wireSig]
  | cons w ws ih =>
    cases i with
    | zero =>
      simp only [wireSig, Nat.testBit_or, Nat.testBit_bool_toNat, Nat.testBit_shiftLeft]
      simp
    | succ i =>
      simpa [wireSig, Nat.testBit_bool_toNat, List.getD_cons_succ] using ih i

/-- Bit `s` records whether any of the included rows has wire signature `s`. -/
def sigOccupied (ws : List Nat) (rows : Nat) : Nat → Nat :=
  Nat.rec 0 (fun row smaller =>
    Bool.rec smaller ((1 <<< wireSig ws row) ||| smaller) (rows.testBit row))

theorem sigOccupied_testBit (ws : List Nat) (rows width s : Nat) :
    (sigOccupied ws rows width).testBit s = true ↔
      ∃ r, r < width ∧ rows.testBit r = true ∧ wireSig ws r = s := by
  induction width with
  | zero => simp [sigOccupied]
  | succ width ih =>
    have bound (r : Nat) : r < width + 1 ↔ r = width ∨ r < width := by omega
    change (Bool.rec (motive := fun _ => Nat) (sigOccupied ws rows width)
      ((1 <<< wireSig ws width) ||| sigOccupied ws rows width)
      (rows.testBit width)).testBit s = true ↔ _
    cases bit : rows.testBit width <;>
      simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_or, Nat.testBit_two_pow,
        Bool.or_eq_true, decide_eq_true_eq, ih]
    · constructor
      · rintro ⟨r, hr, hit, eq⟩
        exact ⟨r, by omega, hit, eq⟩
      · rintro ⟨r, hr, hit, eq⟩
        rcases (bound r).mp hr with rfl | lt
        · exact Bool.noConfusion (bit.symm.trans hit)
        · exact ⟨r, lt, hit, eq⟩
    · constructor
      · rintro (eq | ⟨r, hr, hit, eq⟩)
        · exact ⟨width, Nat.lt_succ_self _, bit, eq⟩
        · exact ⟨r, by omega, hit, eq⟩
      · rintro ⟨r, hr, hit, eq⟩
        rcases (bound r).mp hr with rfl | lt
        · exact Or.inl eq
        · exact Or.inr ⟨r, lt, hit, eq⟩


def sigCross (p n offset : Nat) : Nat :=
  (p &&& (n >>> offset)) ||| (n &&& (p >>> offset))

theorem sigCross_rows {ws : List Nat} {pos neg width offset v : Nat}
    (hit : (sigCross (sigOccupied ws pos width) (sigOccupied ws neg width) offset).testBit v = true) :
    ∃ l r, wireSig ws l = v ∧ wireSig ws r = v + offset ∧
      ((pos.testBit l = true ∧ neg.testBit r = true) ∨
       (neg.testBit l = true ∧ pos.testBit r = true)) := by
  simp only [sigCross, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, Bool.or_eq_true,
    Bool.and_eq_true, sigOccupied_testBit] at hit
  rcases hit with ⟨⟨l, _, hl, eqL⟩, ⟨r, _, hr, eqR⟩⟩ | ⟨⟨l, _, hl, eqL⟩, ⟨r, _, hr, eqR⟩⟩
  · exact ⟨l, r, eqL, eqR.trans (Nat.add_comm _ _), Or.inl ⟨hl, hr⟩⟩
  · exact ⟨l, r, eqL, eqR.trans (Nat.add_comm _ _), Or.inr ⟨hl, hr⟩⟩

def sigUnit (i : Nat) (bit : Bool) : Nat := Bool.rec 0 (1 <<< i) bit

private theorem sigUnit_testBit (i j : Nat) (b : Bool) :
    (sigUnit i b).testBit j = (decide (i = j) && b) := by
  cases b <;> simp [sigUnit, Nat.shiftLeft_eq, Nat.testBit_two_pow]

def sigPatternVal (a b pat : Nat) : Nat :=
  sigUnit a (pat.testBit 0) ||| sigUnit b (pat.testBit 1)

private theorem sigPatternVal_testBit (a b pat i : Nat) : (sigPatternVal a b pat).testBit i =
    ((decide (a = i) && pat.testBit 0) || (decide (b = i) && pat.testBit 1)) := by
  simp only [sigPatternVal, Nat.testBit_or, sigUnit_testBit]

def SigPattern (a b pat v : Nat) : Prop :=
  v.testBit a = pat.testBit 0 ∧ v.testBit b = pat.testBit 1

private theorem sigOr_eq_add {x y : Nat} (disjoint : x &&& y = 0) : x ||| y = x + y := by
  induction y using Nat.div2Induction generalizing x with
  | ind y ih =>
    rcases Nat.eq_zero_or_pos y with rfl | pos
    · simp
    have modZero : (x % 2) &&& (y % 2) = 0 := by
      have h := Nat.and_mod_two_pow (a := x) (b := y) (n := 1)
      rw [disjoint] at h
      exact h.symm
    have divZero : (x / 2) &&& (y / 2) = 0 := by rw [← Nat.and_div_two, disjoint]
    have high := ih pos (x := x / 2) divZero
    have low : (x % 2) ||| (y % 2) = x % 2 + y % 2 := by
      rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;>
      simp [hx, hy] at modZero ⊢
    rw [← Nat.mod_add_div (x ||| y) 2, Nat.or_mod_two, Nat.or_div_two, high, low]
    have hx := Nat.mod_add_div x 2
    have hy := Nat.mod_add_div y 2
    omega

/-- Adding the difference between two valid patterns changes only those two wire bits. -/
theorem sigPattern_shift {a b lo hi v : Nat} (ab : a ≠ b)
    (hp : SigPattern a b lo v) (increasing : sigPatternVal a b lo ≤ sigPatternVal a b hi) :
    let next := v + (sigPatternVal a b hi - sigPatternVal a b lo)
    SigPattern a b hi next ∧ ∀ i, i ≠ a → i ≠ b → v.testBit i = next.testBit i := by
  let clear := v ^^^ sigPatternVal a b lo
  have bits (i : Nat) : clear.testBit i = if i = a ∨ i = b then false else v.testBit i := by
    by_cases ha : i = a
    · subst i
      simp [clear, Nat.testBit_xor, sigPatternVal_testBit, ab.symm, hp.1]
    · by_cases hb : i = b
      · subst i
        simp [clear, Nat.testBit_xor, sigPatternVal_testBit, ab, hp.2]
      · simp [clear, Nat.testBit_xor, sigPatternVal_testBit, ha, hb, Ne.symm ha, Ne.symm hb]
  have old : clear ||| sigPatternVal a b lo = v := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_or, bits, sigPatternVal_testBit]
    by_cases ha : i = a
    · subst i; simp [ab.symm, hp.1]
    · by_cases hb : i = b
      · subst i; simp [ab, hp.2]
      · simp [ha, hb, Ne.symm ha, Ne.symm hb]
  have disj (pat : Nat) : clear &&& sigPatternVal a b pat = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, bits, sigPatternVal_testBit]
    by_cases included : i = a ∨ i = b
    · simp [included]
    · obtain ⟨ha, hb⟩ := not_or.mp included
      simp [included, Ne.symm ha, Ne.symm hb]
  have sum : v + (sigPatternVal a b hi - sigPatternVal a b lo) = clear ||| sigPatternVal a b hi := by
    have orig := (sigOr_eq_add (disj lo)).symm.trans old
    rw [sigOr_eq_add (disj hi)]
    omega
  change SigPattern a b hi (v + (sigPatternVal a b hi - sigPatternVal a b lo)) ∧ _
  rw [sum]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [Nat.testBit_or, bits, sigPatternVal_testBit, ab.symm]
  · simp [Nat.testBit_or, bits, sigPatternVal_testBit, ab]
  · intro i ha hb
    simp [Nat.testBit_or, bits, sigPatternVal_testBit, ha, hb, Ne.symm ha, Ne.symm hb]

theorem sigCross_pattern_sound {ws : List Nat} {pos neg width a b lo hi guard : Nat}
    (ab : a ≠ b) (increasing : sigPatternVal a b lo ≤ sigPatternVal a b hi)
    (guard_ok : ∀ i, guard.testBit i = true → SigPattern a b lo i)
    (hit : (sigCross (sigOccupied ws pos width) (sigOccupied ws neg width)
      (sigPatternVal a b hi - sigPatternVal a b lo) &&& guard) ≠ 0) :
    ∃ l r, ((pos.testBit l = true ∧ neg.testBit r = true) ∨
            (neg.testBit l = true ∧ pos.testBit r = true)) ∧
      SigPattern a b lo (wireSig ws l) ∧ SigPattern a b hi (wireSig ws r) ∧
      ∀ i, i ≠ a → i ≠ b → (ws.getD i 0).testBit l = (ws.getD i 0).testBit r := by
  have bit := Nat.testBit_log2 hit
  rw [Nat.testBit_and, Bool.and_eq_true] at bit
  obtain ⟨l, r, eqL, eqR, side⟩ := sigCross_rows bit.1
  have hp := guard_ok _ bit.2
  obtain ⟨hq, same⟩ := sigPattern_shift ab hp increasing
  refine ⟨l, r, side, eqL ▸ hp, eqR ▸ hq, ?_⟩
  intro i ha hb
  rw [← wireSig_testBit ws l, ← wireSig_testBit ws r, eqL, eqR]
  exact same i ha hb


/-- Low runs of length `2^i`, duplicated at successively larger steps. -/
def sigZeroStripe (i : Nat) : Nat → Nat :=
  Nat.rec ((1 <<< (1 <<< i)) - 1) (fun k prev =>
    prev ||| (prev <<< (1 <<< (i + 1 + k))))

theorem sigZeroStripe_sound {i steps v : Nat} (hit : (sigZeroStripe i steps).testBit v = true) :
    v.testBit i = false := by
  induction steps generalizing v with
  | zero =>
    change ((1 <<< (1 <<< i)) - 1).testBit v = true at hit
    simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one,
      decide_eq_true_eq] at hit
    exact Nat.testBit_lt_two_pow hit
  | succ k ih =>
    change (sigZeroStripe i k ||| (sigZeroStripe i k <<< (1 <<< (i + 1 + k)))).testBit v = true at hit
    rw [Nat.testBit_or, Nat.testBit_shiftLeft] at hit
    simp only [Nat.shiftLeft_eq, Nat.one_mul, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hit
    rcases hit with low | ⟨ge, high⟩
    · exact ih low
    · calc
        v.testBit i = (2^(i + 1 + k) + (v - 2^(i + 1 + k))).testBit i := by
          congr 1
          omega
        _ = (v - 2^(i + 1 + k)).testBit i := Nat.testBit_two_pow_add_gt (by omega) _
        _ = false := ih high

def sigStripeTable : List Nat := [0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555, 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff]

theorem sigStripeTable_eq : ∀ i : Fin 9,
    getDN sigStripeTable i.val = sigZeroStripe i.val (9 - (i.val + 1)) := by decide +kernel

def sigStripeCached (width i : Nat) : Nat :=
  Bool.rec (sigZeroStripe i (width - (i + 1))) (getDN sigStripeTable i) (Nat.blt i 9)

theorem sigStripeCached_sound {width i v : Nat}
    (hit : (sigStripeCached width i).testBit v = true) : v.testBit i = false := by
  unfold sigStripeCached at hit
  cases hi : Nat.blt i 9 with
  | false =>
    rw [hi] at hit
    exact sigZeroStripe_sound hit
  | true =>
    rw [hi] at hit
    change (getDN sigStripeTable i).testBit v = true at hit
    have exactIndex : i < 9 := Nat.blt_eq.mp hi
    rw [sigStripeTable_eq ⟨i, exactIndex⟩] at hit
    exact sigZeroStripe_sound hit

def sigBitGuard (width i : Nat) (on : Bool) : Nat :=
  let zeros := sigStripeCached width i
  Bool.rec zeros (zeros <<< (1 <<< i)) on

theorem sigBitGuard_sound {width i v : Nat} {on : Bool}
    (hit : (sigBitGuard width i on).testBit v = true) : v.testBit i = on := by
  cases on
  · exact sigStripeCached_sound hit
  · change ((sigStripeCached width i) <<< (1 <<< i)).testBit v = true at hit
    rw [Nat.testBit_shiftLeft] at hit
    simp only [Nat.shiftLeft_eq, Nat.one_mul, Bool.and_eq_true, decide_eq_true_eq] at hit
    calc
      v.testBit i = (2^i + (v - 2^i)).testBit i := by
        congr 1
        have ge := hit.1
        omega
      _ = !(v - 2^i).testBit i := Nat.testBit_two_pow_add_eq _ _
      _ = true := by simp [sigStripeCached_sound hit.2]

def sigPatternGuard (width a b pat : Nat) : Nat :=
  sigBitGuard width a (pat.testBit 0) &&& sigBitGuard width b (pat.testBit 1)

theorem sigPatternGuard_sound {width a b pat v : Nat}
    (hit : (sigPatternGuard width a b pat).testBit v = true) : SigPattern a b pat v := by
  simp only [sigPatternGuard, Nat.testBit_and, Bool.and_eq_true] at hit
  exact ⟨sigBitGuard_sound hit.1, sigBitGuard_sound hit.2⟩


def sigPairLo (i : Nat) : Nat := ([0, 0, 0, 1, 1, 2] : List Nat).getD i 0
def sigPairHi (i : Nat) : Nat := ([1, 2, 3, 2, 3, 3] : List Nat).getD i 0

private theorem sigPatternVal0 (a b : Nat) : sigPatternVal a b 0 = 0 := by
  simp [sigPatternVal, sigUnit]
private theorem sigPatternVal1 (a b : Nat) : sigPatternVal a b 1 = 1 <<< a := by
  change (1 <<< a) ||| 0 = _
  simp
private theorem sigPatternVal2 (a b : Nat) : sigPatternVal a b 2 = 1 <<< b := by
  change 0 ||| (1 <<< b) = _
  simp
private theorem sigPatternVal3 {a b : Nat} (ab : a ≠ b) :
    sigPatternVal a b 3 = (1 <<< a) + (1 <<< b) := by
  change (1 <<< a) ||| (1 <<< b) = _
  apply sigOr_eq_add
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow, Nat.zero_testBit]
  by_cases h : a = i
  · subst i
    simp [ab.symm]
  · simp [h]

private theorem sigGuard0 (width a b : Nat) :
    (sigStripeCached width a &&& sigStripeCached width b) = sigPatternGuard width a b 0 := rfl
private theorem sigGuard1 (width a b : Nat) :
    ((sigStripeCached width a <<< (1 <<< a)) &&& sigStripeCached width b) = sigPatternGuard width a b 1 := rfl
private theorem sigGuard2 (width a b : Nat) :
    (sigStripeCached width a &&& (sigStripeCached width b <<< (1 <<< b))) = sigPatternGuard width a b 2 := rfl

def sigPairCode (p n width a b : Nat) : Nat :=
  if a < b then
    let va := 1 <<< a
    let vb := 1 <<< b
    forceW (sigStripeCached width a) fun sa =>
    forceW (sigStripeCached width b) fun sb =>
    forceW (sa &&& sb) fun g0 =>
    forceW ((sa <<< va) &&& sb) fun g1 =>
    forceW (sa &&& (sb <<< vb)) fun g2 =>
    forceW (sigCross p n va) fun ca =>
    forceW (sigCross p n vb) fun cb =>
    forceW (sigCross p n (va + vb)) fun cs =>
    forceW (sigCross p n (vb - va)) fun cd =>
      sigUnit 0 (!(Nat.beq (ca &&& g0) 0)) ||| sigUnit 1 (!(Nat.beq (cb &&& g0) 0)) |||
        sigUnit 2 (!(Nat.beq (cs &&& g0) 0)) ||| sigUnit 3 (!(Nat.beq (cd &&& g1) 0)) |||
        sigUnit 4 (!(Nat.beq (cb &&& g1) 0)) ||| sigUnit 5 (!(Nat.beq (ca &&& g2) 0))
  else 0

theorem sigPairCode_witness {p n width a b i : Nat}
    (hit : (sigPairCode p n width a b).testBit i = true) :
    a < b ∧ i < 6 ∧ sigPatternVal a b (sigPairLo i) ≤ sigPatternVal a b (sigPairHi i) ∧
      ((sigCross p n (sigPatternVal a b (sigPairHi i) - sigPatternVal a b (sigPairLo i))) &&&
        sigPatternGuard width a b (sigPairLo i)) ≠ 0 := by
  by_cases ab : a < b
  · have vp : (1 : Nat) <<< a ≤ 1 <<< b := by
      simp only [Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.pow_le_pow_right (by decide) ab.le
    have val := sigPatternVal3 ab.ne
    simp only [sigPairCode, ab, ite_true, forceW_eq, sigGuard0, sigGuard1, sigGuard2, Nat.testBit_or, sigUnit_testBit,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hit
    rcases hit with (((((⟨rfl, hit⟩ | ⟨rfl, hit⟩) | ⟨rfl, hit⟩) | ⟨rfl, hit⟩) | ⟨rfl, hit⟩) | ⟨rfl, hit⟩)
    all_goals
      have nz := ne_of_beq_false hit
      refine ⟨ab, by decide, ?_, ?_⟩
      · simp [sigPairLo, sigPairHi, sigPatternVal0, sigPatternVal1, sigPatternVal2, val, vp]
      · simpa [sigPairLo, sigPairHi, sigPatternVal0, sigPatternVal1, sigPatternVal2, val] using nz
  · simp [sigPairCode, ab] at hit

def sigRawGate (op : Nat) (x y : Bool) : Bool :=
  bsel (Nat.beq op 0) (x && y)
    (bsel (Nat.beq op 1) (x || y) (bsel (Nat.beq op 2) (x && !y) (!x && y)))

def sigRuleMask (op keep : Nat) : Nat :=
  if op < 4 ∧ keep < 4 then
    (([[11, 2, 1, 0], [56, 16, 32, 0], [38, 2, 32, 0], [21, 16, 1, 0]] :
      List (List Nat)).getD op []).getD keep 0
  else 0

private theorem sigRuleMask_small : ∀ (op keep : Fin 4) (i : Fin 6),
    (sigRuleMask op.val keep.val).testBit i.val = true →
    (Nat.beq (keep.val &&& 1) 1 = true → (sigPairLo i.val).testBit 0 = (sigPairHi i.val).testBit 0) ∧
    (Nat.beq ((keep.val >>> 1) &&& 1) 1 = true → (sigPairLo i.val).testBit 1 = (sigPairHi i.val).testBit 1) ∧
    sigRawGate op.val ((sigPairLo i.val).testBit 0) ((sigPairLo i.val).testBit 1) =
      sigRawGate op.val ((sigPairHi i.val).testBit 0) ((sigPairHi i.val).testBit 1) := by decide +kernel

theorem sigRuleMask_sound {op keep i : Nat} (hi : i < 6)
    (h : (sigRuleMask op keep).testBit i = true) :
    (Nat.beq (keep &&& 1) 1 = true → (sigPairLo i).testBit 0 = (sigPairHi i).testBit 0) ∧
    (Nat.beq ((keep >>> 1) &&& 1) 1 = true → (sigPairLo i).testBit 1 = (sigPairHi i).testBit 1) ∧
    sigRawGate op ((sigPairLo i).testBit 0) ((sigPairLo i).testBit 1) =
      sigRawGate op ((sigPairHi i).testBit 0) ((sigPairHi i).testBit 1) := by
  by_cases bounds : op < 4 ∧ keep < 4
  · exact sigRuleMask_small ⟨op, bounds.1⟩ ⟨keep, bounds.2⟩ ⟨i, hi⟩ h
  · simp [sigRuleMask, bounds] at h

def sigPairPrune (code op keep : Nat) : Bool := !(Nat.beq (code &&& sigRuleMask op keep) 0)


private theorem sigBinOp_agrees {mask op x y p n : Nat}
    (hp : mask.testBit p = true) (hn : mask.testBit n = true)
    (eq : sigRawGate op (x.testBit p) (y.testBit p) = sigRawGate op (x.testBit n) (y.testBit n)) :
    (binOp mask op x y).testBit p = (binOp mask op x y).testBit n := by
  unfold binOp sigRawGate at *
  cases e0 : Nat.beq op 0 <;> cases e1 : Nat.beq op 1 <;> cases e2 : Nat.beq op 2 <;>
    simp only [e0, e1, e2, bsel_true, bsel_false] at eq ⊢ <;>
    apply (canon_testBit_eq hp hn).mpr <;>
    simpa [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, hp, hn] using eq

private theorem sigNeg_care {mask goal row : Nat}
    (hit : (mask ^^^ (goal &&& mask)).testBit row = true) :
    (mask ^^^ goal).testBit row = true ∧ mask.testBit row = true := by
  simp only [Nat.testBit_xor, Nat.testBit_and] at hit ⊢
  cases hm : mask.testBit row <;> cases hg : goal.testBit row <;> simp_all

theorem sigPairPrune_part {mask goal a b op keep : Nat} {ws : List Nat}
    (hit : sigPairPrune (sigPairCode (sigOccupied ws (goal &&& mask) 64)
      (sigOccupied ws (mask ^^^ (goal &&& mask)) 64) ws.length a b) op keep = true) :
    let x := ws.getD a 0
    let y := ws.getD b 0
    let z := binOp mask op x y
    let keepA := Nat.beq (keep &&& 1) 1
    let keepB := Nat.beq ((keep >>> 1) &&& 1) 1
    dagPart (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws)))
      goal (mask ^^^ goal) = false := by
  simp only [sigPairPrune, Bool.not_eq_true'] at hit
  have bit := Nat.testBit_log2 (ne_of_beq_false hit)
  rw [Nat.testBit_and, Bool.and_eq_true] at bit
  obtain ⟨ab, pair_bound, increasing, cross⟩ := sigPairCode_witness bit.1
  have valid := sigRuleMask_sound pair_bound bit.2
  obtain ⟨l, r, signs, lo, hi, same⟩ :=
    sigCross_pattern_sound ab.ne increasing (fun _ => sigPatternGuard_sound) cross
  have ⟨al, bl⟩ := lo
  have ⟨ar, br⟩ := hi
  rw [wireSig_testBit] at al bl ar br
  have pos {row} (yes : (goal &&& mask).testBit row = true) :
      goal.testBit row = true ∧ mask.testBit row = true := by
    simpa only [Nat.testBit_and, Bool.and_eq_true] using yes
  have care : mask.testBit l = true ∧ mask.testBit r = true := by
    rcases signs with ⟨hp, hn⟩ | ⟨hn, hp⟩
    · exact ⟨(pos hp).2, (sigNeg_care hn).2⟩
    · exact ⟨(sigNeg_care hn).2, (pos hp).2⟩
  have gate := sigBinOp_agrees care.1 care.2 (x := ws.getD a 0) (y := ws.getD b 0) (op := op) (by
    rw [al, bl, ar, br]
    exact valid.2.2)
  dsimp only
  have agrees : ∀ w ∈ insertSorted (binOp mask op (ws.getD a 0) (ws.getD b 0))
      (dropVal (!(Nat.beq (keep &&& 1) 1)) (ws.getD a 0)
        (dropVal (!(Nat.beq ((keep >>> 1) &&& 1) 1)) (ws.getD b 0) ws)),
      w.testBit l = w.testBit r := by
    intro w hw
    rcases insertSorted_mem.mp hw with rfl | mem
    · exact gate
    · obtain ⟨earlier, dropA⟩ := dropVal_mem.mp mem
      obtain ⟨stock, dropB⟩ := dropVal_mem.mp earlier
      obtain ⟨i, _, iw⟩ := getElem_index_lt stock
      rw [← iw]
      by_cases ia : i = a
      · subst i
        have keepA : Nat.beq (keep &&& 1) 1 = true := by
          cases e : Nat.beq (keep &&& 1) 1
          · exact (dropA (by rw [e, Bool.not_false]) iw.symm).elim
          · rfl
        exact al.trans ((valid.1 keepA).trans ar.symm)
      · by_cases ib : i = b
        · subst i
          have keepB : Nat.beq ((keep >>> 1) &&& 1) 1 = true := by
            cases e : Nat.beq ((keep >>> 1) &&& 1) 1
            · exact (dropB (by rw [e, Bool.not_false]) iw.symm).elim
            · rfl
          exact bl.trans ((valid.2.1 keepB).trans br.symm)
        · exact same i ia ib
  rcases signs with ⟨hp, hn⟩ | ⟨hn, hp⟩
  · exact dagPart_false_of_agreement (pos hp).1 (sigNeg_care hn).1 agrees
  · exact dagPart_false_of_agreement (pos hp).1 (sigNeg_care hn).1 (fun w hw => (agrees w hw).symm)

def sigDagPos (mask goal : Nat) (ws : List Nat) : Nat :=
  if mask = fullMask then sigOccupied ws (goal &&& mask) 64 else 0

def sigDagNeg (mask goal : Nat) (ws : List Nat) : Nat :=
  if mask = fullMask then sigOccupied ws (mask ^^^ (goal &&& mask)) 64 else 0

def sigDagCode (mask p n width a b : Nat) : Nat :=
  if mask = fullMask then sigPairCode p n width a b else 0

def sigDagLocalF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) (linked : Bool) : Bool :=
  if mask = fullMask then
    let (fuel, ws, _) := state
    Bool.rec (Bool.rec (Bool.rec (Bool.rec true false (dagPartF ws goal (Nat.xor mask goal)))
      true linked) true (knownClosesF bounds state)) true (Nat.blt (Nat.add fuel 1) (lenN ws))
  else Bool.rec linked true (dagLocalF mask goal bounds state)

theorem sigDagLocalF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) (linked : Bool) :
    sigDagLocalF mask goal bounds state linked = (dagLocal mask goal bounds state || linked) := by
  by_cases big : mask = fullMask
  · obtain ⟨fuel, ws, hist⟩ := state
    simp only [sigDagLocalF, ite_eq_left big, lenN_eq, dagPartF_eq, knownClosesF_eq hgoals, dagLocal]
    cases Nat.blt (fuel + 1) ws.length <;> cases dagPart ws goal (mask ^^^ goal) <;>
      cases knownCloses goal bounds (fuel, ws, hist) <;> cases linked <;> rfl
  · simp only [sigDagLocalF, ite_eq_right big, dagLocalF_eq hgoals]
    cases dagLocal mask goal bounds state <;> rfl

theorem sigDagPrune_or_eq (mask goal a b op keep fuel : Nat) (ws : List Nat)
    (hist : List (Nat × Nat × Nat)) (bounds : List (Nat × List Nat × Nat × Nat)) (linked : Bool) :
    let x := ws.getD a 0
    let y := ws.getD b 0
    let z := binOp mask op x y
    let keepA := Nat.beq (keep &&& 1) 1
    let keepB := Nat.beq ((keep >>> 1) &&& 1) 1
    let state := (fuel, insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws)), hist)
    let prune := sigPairPrune (sigDagCode mask (sigDagPos mask goal ws) (sigDagNeg mask goal ws)
      ws.length a b) op keep
    (prune || (dagLocal mask goal bounds state || linked)) =
      (dagLocal mask goal bounds state || linked) := by
  dsimp only
  cases hit : sigPairPrune (sigDagCode mask (sigDagPos mask goal ws) (sigDagNeg mask goal ws)
      ws.length a b) op keep
  · rfl
  · by_cases big : mask = fullMask
    · simp only [sigDagCode, sigDagPos, sigDagNeg, ite_eq_left big] at hit
      have bad := sigPairPrune_part hit
      unfold dagLocal
      dsimp only at bad ⊢
      rw [bad]
      simp
    · simp [sigDagCode, big, sigPairPrune] at hit

private theorem sigNatSub_eq (a b : Nat) : Nat.sub a b = a - b := rfl


private def halfMask : Nat := 0x8000000000000000

private theorem halfMask_land {w : Nat} (hw : w < halfMask) : w &&& fullMask = w :=
  Nat.and_two_pow_sub_one_of_lt_two_pow (n := 64) (Nat.lt_trans hw (by decide))

private theorem canonFullHalf {w : Nat} (hw : w < halfMask) : canon fullMask w = w := by
  have hn : w ≠ fullMask := Nat.ne_of_lt (Nat.lt_trans hw (by decide))
  have top : (fullMask ^^^ w).testBit 63 = true := by
    rw [Nat.testBit_xor, show fullMask.testBit 63 = true by decide,
      Nat.testBit_lt_two_pow (i := 63) hw]
    decide
  have lt : Nat.blt w (fullMask ^^^ w) = true :=
    Nat.blt_eq.mpr (Nat.lt_of_lt_of_le hw (Nat.ge_two_pow_of_testBit top))
  by_cases hz : w = 0
  · subst w; exact canon_zero _
  · simp only [canon, halfMask_land hw, beq_false_ne hz, beq_false_ne hn, lt,
      Bool.false_or, bsel_true, bsel_false]

private theorem andFullXor {a b : Nat} (ha : a < halfMask) :
    a &&& (fullMask ^^^ b) = a ^^^ (a &&& b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hmask := congrArg (fun w : Nat => w.testBit i) (halfMask_land ha)
  cases h : a.testBit i <;> cases b.testBit i <;>
    simp_all [Nat.testBit_and, Nat.testBit_xor]

private def cachedBinOp (a b both op : Nat) : Nat :=
  Bool.rec
    (Bool.rec (Bool.rec (Nat.xor b both) (Nat.xor a both) (Nat.beq op 2))
      (Nat.lor a b) (Nat.beq op 1))
    both (Nat.beq op 0)

private theorem cachedBinOp_eq {a b : Nat} (ha : a < halfMask) (hb : b < halfMask) (op : Nat) :
    cachedBinOp a b (a &&& b) op = binOp fullMask op a b := by
  have both : a &&& b < halfMask := Nat.and_lt_two_pow (n := 63) a hb
  unfold cachedBinOp binOp bsel
  rw [andFullXor ha, Nat.and_comm (fullMask ^^^ a) b, andFullXor hb, Nat.and_comm b a]
  rw [canonFullHalf both, canonFullHalf (Nat.or_lt_two_pow (n := 63) ha hb),
    canonFullHalf (Nat.xor_lt_two_pow (n := 63) ha both),
    canonFullHalf (Nat.xor_lt_two_pow (n := 63) hb both)]
  rfl

private def cacheBinOps (mask a b : Nat) (k : (Nat → Nat) → Bool) : Bool :=
  Bool.rec (k (fun op => binOpF mask op a b))
    (forceW (Nat.land a b) (fun both => k (cachedBinOp a b both)))
    (Nat.beq mask fullMask && Nat.blt a halfMask && Nat.blt b halfMask)

private theorem cacheBinOps_eq (mask a b : Nat) (k : (Nat → Nat) → Bool) :
    cacheBinOps mask a b k = k (fun op => binOp mask op a b) := by
  unfold cacheBinOps
  cases hit : Nat.beq mask fullMask && Nat.blt a halfMask && Nat.blt b halfMask
  · exact congrArg k (funext fun op => binOpF_eq mask op a b)
  · simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hit
    rcases hit with ⟨⟨rfl, ha⟩, hb⟩
    rw [forceW_eq]
    exact congrArg k (funext (cachedBinOp_eq ha hb))

def dagCheckChildrenF (mask goal : Nat) (bounds : Nat → List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, hist) := state
  let n := lenN ws
  Bool.rec
    (Bool.rec
      (Bool.rec false
        (forceW (sigDagPos mask goal ws) (fun pos =>
          forceW (sigDagNeg mask goal ws) (fun neg =>
          treeBlockF 0 n (fun a =>
          forceW (getDN ws a) (fun x =>
          treeBlockF (Nat.add a 1) n (fun b =>
            forceW (getDN ws b) (fun y =>
            forceW (sigDagCode mask pos neg n a b) (fun code =>
            cacheBinOps mask x y (fun gate =>
            treeBlockF 0 4 (fun op =>
              forceW (gate op) (fun z =>
                Bool.rec
                  (Bool.rec
                    (treeBlockF 0 4 (fun keep =>
                      let keepA := Nat.beq (Nat.land keep 1) 1
                      let keepB := Nat.beq (Nat.land (Nat.shiftRight keep 1) 1) 1
                      let newLen := Nat.add (Nat.add (Nat.sub n 1) (Bool.rec 0 1 keepA)) (Bool.rec 0 1 keepB)
                      Bool.rec
                        (Bool.rec
                          (forceWs (insertSortedF z (dropValF (Bool.rec true false keepA) x (dropValF (Bool.rec true false keepB) y ws))) (fun ws' =>
                          let ch := (Nat.sub fuel 1, ws', (z, x, y) :: hist)
                          let tok := Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) op) 2) keep
                          sigDagLocalF mask goal (bounds tok) ch (ref tok ch)))
                          true (sigPairPrune code op keep))
                        true (Nat.blt fuel newLen)))
                    true (memN z ws))
                  true (Nat.beq z 0))))))))))))
        (Nat.blt n 17))
      true (Nat.beq fuel 0))
    false (memN goal ws)

theorem makeTokenF_eq (a b op keep : Nat) :
    Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) op) 2) keep =
    makeToken a b op keep := by
  unfold makeToken
  change ((((a <<< 4) + b) <<< 2) + op) <<< 2 + keep = _
  simp only [Nat.shiftLeft_eq]

theorem localOr (a b : Bool) : Bool.rec b true a = (a || b) := by
  cases a <;> rfl

set_option maxHeartbeats 1000000 in
theorem dagCheckChildrenF_eq {mask goal : Nat} {bounds : Nat → List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ tok, ∀ b ∈ bounds tok, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    dagCheckChildrenF mask goal bounds ref state = dagCheckChildren mask goal bounds ref state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold dagCheckChildrenF dagCheckChildren; dsimp only
  simp only [forceW_eq, cacheBinOps_eq, lenN_eq, memN_eq, treeBlockF_eq]
  cases ws.contains goal
  · cases Nat.beq fuel 0
    · cases Nat.blt ws.length 17
      · rfl
      · dsimp only
        simp only [Bool.not_false, Bool.true_and, Bool.false_or]
        apply congrArg (treeBlock 0 ws.length); funext a
        simp only [getDN_eq]
        apply congrArg (treeBlock (a + 1) ws.length); funext b
        apply congrArg (treeBlock 0 4); funext op
        cases Nat.beq (binOp mask op (ws.getD a 0) (ws.getD b 0)) 0
        · cases ws.contains (binOp mask op (ws.getD a 0) (ws.getD b 0))
          · dsimp only; simp only [Bool.false_or]
            apply congrArg (treeBlock 0 4); funext keep
            simp only [insertSortedF_eq, dropValF_eq, forceWs_eq, makeTokenF_eq,
              sigDagLocalF_eq (hgoals (makeToken a b op keep)), localOr]
            cases ha : Nat.beq (keep &&& 1) 1 <;> cases hb : Nat.beq ((keep >>> 1) &&& 1) 1
            all_goals dsimp only
            all_goals simp only [Bool.false_eq_true, ite_true, ite_false, Bool.not_true, Bool.not_false]
            all_goals cases Nat.blt fuel _
            all_goals try rfl
            all_goals simp only [Bool.false_or, sigNatSub_eq]
            all_goals
              let x := ws.getD a 0
              let y := ws.getD b 0
              let z := binOp mask op x y
              let ch := (fuel - 1, insertSorted z (dropVal (!(Nat.beq (keep &&& 1) 1)) x
                (dropVal (!(Nat.beq ((keep >>> 1) &&& 1) 1)) y ws)), (z, x, y) :: hist)
              have eq := sigDagPrune_or_eq mask goal a b op keep (fuel - 1) ws ((z, x, y) :: hist)
                (bounds (makeToken a b op keep)) (ref (makeToken a b op keep) ch)
              simpa only [ch, x, y, z, ha, hb, Bool.not_true, Bool.not_false] using eq
          · rfl
        · rfl
    · rfl
  · rfl

def dagCheckNodeF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildrenF mask goal (fun _ => bounds) (dagRefF count states links (Nat.add i 1)) st

def dagCheckRootsF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (stock : List Nat) (fuel : Nat) : Bool :=
  treeBlockF 0 (Nat.shiftLeft 1 (lenN stock)) (fun token =>
    forceWs (subsetWordsF stock token) (fun ws =>
      let st := (fuel, ws, [])
      Bool.rec (dagLocalF mask goal bounds st) true (ref token st)))

theorem dagCheckRootsF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (stock : List Nat) (fuel : Nat) :
    dagCheckRootsF mask goal bounds ref stock fuel = dagCheckRoots mask goal bounds ref stock fuel := by
  unfold dagCheckRootsF dagCheckRoots
  have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
    rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [hpow, treeBlockF_eq]
  congr 1; funext tok
  simp only [subsetWordsF_eq, forceWs_eq, dagLocalF_eq hgoals]
  cases ref tok (fuel, subsetWords stock tok, []) <;> cases dagLocal mask goal bounds (fuel, subsetWords stock tok, []) <;> rfl

def unpackF (data width idx : Nat) : Nat :=
  Nat.land (Nat.shiftRight data (Nat.mul idx width)) (Nat.sub (Nat.shiftLeft 1 width) 1)

def unpackForestF (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := Nat.add pBits tBits
  let code := unpackF data w i
  (Nat.shiftRight code tBits, Nat.land code (Nat.sub (Nat.shiftLeft 1 tBits) 1))

def unpackLinksF (index data idxW sizeBits tokBits destBits steps : Nat) : Nat → Nat → Option Nat :=
  fun parent tok =>
    let entry := unpackF index idxW parent
    let sz := Nat.land entry (Nat.sub (Nat.shiftLeft 1 sizeBits) 1)
    let off := Nat.shiftRight entry sizeBits
    let w := Nat.add tokBits destBits
    (Nat.rec (motive := fun _ => Nat → Nat → Option Nat) (fun _ _ => none)
      (fun _ next lo hi =>
        Bool.rec none
          (let mid := Nat.shiftRight (Nat.add lo hi) 1
           let code := unpackF data w mid
           let key := Nat.land code (Nat.sub (Nat.shiftLeft 1 tokBits) 1)
           Bool.rec
             (Bool.rec (next (Nat.add mid 1) hi) (next lo mid) (Nat.blt tok key))
             (some (Nat.shiftRight code tokBits)) (Nat.beq tok key))
          (Nat.blt lo hi)) steps) off (Nat.add off sz)

theorem treeBlockF_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlockF lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  rw [treeBlockF_eq] at h; exact treeBlock_at h

def hintWordAt (pages : List (Nat × Nat × Nat)) (i : Nat) : Nat :=
  let page := pages.getD (Nat.shiftRight i 5) (0, 1, 0)
  let j := Nat.land i 31
  let first := unpackF page.1 page.2.1 j
  let last := unpackF page.1 page.2.1 (Nat.add j 1)
  Nat.land (Nat.shiftRight page.2.2 first) (Nat.sub (Nat.shiftLeft 1 (Nat.sub last first)) 1)

def hintCut (word token : Nat) : Nat :=
  (Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 63)
    (fun _ next at' =>
      forceW (Nat.shiftRight word at') (fun info =>
        Bool.rec
          (let bit := Nat.land (Nat.shiftRight info 1) 15
           let leftLeaves := Nat.land (Nat.shiftRight info 5) 63
           next (Bool.rec (Nat.add at' 11) (Nat.add at' (Nat.mul leftLeaves 18)) (Nat.testBit token bit)))
          (Nat.land (Nat.shiftRight info 1) 63) (Nat.beq (Nat.land info 1) 0))) 13) 0

def hintedBounds (chunks : List (List (Nat × List Nat × Nat × Nat))) (word token : Nat) :
    List (Nat × List Nat × Nat × Nat) :=
  forceW (hintCut word token) fun i =>
    match chunks[Nat.shiftRight i 3]? with
    | none => []
    | some chunk =>
      match chunk[Nat.land i 7]? with
      | none => []
      | some b => [b]

theorem hintedBounds_mem {chunks : List (List (Nat × List Nat × Nat × Nat))}
    {word token : Nat} {b : Nat × List Nat × Nat × Nat}
    (hb : b ∈ hintedBounds chunks word token) : b ∈ chunks.flatten := by
  simp only [hintedBounds, forceW_eq] at hb
  split at hb
  · simp at hb
  · rename_i chunk hchunk
    split at hb
    · simp at hb
    · rename_i a ha
      have eq : b = a := List.mem_singleton.mp hb
      subst b
      exact List.mem_flatten.mpr ⟨chunk, List.mem_of_getElem? hchunk, List.mem_of_getElem? ha⟩

-- The general checker is from barelyanything's pull request 54457.

theorem blockSpec {f : Nat → Bool} {lo hi : Nat} (h : treeBlockF lo hi f = true) :
    ∀ i, lo ≤ i → i < hi → f i = true := fun _ hlo hhi => treeBlockF_at h hlo hhi

theorem joinBlockSpecs {f : Nat → Bool} {lo mid hi : Nat}
    (first : ∀ i, lo ≤ i → i < mid → f i = true)
    (last : ∀ i, mid ≤ i → i < hi → f i = true) :
    ∀ i, lo ≤ i → i < hi → f i = true := by
  intro i hlo hhi
  by_cases h : i < mid
  · exact first i hlo h
  · exact last i (by omega) hhi


section Relabel

variable {n r : Nat}


def rowPull (p : Fin r → Fin n) (w : Nat) : Nat :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin r => w.testBit (p i).val)).toNat

theorem rowPull_testBit (p : Fin r → Fin n) (w i : Nat) :
    (rowPull p w).testBit i = if h : i < r then w.testBit (p ⟨i, h⟩).val else false := by
  simp only [rowPull, BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : i < r <;> simp [h]

theorem rowPull_bit (p : Fin r → Fin n) (w : Nat) (i : Fin r) :
    (rowPull p w).testBit i.val = w.testBit (p i).val := by
  simp only [rowPull_testBit, i.isLt, dite_true]

theorem rowPull_zero (p : Fin r → Fin n) : rowPull p 0 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < r <;> simp [rowPull_testBit, h]

theorem rowPull_and (p : Fin r → Fin n) (a b : Nat) :
    rowPull p (a &&& b) = rowPull p a &&& rowPull p b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < r <;> simp [rowPull_testBit, h]

theorem rowPull_or (p : Fin r → Fin n) (a b : Nat) :
    rowPull p (a ||| b) = rowPull p a ||| rowPull p b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < r <;> simp [rowPull_testBit, h]

theorem rowPull_xor (p : Fin r → Fin n) (a b : Nat) :
    rowPull p (a ^^^ b) = rowPull p a ^^^ rowPull p b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < r <;> simp [rowPull_testBit, h]

def rowCanon (p : Fin r → Fin n) (mask w : Nat) : Nat :=
  canon (rowPull p mask) (rowPull p w)

theorem rowCanon_zero (p : Fin r → Fin n) (mask : Nat) : rowCanon p mask 0 = 0 := by
  rw [rowCanon, rowPull_zero, canon_zero]

theorem rowCanon_canon (p : Fin r → Fin n) (mask w : Nat) :
    rowCanon p mask (canon mask w) = rowCanon p mask w := by
  have cut : rowCanon p mask (w &&& mask) = rowCanon p mask w := by
    rw [rowCanon, rowPull_and, canon_land]
    rfl
  rcases canon_cases mask w with ⟨h0, hz | hm⟩ | ⟨_, h | h⟩
  · rw [h0, rowCanon_zero, ← cut, hz, rowCanon_zero]
  · rw [h0, rowCanon_zero, ← cut, hm, rowCanon, canon_self]
  · rw [h, cut]
  · rw [h, rowCanon, rowPull_xor, canon_xor_mask]
    exact cut

private theorem rowCanon_binOp (p : Fin r → Fin n) (mask op a b : Nat) (hop : op < 4) :
    rowCanon p mask (binOp mask op a b) = 0 ∨
    rowCanon p mask (binOp mask op a b) = rowCanon p mask a ∨
    rowCanon p mask (binOp mask op a b) = rowCanon p mask b ∨
    ∃ k < 4, rowCanon p mask (binOp mask op a b) =
      binOp (rowPull p mask) k (rowCanon p mask a) (rowCanon p mask b) := by
  rcases (show op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [show binOp mask 0 a b = canon mask (a &&& b) from rfl, rowCanon_canon]
    simp only [rowCanon, rowPull_and]
    exact canon_and_in_binOp _ _ _
  · rw [show binOp mask 1 a b = canon mask (a ||| b) from rfl, rowCanon_canon]
    simp only [rowCanon, rowPull_or]
    exact canon_or_in_binOp _ _ _
  · rw [show binOp mask 2 a b = canon mask (a &&& (mask ^^^ b)) from rfl, rowCanon_canon]
    simp only [rowCanon, rowPull_and, rowPull_xor]
    simpa only [canon_xor_mask] using
      canon_and_in_binOp (rowPull p mask) (rowPull p a) (rowPull p mask ^^^ rowPull p b)
  · rw [show binOp mask 3 a b = canon mask ((mask ^^^ a) &&& b) from rfl, rowCanon_canon]
    simp only [rowCanon, rowPull_and, rowPull_xor]
    simpa only [canon_xor_mask] using
      canon_and_in_binOp (rowPull p mask) (rowPull p mask ^^^ rowPull p a) (rowPull p b)

theorem avail_rowPull (p : Fin r → Fin n) {mask w : Nat} {bank bank' : List Nat}
    (stocked : ∀ u ∈ bank, Avail bank' (rowCanon p mask u)) (h : Avail bank w) :
    Avail bank' (rowCanon p mask w) := by
  rcases h with rfl | h
  · exact .inl (rowCanon_zero p mask)
  · exact stocked _ h

private theorem gateBin_copy {mask w : Nat} {bank : List Nat} (h : Avail bank w)
    (hc : canon mask w = w) : GateBin mask bank w := by
  refine ⟨w, w, 0, by omega, h, h, ?_⟩
  change w = canon mask (w &&& w)
  rw [Nat.and_self, hc]

theorem gateBin_rowPull (p : Fin r → Fin n) {mask w : Nat} {bank bank' : List Nat}
    (stocked : ∀ u ∈ bank, Avail bank' (rowCanon p mask u)) (h : GateBin mask bank w) :
    GateBin (rowPull p mask) bank' (rowCanon p mask w) := by
  obtain ⟨a, b, op, hop, ha, hb, rfl⟩ := h
  have ha' := avail_rowPull p stocked ha
  have hb' := avail_rowPull p stocked hb
  have hcanon := canon_idem (rowPull p mask) (rowPull p (binOp mask op a b))
  rcases rowCanon_binOp p mask op a b hop with h0 | h1 | h2 | ⟨k, hk, hv⟩
  · exact gateBin_copy (.inl h0) hcanon
  · exact gateBin_copy (h1.symm ▸ ha') hcanon
  · exact gateBin_copy (h2.symm ▸ hb') hcanon
  · exact ⟨_, _, k, hk, ha', hb', hv⟩

theorem buildsBin_rowPull (p : Fin r → Fin n) {mask : Nat} {bank bank' vs : List Nat}
    (stocked : ∀ u ∈ bank, Avail bank' (rowCanon p mask u)) (h : BuildsBin mask bank vs) :
    BuildsBin (rowPull p mask) bank' (vs.map (rowCanon p mask)) := by
  induction vs generalizing bank bank' with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gateBin_rowPull p stocked h.1, ih ?_ h.2⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact .inr List.mem_cons_self
    · rcases stocked w hw with h0 | hmem
      · exact .inl h0
      · exact .inr (List.mem_cons_of_mem _ hmem)

theorem lowerBin_of_rowPull (p : Fin r → Fin n) {mask goal k : Nat} {stock stock' : List Nat}
    (stocked : ∀ w ∈ stock, Avail stock' (rowCanon p mask w))
    (known : LowerBin (rowPull p mask) stock' (rowCanon p mask goal) k) :
    LowerBin mask stock goal k := by
  intro vs circuit hit
  have projected := buildsBin_rowPull p stocked circuit
  have output : Avail (vs.map (rowCanon p mask) ++ stock') (rowCanon p mask goal) := by
    apply avail_rowPull p _ hit
    intro w hw
    rcases List.mem_append.mp hw with hvs | hs
    · exact .inr (List.mem_append_left _ (List.mem_map_of_mem hvs))
    · rcases stocked w hs with h0 | hmem
      · exact .inl h0
      · exact .inr (List.mem_append_right _ hmem)
  simpa only [List.length_map] using known _ projected output

theorem rowPull_inverse (p : Equiv.Perm (Fin n)) (w : Nat) :
    rowPull p.symm (rowPull p w) = w % 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < n
  · let j : Fin n := ⟨i, h⟩
    simp only [Nat.testBit_mod_two_pow, h, decide_true, Bool.true_and]
    change (rowPull p.symm (rowPull p w)).testBit j.val = w.testBit j.val
    rw [rowPull_bit p.symm, rowPull_bit p, Equiv.apply_symm_apply]
  · simp [rowPull_testBit, Nat.testBit_mod_two_pow, h]

private theorem canon_before_width {mask : Nat} (h : mask < 2 ^ n) (w : Nat) :
    canon mask (w % 2 ^ n) = canon mask w := by
  rw [← canon_land mask (w % 2 ^ n), ← canon_land mask w]
  congr 1
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · simp [Nat.testBit_and, Nat.testBit_mod_two_pow, hi]
  · have hz : mask.testBit i = false := Nat.testBit_lt_two_pow
      (h.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_of_not_lt hi)))
    simp [Nat.testBit_and, hz]

theorem rowCanon_inverse (p : Equiv.Perm (Fin n)) {mask : Nat} (h : mask < 2 ^ n) (w : Nat) :
    rowCanon p.symm (rowPull p mask) (rowCanon p mask w) = canon mask w := by
  change rowCanon p.symm (rowPull p mask) (canon (rowPull p mask) (rowPull p w)) = canon mask w
  rw [rowCanon_canon, rowCanon, rowPull_inverse p mask, rowPull_inverse p w,
    Nat.mod_eq_of_lt h, canon_before_width h]

theorem rowCanon_injective_on_canon (p : Equiv.Perm (Fin n)) {mask a b : Nat}
    (hm : mask < 2 ^ n) (ha : canon mask a = a) (hb : canon mask b = b)
    (h : rowCanon p mask a = rowCanon p mask b) : a = b := by
  have e := congrArg (rowCanon p.symm (rowPull p mask)) h
  simpa only [rowCanon_inverse p hm, ha, hb] using e

end Relabel


def decodeRows (code : Nat) (i : Fin 64) : Fin 64 :=
  ⟨Nat.mod (Nat.shiftRight code (Nat.mul i.val 6)) 64, Nat.mod_lt _ (by decide)⟩

abbrev DagState := Nat × List Nat × List (Nat × Nat × Nat)

def RefSound (mask goal count : Nat) (states : Nat → Option DagState)
    (ref : Nat → Nat → DagState → Bool) : Prop :=
  ∀ parent tok st, ref parent tok st = true →
    ∃ dest saved, dest < count ∧ states dest = some saved ∧ saved.1 = st.1 ∧
      ∀ k, LiveBin mask goal k st.2.1.toFinset → LiveBin mask goal k saved.2.1.toFinset

def checkNodeVia (mask goal : Nat) (bounds : Nat → List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option DagState) (ref : Nat → Nat → DagState → Bool) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildren mask goal bounds (ref (i + 1)) st

theorem dagAllNodesRef {mask goal fuel count : Nat} {stock : List Nat}
    {boundsFor : Nat → Nat → List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {ref : Nat → Nat → DagState → Bool}
    (hgm : Masked mask goal) (hknown : ∀ i tok, KnownBin (boundsFor i tok))
    (hsub : ∀ i tok, ∀ b ∈ boundsFor i tok, mask &&& b.1 = b.1) (snd : stock.Nodup)
    (good : RefSound mask goal count (dagTrace mask stock fuel forest) ref)
    (hnodes : ∀ i, 0 ≤ i → i < count → checkNodeVia mask goal (boundsFor i)
      (dagTrace mask stock fuel forest) ref i = true) :
    ∀ cap i st, i < count → dagTrace mask stock fuel forest i = some st →
      st.1 = cap → ∀ k, k ≤ cap → ¬LiveBin mask goal k st.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i st hi htr hcap k hk hlive
    obtain ⟨rem, ws, hist⟩ := st
    dsimp only at hcap hlive
    have nd : ws.Nodup := dagTrace_nodup snd htr
    have hchk := hnodes i (Nat.zero_le i) hi
    unfold checkNodeVia at hchk
    rw [htr] at hchk
    unfold dagCheckChildren at hchk
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq] at hchk
    obtain ⟨hnohit, hstep⟩ := hchk
    generalize hS : ws.toFinset = S at hlive
    cases hlive with
    | done =>
      have hgm' : goal ∈ ws := List.mem_toFinset.mp (hS.symm ▸ Finset.mem_singleton_self goal)
      have hc : ws.contains goal = true := List.contains_iff_mem.mpr hgm'
      rw [hc] at hnohit; exact Bool.noConfusion hnohit
    | @step k' _ a0 b0 op0 ha0 hb0 hab0 _ _ hop0 hz0 hf0 keepA0 keepB0 tail0 =>
      rw [← hS] at ha0 hb0 hf0 tail0
      have hrem_pos : rem ≠ 0 := by omega
      rcases hstep with hrem0 | ⟨hn17, hblock⟩
      · exact hrem_pos hrem0
      · have haM : a0 ∈ ws := List.mem_toFinset.mp ha0
        have hbM : b0 ∈ ws := List.mem_toFinset.mp hb0
        obtain ⟨ia0, hia0, hea0⟩ := getElem_index_lt haM
        obtain ⟨ib0, hib0, heb0⟩ := getElem_index_lt hbM
        have hiab_ne : ia0 ≠ ib0 := fun heq => hab0 (hea0.symm.trans (heq ▸ heb0))
        have ⟨a, b, op, keepA, keepB, ha_lt, hab_lt, hb_lt, hop_lt, hax, hby, hzeq, htail⟩ :
            ∃ a b op keepA keepB, a < ws.length ∧ a < b ∧ b < ws.length ∧ op < 4 ∧
              ws.getD a 0 = (if ia0 < ib0 then a0 else b0) ∧
              ws.getD b 0 = (if ia0 < ib0 then b0 else a0) ∧
              binOp mask op (ws.getD a 0) (ws.getD b 0) = binOp mask op0 a0 b0 ∧
              LiveBin mask goal k' (insert (binOp mask op (ws.getD a 0) (ws.getD b 0))
                (dropIf (!keepA) (ws.getD a 0) (dropIf (!keepB) (ws.getD b 0) ws.toFinset))) := by
          by_cases hlt : ia0 < ib0
          · exact ⟨ia0, ib0, op0, keepA0, keepB0, hia0, hlt, hib0, hop0,
              by simp only [hlt, ite_true]; exact hea0,
              by simp only [hlt, ite_true]; exact heb0,
              by rw [hea0, heb0], by rw [hea0, heb0]; exact tail0⟩
          · obtain ⟨op1, hop1, hopEq⟩ := binOp_comm mask op0 a0 b0 hop0
            have hswap : dropIf (!keepB0) b0 (dropIf (!keepA0) a0 ws.toFinset) =
                dropIf (!keepA0) a0 (dropIf (!keepB0) b0 ws.toFinset) := by
              ext w; simp only [dropIf]; cases keepA0 <;> cases keepB0 <;> simp [Finset.mem_erase, and_left_comm]
            exact ⟨ib0, ia0, op1, keepB0, keepA0, hib0, by omega, hia0, hop1,
              by simp only [hlt, ite_false]; exact heb0,
              by simp only [hlt, ite_false]; exact hea0,
              by rw [hea0, heb0, hopEq],
              by rw [hea0, heb0, ← hopEq, hswap]; exact tail0⟩
        set x := ws.getD a 0
        set y := ws.getD b 0
        set z := binOp mask op x y
        set keep := (if keepA then 1 else 0) + (if keepB then 2 else 0)
        have hkeep_lt : keep < 4 := by cases keepA <;> cases keepB <;> simp [keep]
        have hkA : Nat.beq (keep &&& 1) 1 = keepA := by cases keepA <;> cases keepB <;> decide
        have hkB : Nat.beq ((keep >>> 1) &&& 1) 1 = keepB := by cases keepA <;> cases keepB <;> decide
        have hkA' : (keep &&& 1 = 1) ↔ keepA = true := by cases keepA <;> cases keepB <;> decide
        have hkB' : ((keep >>> 1) &&& 1 = 1) ↔ keepB = true := by cases keepA <;> cases keepB <;> decide
        have hA := treeBlock_at hblock (Nat.zero_le a) ha_lt
        have hB := treeBlock_at hA (by omega : a + 1 ≤ b) hb_lt
        have hO := treeBlock_at hB (Nat.zero_le op) hop_lt
        simp only [forceW_eq, Bool.or_eq_true, Nat.beq_eq] at hO
        have hznz : z ≠ 0 := hzeq.symm ▸ hz0
        have hznm : ws.contains z = false := by
          cases h : ws.contains z
          · rfl
          · exact absurd (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)) (hzeq.symm ▸ hf0)
        rcases hO with (hz' | hcm) | hK
        · exact hznz hz'
        · rw [hznm] at hcm; exact Bool.noConfusion hcm
        · have hKe := treeBlock_at hK (Nat.zero_le keep) hkeep_lt
          simp only [hkA, hkB, hkA', hkB', forceWs_eq, Bool.or_eq_true, Nat.blt_eq] at hKe
          set ws' := insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))
          have hxM : x ∈ ws := by simp only [x, hax]; split; exact haM; exact hbM
          have hyM : y ∈ ws := by simp only [y, hby]; split; exact hbM; exact haM
          have hxy : x ≠ y := by simp only [x, y, hax, hby]; split; exact hab0; exact hab0.symm
          have hzNotW : z ∉ ws := fun hm => by
            have := List.contains_iff_mem.mpr hm; rw [hznm] at this; exact Bool.noConfusion this
          have hnd' : ws'.Nodup :=
            insertSorted_nodup (fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
          have hset' : ws'.toFinset = insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
            ext w; simp only [ws', List.mem_toFinset, insertSorted_mem, Finset.mem_insert, ← dropVal_toFinset]
          have hlive' : LiveBin mask goal k' ws'.toFinset := by rwa [hset']
          have hlen' := list_len_child (z := z) (keepA := keepA) (keepB := keepB) nd hxM hyM hxy hzNotW
          have hcard' : ws'.length ≤ rem := by
            have := liveBin_card_le hlive'
            rw [List.toFinset_card_of_nodup hnd'] at this; omega
          rcases hKe with hwide | hloc | href
          · change ws'.length = _ at hlen'; rw [← hlen'] at hwide; omega
          · have hopen := dagLocal_open (state := (rem - 1, ws', (z, x, y) :: hist)) hgm (hknown i (makeToken a b op keep)) (hsub i (makeToken a b op keep)) hnd' (k := k') (by omega) hlive'
            rw [hopen] at hloc; exact Bool.noConfusion hloc
          · obtain ⟨dest, saved, hdest, htr', heq, moved⟩ :=
              good (i + 1) (makeToken a b op keep) _ href
            exact ih (rem - 1) (by omega) dest saved hdest htr' heq k' (by omega) (moved k' hlive')

theorem lowerDagRef {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {boundsFor : Nat → Nat → List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {ref : Nat → Nat → DagState → Bool}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hroots : dagCheckRoots mask goal bounds
      (ref 0) stock fuel = true)
    (hknownFor : ∀ i tok, KnownBin (boundsFor i tok))
    (hsubFor : ∀ i tok, ∀ b ∈ boundsFor i tok, mask &&& b.1 = b.1)
    (good : RefSound mask goal count (dagTrace mask stock fuel forest) ref)
    (hnodes : ∀ i, 0 ≤ i → i < count → checkNodeVia mask goal (boundsFor i)
      (dagTrace mask stock fuel forest) ref i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  intro vs hbuild hhit
  by_contra! hlt
  have hcs' : ∀ w ∈ stock, canon mask w = w := fun w hw =>
    Nat.beq_eq.mp (List.all_eq_true.mp hcs w hw)
  obtain ⟨k, S, hk, hSsub, hlive⟩ := extractLiveBin hgnz hcs' hbuild hhit
  obtain ⟨tok, htok, hteq⟩ := exists_subsetToken stock S
  rw [Finset.inter_eq_left.mpr hSsub] at hteq
  have hchk := treeBlock_at hroots (Nat.zero_le tok) htok
  simp only [forceWs_eq, Bool.or_eq_true] at hchk
  have hnd : (subsetWords stock tok).Nodup := subsetWords_nodup snd tok
  have hlive' : LiveBin mask goal k (subsetWords stock tok).toFinset := by rwa [hteq]
  rcases hchk with hloc | href
  · have hopen := dagLocal_open (state := (fuel, subsetWords stock tok, [])) hgm hknown hsub hnd (k := k) (by omega) hlive'
    rw [hopen] at hloc; exact Bool.noConfusion hloc
  · obtain ⟨dest, saved, hdest, htr, heq, moved⟩ := good 0 tok _ href
    exact dagAllNodesRef hgm hknownFor hsubFor snd good hnodes fuel dest saved hdest htr heq k
      (by omega) (moved k hlive')

def chooseBounds : List (Nat × List Nat × Nat × Nat) → Nat → List (Nat × List Nat × Nat × Nat)
  | [], _ => []
  | b :: bs, bits =>
    let rest := chooseBounds bs (Nat.shiftRight bits 1)
    Bool.rec rest (b :: rest) (Nat.testBit bits 0)

theorem chooseBounds_mem {bs : List (Nat × List Nat × Nat × Nat)} (bits : Nat)
    {b : Nat × List Nat × Nat × Nat} (h : b ∈ chooseBounds bs bits) : b ∈ bs := by
  induction bs generalizing bits with
  | nil => simp [chooseBounds] at h
  | cons a tail ih =>
    cases e : Nat.testBit bits 0
    · simp only [chooseBounds, e] at h
      exact List.mem_cons_of_mem _ (ih _ h)
    · simp only [chooseBounds, e] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ h)

def checkNodeViaF (mask goal : Nat) (bounds : Nat → List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option DagState) (ref : Nat → Nat → DagState → Bool) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildrenF mask goal bounds (ref (Nat.add i 1)) st

theorem checkNodeViaF_eq {mask goal : Nat} {bounds : Nat → List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ tok, ∀ b ∈ bounds tok, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (states : Nat → Option DagState) (ref : Nat → Nat → DagState → Bool) (i : Nat) :
    checkNodeViaF mask goal bounds states ref i = checkNodeVia mask goal bounds states ref i := by
  unfold checkNodeViaF checkNodeVia
  cases states i with
  | none => rfl
  | some st => exact dagCheckChildrenF_eq hgoals _ st

theorem lowerDagRefF {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)} {boundsFor : Nat → Nat → List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {ref : Nat → Nat → DagState → Bool}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true) (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hmem : ∀ i tok b, b ∈ boundsFor i tok → b ∈ bounds)
    (good : RefSound mask goal count (dagTraceF mask stock fuel forest) ref)
    (hroots : dagCheckRootsF mask goal bounds (ref 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → checkNodeViaF mask goal (boundsFor i)
      (dagTraceF mask stock fuel forest) ref i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr] at good hnodes
  rw [dagCheckRootsF_eq hgoals] at hroots
  refine lowerDagRef hgm hgnz hcs snd hknown hsub hroots
    (boundsFor := boundsFor) (fun i tok b hb => hknown b (hmem i tok b hb))
    (fun i tok b hb => hsub b (hmem i tok b hb)) good ?_
  intro i hlo hhi
  have h := hnodes i hlo hhi
  rwa [checkNodeViaF_eq (fun tok b hb => hgoals b (hmem i tok b hb))] at h



theorem dagRefF_sound (mask goal count : Nat) (states : Nat → Option DagState)
    (links : Nat → Nat → Option Nat) : RefSound mask goal count states
      (dagRefF count states links) := by
  intro parent tok st h
  unfold dagRefF at h
  split at h
  · contradiction
  · rename_i dest hlink
    cases hd : Nat.blt dest count
    · rw [hd] at h
      contradiction
    · rw [hd] at h
      dsimp only at h
      split at h
      · contradiction
      · rename_i saved hstate
        cases hf : Nat.beq saved.1 st.1
        · rw [hf] at h
          contradiction
        · rw [hf] at h
          have eq : saved.2.1 = st.2.1 := by
            change eqListN saved.2.1 st.2.1 = true at h
            rw [eqListN_eq] at h
            exact beq_iff_eq.mp h
          refine ⟨dest, saved, Nat.blt_eq.mp hd, hstate, Nat.beq_eq.mp hf, ?_⟩
          intro k hl
          simpa only [eq] using hl

theorem lowerDagF {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hroots : dagCheckRootsF mask goal bounds
      (dagRefF count (dagTraceF mask stock fuel forest) links 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeF mask goal bounds count
      (dagTraceF mask stock fuel forest) links i = true) :
    LowerBin mask stock goal (fuel + 1) :=
  lowerDagRefF (boundsFor := fun _ _ => bounds) hgm hgnz hcs snd hknown hsub hgoals
    (fun _ _ _ h => h) (dagRefF_sound mask goal count _ links) hroots hnodes

theorem image_dropIf (f : Nat → Nat) (drop : Bool) (x : Nat) (S : Finset Nat)
    (hinj : ∀ w ∈ S, f w = f x → w = x) :
    (dropIf drop x S).image f = dropIf drop (f x) (S.image f) := by
  cases drop with
  | false => rfl
  | true =>
    change (S.erase x).image f = (S.image f).erase (f x)
    ext y
    constructor
    · intro hy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      exact Finset.mem_erase.mpr ⟨fun eq => hne (hinj w hmem eq), Finset.mem_image_of_mem _ hmem⟩
    · intro hy
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hmem
      exact Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨fun eq => hne (congrArg f eq), hw⟩)

theorem liveBin_rowPerm {n : Nat} (p : Equiv.Perm (Fin n)) {mask goal k : Nat} {S : Finset Nat}
    (hm : mask < 2 ^ n) (h : LiveBin mask goal k S) (canonical : ∀ w ∈ S, canon mask w = w) :
    LiveBin (rowPull p mask) (rowCanon p mask goal) k (S.image (rowCanon p mask)) := by
  induction h with
  | done =>
    simpa only [Finset.image_singleton] using
      (LiveBin.done (mask := rowPull p mask) (goal := rowCanon p mask goal))
  | @step k S a b op ha hb hab ha0 hb0 hop hz fresh keepA keepB _ ih =>
    let f := rowCanon p mask
    let z := binOp mask op a b
    let after := dropIf (!keepA) a (dropIf (!keepB) b S)
    have cz : canon mask z = z := binOp_canon mask op a b
    have ca := canonical a ha
    have cb := canonical b hb
    have ha' : f a ∈ S.image f := Finset.mem_image_of_mem _ ha
    have hb' : f b ∈ S.image f := Finset.mem_image_of_mem _ hb
    have distinct : f a ≠ f b := fun he => hab (rowCanon_injective_on_canon p hm ca cb he)
    have nonzero {w : Nat} (hw : canon mask w = w) (hn : w ≠ 0) : f w ≠ 0 := by
      intro he
      exact hn (rowCanon_injective_on_canon p hm hw (canon_zero mask)
        (he.trans (rowCanon_zero p mask).symm))
    have new : f z ∉ S.image f := by
      intro hit
      obtain ⟨w, hw, eq⟩ := Finset.mem_image.mp hit
      have he := rowCanon_injective_on_canon p hm (canonical w hw) cz eq
      apply fresh
      change z ∈ S
      rwa [← he]
    have moved : ∃ op' < 4, f z = binOp (rowPull p mask) op' (f a) (f b) := by
      rcases rowCanon_binOp p mask op a b hop with eq | eq | eq | ok
      · exact (nonzero cz hz eq).elim
      · exfalso
        apply new
        change f z = f a at eq
        rwa [eq]
      · exfalso
        apply new
        change f z = f b at eq
        rwa [eq]
      · exact ok
    obtain ⟨op', hop', produced⟩ := moved
    have nextCanonical : ∀ w ∈ insert z after, canon mask w = w := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact cz
      · exact canonical w (dropIf_subset (!keepB) b S
          (dropIf_subset (!keepA) a (dropIf (!keepB) b S) hw))
    have firstDrop : (dropIf (!keepB) b S).image f = dropIf (!keepB) (f b) (S.image f) :=
      image_dropIf f (!keepB) b S (fun w hw => rowCanon_injective_on_canon p hm (canonical w hw) cb)
    have movedAfter : after.image f = dropIf (!keepA) (f a) (dropIf (!keepB) (f b) (S.image f)) := by
      unfold after
      rw [image_dropIf f (!keepA) a (dropIf (!keepB) b S), firstDrop]
      intro w hw
      exact rowCanon_injective_on_canon p hm (canonical w (dropIf_subset (!keepB) b S hw)) ca
    have rest := ih nextCanonical
    change LiveBin (rowPull p mask) (rowCanon p mask goal) k ((insert z after).image f) at rest
    rw [Finset.image_insert, movedAfter, produced] at rest
    exact LiveBin.step ha' hb' distinct (nonzero ca ha0) (nonzero cb hb0) hop'
      (by rw [← produced]; exact nonzero cz hz) (by rwa [← produced]) keepA keepB rest

theorem liveBin_rowSymmetry {n : Nat} (p : Equiv.Perm (Fin n)) {mask goal k : Nat} {S : Finset Nat}
    (hm : mask < 2 ^ n) (hmask : rowPull p mask = mask) (hgoal : rowCanon p mask goal = goal)
    (h : LiveBin mask goal k S) (canonical : ∀ w ∈ S, canon mask w = w) :
    LiveBin mask goal k (S.image (rowCanon p mask)) := by
  simpa only [hmask, hgoal] using liveBin_rowPerm p hm h canonical

structure RowAction64 where
  source : Fin 64 → Fin 64
  apply : Nat → Nat
  testBit_eq : ∀ w (i : Fin 64), (apply w).testBit i.val = w.testBit (source i).val

def RowAction64.id : RowAction64 := ⟨fun i => i, fun w => w, fun _ _ => rfl⟩

def RowAction64.comp (a b : RowAction64) : RowAction64 :=
  ⟨fun i => b.source (a.source i), fun w => a.apply (b.apply w), by
    intro w i
    rw [a.testBit_eq, b.testBit_eq]⟩

private def lowerLane (lo d : Nat) (i : Fin 64) : Bool :=
  decide (d ≤ i.val) && lo.testBit (i.val - d)

private def maskSource (lo hi d : Nat) (i : Fin 64) : Fin 64 :=
  ⟨(if lowerLane lo d i then i.val - d
    else if hi.testBit (d + i.val) then d + i.val else i.val) % 64, Nat.mod_lt _ (by decide)⟩

def goodMaskLanes (lo hi keep d : Nat) (i : Fin 64) : Prop :=
  let a := lowerLane lo d i
  let b := hi.testBit (d + i.val)
  let c := keep.testBit i.val
  (a = true ∧ b = false ∧ c = false) ∨
    (a = false ∧ b = true ∧ c = false ∧ d + i.val < 64) ∨
    (a = false ∧ b = false ∧ c = true)

def maskedRow64 (lo hi keep d : Nat) (cert : ∀ i : Fin 64, goodMaskLanes lo hi keep d i) : RowAction64 :=
  ⟨maskSource lo hi d, fun w => ((lo &&& w) <<< d) ||| ((hi &&& w) >>> d) ||| (keep &&& w), by
    intro w i
    have bits : (((lo &&& w) <<< d) ||| ((hi &&& w) >>> d) ||| (keep &&& w)).testBit i.val =
        ((lowerLane lo d i && w.testBit (i.val-d)) ||
          (hi.testBit (d+i.val) && w.testBit (d+i.val)) ||
          (keep.testBit i.val && w.testBit i.val)) := by
      simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
        lowerLane, Bool.and_assoc]
    rw [bits]
    have h := cert i
    unfold goodMaskLanes at h
    rcases h with ⟨a,b,c⟩ | ⟨a,b,c,h⟩ | ⟨a,b,c⟩
    · have h : i.val-d < 64 := (Nat.sub_le ..).trans_lt i.isLt
      simp [maskSource, a, b, c, Nat.mod_eq_of_lt h]
    · simp [maskSource, a, b, c, Nat.mod_eq_of_lt h]
    · simp [maskSource, a, b, c, Nat.mod_eq_of_lt i.isLt]⟩

theorem fullMask_testBit (i : Nat) : fullMask.testBit i = decide (i < 64) := by
  change (2 ^ 64 - 1).testBit i = _
  exact Nat.testBit_two_pow_sub_one _ _

theorem rowPull_fullMask (p : Fin 64 → Fin 64) : rowPull p fullMask = fullMask := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · simp [rowPull_testBit, hi, fullMask_testBit, (p ⟨i, hi⟩).isLt]
  · simp [rowPull_testBit, hi, fullMask_testBit]

theorem RowAction64.pull_eq (a : RowAction64) {p : Fin 64 → Fin 64} (h : ∀ i, a.source i = p i)
    (w : Nat) : a.apply w &&& fullMask = rowPull p w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, fullMask_testBit]
  by_cases hi : i < 64
  · let j : Fin 64 := ⟨i, hi⟩
    simp only [hi, decide_true, Bool.and_true]
    change (a.apply w).testBit j.val = (rowPull p w).testBit j.val
    rw [a.testBit_eq, rowPull_bit, h]
  · simp [hi, rowPull_testBit]

theorem RowAction64.canon_eq (a : RowAction64) {p : Fin 64 → Fin 64} (h : ∀ i, a.source i = p i)
    (w : Nat) : canonF fullMask (a.apply w) = rowCanon p fullMask w := by
  rw [canonF_eq, ← canon_land fullMask (a.apply w), a.pull_eq h, rowCanon, rowPull_fullMask]


def unpackPaged (pages : List Nat) (width pageBits i : Nat) : Nat :=
  unpackF (getDN pages (Nat.shiftRight i pageBits)) width
    (Nat.land i (Nat.sub (Nat.shiftLeft 1 pageBits) 1))

def unpackPagedWidths (pages : List (Nat × Nat)) (pageBits i : Nat) : Nat :=
  let page := pages.getD (Nat.shiftRight i pageBits) (0, 0)
  unpackF page.2 page.1 (Nat.land i (Nat.sub (Nat.shiftLeft 1 pageBits) 1))

def unpackForestRelative (row : Nat → Nat) (tBits : Nat) : Nat → Nat × Nat := fun i =>
  let code := row i
  let distance := Nat.shiftRight code tBits
  (Bool.rec (Nat.sub (Nat.add i 1) distance) 0 (Nat.beq distance 0),
    Nat.land code (Nat.sub (Nat.shiftLeft 1 tBits) 1))

def unpackLinksPaged (index entry : Nat → Nat) (sizeBits tokBits steps : Nat) : Nat → Nat → Option Nat :=
  fun parent tok =>
    let start := index parent
    let sz := Nat.land start (Nat.sub (Nat.shiftLeft 1 sizeBits) 1)
    let off := Nat.shiftRight start sizeBits
    (Nat.rec (motive := fun _ => Nat → Nat → Option Nat) (fun _ _ => none)
      (fun _ next lo hi =>
        Bool.rec none
          (let mid := Nat.shiftRight (Nat.add lo hi) 1
           let code := entry mid
           let key := Nat.land code (Nat.sub (Nat.shiftLeft 1 tokBits) 1)
           Bool.rec
             (Bool.rec (next (Nat.add mid 1) hi) (next lo mid) (Nat.blt tok key))
             (some (Nat.shiftRight code tokBits)) (Nat.beq tok key))
          (Nat.blt lo hi)) steps) off (Nat.add off sz)

abbrev TableSymmetry (mask goal : Nat) :=
  {s : ({p : Equiv.Perm (Fin 64) // rowPull p mask = mask ∧
      rowCanon p mask goal = goal}) × (Nat → Nat) //
    ∀ w, s.2 w = rowCanon s.1.val mask w}

def rowSort (f : Nat → Nat) : List Nat → List Nat
  | [] => []
  | w :: ws => insertSortedF (f w) (rowSort f ws)

theorem rowSort_mem (f : Nat → Nat) (ws : List Nat) (w : Nat) :
    w ∈ rowSort f ws ↔ w ∈ ws.map f := by
  induction ws with
  | nil => rfl
  | cons a as ih => simp only [rowSort, List.map_cons, insertSortedF_eq, insertSorted_mem, List.mem_cons, ih]

theorem rowSort_finset (f : Nat → Nat) (ws : List Nat) :
    (rowSort f ws).toFinset = ws.toFinset.image f := by
  ext w
  simp only [List.mem_toFinset, rowSort_mem, List.mem_map, Finset.mem_image]

def refMatches (mask goal : Nat) (syms : List (TableSymmetry mask goal))
    (sym : Nat) (saved st : DagState) : Bool :=
  if Nat.beq sym 0 then eqListN st.2.1 saved.2.1
  else match syms[sym]? with
  | none => false
  | some p => st.2.1.all (fun w => Nat.beq (canonF mask w) w) &&
      eqListN (rowSort p.val.2 st.2.1) saved.2.1

theorem refMatches_sound {mask goal : Nat} (hm : mask < 2 ^ 64)
    (syms : List (TableSymmetry mask goal)) (sym : Nat) (saved st : DagState)
    (hc : refMatches mask goal syms sym saved st = true) (k : Nat)
    (live : LiveBin mask goal k st.2.1.toFinset) : LiveBin mask goal k saved.2.1.toFinset := by
  unfold refMatches at hc
  split at hc
  · simp only [eqListN_eq, beq_iff_eq] at hc
    exact hc ▸ live
  · split at hc
    · contradiction
    · rename_i p hp
      simp only [Bool.and_eq_true, eqListN_eq, beq_iff_eq] at hc
      have hcanonical : ∀ w ∈ st.2.1.toFinset, canon mask w = w := by
        intro w hw
        have h := Nat.beq_eq.mp (List.all_eq_true.mp hc.1 w (List.mem_toFinset.mp hw))
        rwa [canonF_eq] at h
      have moved := liveBin_rowSymmetry p.val.1.val hm p.val.1.property.1 p.val.1.property.2 live hcanonical
      have haction : p.val.2 = rowCanon p.val.1.val mask := funext p.property
      rw [← haction, ← rowSort_finset, hc.2] at moved
      exact moved

def symDagRef (mask goal count bits : Nat) (syms : List (TableSymmetry mask goal))
    (states : Nat → Option DagState) (links : Nat → Nat → Option Nat)
    (parent tok : Nat) (st : DagState) : Bool :=
  match links parent tok with
  | none => false
  | some code =>
    let dest := Nat.shiftRight code bits
    let sym := Nat.land code (Nat.sub (Nat.shiftLeft 1 bits) 1)
    Nat.blt dest count &&
      (match states dest with
      | none => false
      | some saved => Nat.beq saved.1 st.1 && refMatches mask goal syms sym saved st)

theorem symDagRef_sound {mask goal count bits : Nat} (hm : mask < 2 ^ 64)
    (syms : List (TableSymmetry mask goal)) (states : Nat → Option DagState)
    (links : Nat → Nat → Option Nat) : RefSound mask goal count states
      (symDagRef mask goal count bits syms states links) := by
  intro parent tok st h
  unfold symDagRef at h
  split at h
  · contradiction
  · rename_i code heq
    simp only [Bool.and_eq_true] at h
    obtain ⟨hd, hmoves⟩ := h
    split at hmoves
    · contradiction
    · rename_i saved hstate
      simp only [Bool.and_eq_true] at hmoves
      obtain ⟨hf, hmatch⟩ := hmoves
      exact ⟨_, saved, Nat.blt_eq.mp hd, hstate, Nat.beq_eq.mp hf,
        refMatches_sound hm syms _ saved st hmatch⟩

private theorem relabelLower {mask goal cut target lower : Nat} {stock seeds : List Nat}
    (rows : Fin 64 → Fin 64) (known : LowerBin cut seeds target lower)
    (wires : stock.all (fun w => availBF seeds (rowCanon rows mask w)) = true)
    (hm : rowPull rows mask = cut) (hg : rowCanon rows mask goal = target) :
    LowerBin mask stock goal lower := by
  apply lowerBin_of_rowPull rows (stock' := seeds)
  · intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp wires w hw
  · rw [hm, hg]
    exact known

def cert_mask : Nat := 0xffffffffffffffff
def cert_stock : List Nat := [0xffffffff, 0xffff0000ffff, 0xff00ff00ff00ff, 0xf0f0f0f0f0f0f0f, 0x3333333333333333, 0x5555555555555555]
def cert_goal : Nat := 0x11717570157577f
def cert_bound_chunks : List (List (Nat × List Nat × Nat × Nat)) := [
  [(0xf0f0f0f0f0f0f0f0, [0xf0f0f0f0, 0xf0f00000f0f0, 0xf000f000f000f0, 0x3030303030303030, 0x5050505050505050], 9, 0x10105000505070), (0xcccccccccccccccc, [0xcccccccc, 0xcccc0000cccc, 0xcc00cc00cc00cc, 0xc0c0c0c0c0c0c0c, 0x4444444444444444], 9, 0x404440044444c), (0xff00ff00ff00ff, [0xff00ff, 0xff000000ff, 0xf000f000f000f, 0x33003300330033, 0x55005500550055], 9, 0x1700570057007f), (0xffff0000ffff, [0xffff, 0xff000000ff, 0xf0f00000f0f, 0x333300003333, 0x555500005555], 9, 0x17570000577f), (0x5555555555555555, [0x55555555, 0x555500005555, 0x55005500550055, 0x505050505050505, 0x1111111111111111], 8, 0x115155501555555), (0xaaaaaaaaaaaaaaaa, [0xaaaaaaaa, 0xaaaa0000aaaa, 0xaa00aa00aa00aa, 0xa0a0a0a0a0a0a0a, 0x2222222222222222], 8, 0x202020002022a), (0xf0f0f0f0f0f0f0f, [0xf0f0f0f, 0xf0f00000f0f, 0xf000f000f000f, 0x303030303030303, 0x505050505050505], 8, 0x10707070107070f), (0xffff00000000ffff, [0xffff, 0xff0000000000ff, 0xf0f000000000f0f, 0x3333000000003333, 0x5555000000005555], 10, 0x11700000000577f)],
  [(0xff00ff00ff00ff00, [0xff00ff00, 0xff000000ff00, 0xf000f000f000f00, 0x3300330033003300, 0x5500550055005500], 8, 0x100170001005700), (0x3333333333333333, [0x33333333, 0x333300003333, 0x33003300330033, 0x303030303030303, 0x1111111111111111], 8, 0x113131301131333), (0xffff0000ffff0000, [0xffff0000, 0xff000000ff0000, 0xf0f00000f0f0000, 0x3333000033330000, 0x5555000055550000], 8, 0x117000001570000), (0xffffffff00000000, [0xffff00000000, 0xff00ff00000000, 0xf0f0f0f00000000, 0x3333333300000000, 0x5555555500000000], 9, 0x117175700000000), (0xffffffff, [0xffff, 0xff00ff, 0xf0f0f0f, 0x33333333, 0x55555555], 9, 0x157577f), (0x55555555aaaaaaaa, [0xaaaaaaaa, 0x55550000aaaa, 0x55005500aa00aa, 0x50505050a0a0a0a, 0x1111111122222222], 10, 0x11515550002022a), (0x5555555500000000, [0x555500000000, 0x55005500000000, 0x505050500000000, 0x1111111100000000], 7, 0x115155500000000), (0x5500550055005500, [0x55005500, 0x550000005500, 0x500050005000500, 0x1100110011001100], 5, 0x100150001005500)],
  [(0xff000000ff, [0xff, 0xf0000000f, 0x3300000033, 0x5500000055], 5, 0x570000007f), (0xf0f0f0f00f0f0f0f, [0xf0f0f0f, 0xf0f000000f0f, 0xf000f0000f000f, 0x3030303003030303, 0x5050505005050505], 10, 0x1010500107070f), (0xaaaaaaaa, [0xaaaa, 0xaa00aa, 0xa0a0a0a, 0x22222222], 7, 0x2022a), (0x5050505050505050, [0x50505050, 0x505000005050, 0x50005000500050, 0x1010101010101010], 5, 0x10105000505050), (0xf0f00000f0f0, [0xf0f0, 0xf0000000f0, 0x303000003030, 0x505000005050], 6, 0x105000005070), (0x33333333, [0x3333, 0x330033, 0x3030303, 0x11111111], 7, 0x1131333), (0xa0a0a0a0a0a0a0a, [0xa0a0a0a, 0xa0a00000a0a, 0xa000a000a000a, 0x202020202020202], 5, 0x202020002020a), (0xff00ff0000000000, [0xff0000000000, 0xf000f0000000000, 0x3300330000000000, 0x5500550000000000], 7, 0x100170000000000)],
  [(0xf0f0f0f, [0xf0f, 0xf000f, 0x3030303, 0x5050505], 7, 0x107070f), (0xffff000000000000, [0xff000000000000, 0xf0f000000000000, 0x3333000000000000, 0x5555000000000000], 7, 0x117000000000000), (0x4444444444444444, [0x44444444, 0x444400004444, 0x44004400440044, 0x404040404040404], 5, 0x4044400444444), (0xcc00cc00cc00cc, [0xcc00cc, 0xcc000000cc, 0xc000c000c000c, 0x44004400440044], 6, 0x400440044004c), (0x5555000055550000, [0x55550000, 0x55000000550000, 0x505000005050000, 0x1111000011110000], 5, 0x115000001550000), (0x2222222222222222, [0x22222222, 0x222200002222, 0x22002200220022, 0x202020202020202], 5, 0x2020200020222), (0xaa00aa00aa00aa, [0xaa00aa, 0xaa000000aa, 0xa000a000a000a, 0x22002200220022], 5, 0x200020002002a), (0xc0c0c0c0c0c0c0c, [0xc0c0c0c, 0xc0c00000c0c, 0xc000c000c000c, 0x404040404040404], 5, 0x404040004040c)],
  [(0xaaaa0000aaaa, [0xaaaa, 0xaa000000aa, 0xa0a00000a0a, 0x222200002222], 5, 0x2020000022a), (0xff00ff0000ff00ff, [0xff00ff, 0xff00000000ff, 0xf000f00000f000f, 0x3300330000330033, 0x5500550000550055], 10, 0x10017000057007f), (0xcccccccc33333333, [0x33333333, 0xcccc00003333, 0xcc00cc00330033, 0xc0c0c0c03030303, 0x4444444411111111], 10, 0x4044401131333), (0xc0c0c0c0c0c0c0c0, [0xc0c0c0c0, 0xc0c00000c0c0, 0xc000c000c000c0, 0x4040404040404040], 5, 0x4000404040), (0xcccc0000cccc, [0xcccc, 0xcc000000cc, 0xc0c00000c0c, 0x444400004444], 6, 0x4440000444c), (0x3300330033003300, [0x33003300, 0x330000003300, 0x300030003000300, 0x1100110011001100], 4, 0x100130001001300), (0xf000f000f000f0, [0xf000f0, 0xf0000000f0, 0x30003000300030, 0x50005000500050], 6, 0x10005000500070), (0xff000000ff0000, [0xff0000, 0xf0000000f0000, 0x33000000330000, 0x55000000550000], 5, 0x17000000570000)],
  [(0xf0f0f0f000000000, [0xf0f000000000, 0xf000f000000000, 0x3030303000000000, 0x5050505000000000], 5, 0x10105000000000), (0xffff, [0xff, 0xf0f, 0x3333, 0x5555], 5, 0x577f), (0xffff00000000, [0xff00000000, 0xf0f00000000, 0x333300000000, 0x555500000000], 5, 0x175700000000), (0x3030303030303030, [0x30303030, 0x303000003030, 0x30003000300030, 0x1010101010101010], 5, 0x10101000101030), (0x3333333300000000, [0x333300000000, 0x33003300000000, 0x303030300000000, 0x1111111100000000], 5, 0x113131300000000), (0xf000f000f000f00, [0xf000f00, 0xf0000000f00, 0x300030003000300, 0x500050005000500], 4, 0x100070001000700), (0xcccccccc00000000, [0xcccc00000000, 0xcc00cc00000000, 0xc0c0c0c00000000, 0x4444444400000000], 5, 0x4044400000000), (0xf0f0f0f00000000, [0xf0f00000000, 0xf000f00000000, 0x303030300000000, 0x505050500000000], 5, 0x107070700000000)],
  [(0xff000000ff00, [0xff00, 0xf0000000f00, 0x330000003300, 0x550000005500], 5, 0x170000005700), (0xff00ff, [0xff, 0xf000f, 0x330033, 0x550055], 5, 0x57007f), (0xcccccccc, [0xcccc, 0xcc00cc, 0xc0c0c0c, 0x44444444], 5, 0x44444c), (0xf0f0f0f0, [0xf0f0, 0xf000f0, 0x30303030, 0x50505050], 5, 0x505070), (0xffff0000, [0xff0000, 0xf0f0000, 0x33330000, 0x55550000], 5, 0x1570000), (0x3333000033330000, [0x33330000, 0x33000000330000, 0x303000003030000, 0x1111000011110000], 4, 0x113000001130000), (0xf0f00000f0f0000, [0xf0f0000, 0xf0000000f0000, 0x303000003030000, 0x505000005050000], 4, 0x107000001070000), (0xff00ff00000000, [0xff00000000, 0xf000f00000000, 0x33003300000000, 0x55005500000000], 5, 0x17005700000000)],
  [(0xff00ff00, [0xff00, 0xf000f00, 0x33003300, 0x55005500], 5, 0x1005700)]]
def cert_bounds := cert_bound_chunks.flatten
theorem cert_sub : ∀ b ∈ cert_bounds, cert_mask &&& b.1 = b.1 := by
  have hall : cert_bounds.all (fun b => Nat.beq (Nat.land cert_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem cert_goals : ∀ b ∈ cert_bounds, canon b.1 cert_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : cert_bounds.all (fun b => Nat.beq (canonF b.1 cert_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def cert_forest : Nat → Nat × Nat := unpackForestRelative (unpackPagedWidths [
    (17, 0x19a58ad1c18a81b43091f828df80dc0b7c61a5835c1668e0c600a2a02df126860b7c411f8ed7c18d82b5b11ab82d7018c80b5306380e8dc56c01c7c09b802d20129e08367833031a09ade0c581eb1831a054de0c580d2f8318014ae98460532211bc1488746305221916c14d854570ab20291078a6093405a1881b828c40c5a0423020f81026003f),
    (18, 0x2193ec6f02113dc6302113cc5b021b3bc57055900844e914c1474021106c5b059e0086c1515c1d64051d008440d14c234b06d1c0c5402d0c0864c8dbc1474021d03e7f051900864099cc156f0358c0844b4d3c1578021d03e7f055a00864099cc156f0358c085ca0d1c083406d0c0834028fe596e021500a5f90518124402110345304d90083402d0c126e02919f93e),
    (19, 0x16a4069bc092f80a570d08c029902a3780a44088c6029101a2d80a6c048ae05590052200c530107d5c06cb63596453016a80358ca5b580c8c018a64cd9c063200e7b2369e02d90073d90343038a604d3c05a18e26a0747e02d30151d822370147802d10051980944078a60251015a78125f014a6024d005a18626205ad608dac0db38135f016a60c92804a201c6b012880314c051940017),
    (18, 0xa315c085c0559008449b14c147402110745b059e0086c1715c085c07590147402110345308d2c1b47031500b4302191e36f051d008740f9fc1464021902673055bc0d6302111934f055e008740f9fc1568021902673055bc0d630217143470cd2c2b47031501b43048fc0a37421b80b7c14d2c0d7010d1c145402df02b4302df01a3f031c00a372a1983d6f0d58c2b52),
    (20, 0x9441bb4f013640096401e7b00d6b0093418b4300b6402b4300b6401a3f00a6400a331516e01b430123f00a331316600c5804d6b00a5c03a6b00c7002a6700c5801a5f00a5c00a530d94600a4401c6b00a4400c530b13e031440084c01a3700925008360084404c530194400b5f0084402b4f012440084400c530083e030620085401b5f008560083e0084a8381f008642bc6f008442ac630084429c5b0086c),
    (20, 0x134900b4804453025620156000a3400c6a01b4b00d6e00b430084c102370635200c580515f00c600415701a5f00b6c00a570213d0146200b500092709846009440845b0096c07457015640094405c530094404b4f0095c03b4702c5b024570156400b4800c5300a360082eaa0530094425c6b0094424c53013540095401d6300c530093421b6b0148c0094401c5300b430097c1eb67014640096401e7b00d6b),
    (20, 0x1b4f0095c00b470082edd85b0084432c5b0086c31c570085c01d6400937008442f45300c6403b6f02b5f0235700b540125f00a37008442aa4f015680086407b6f0084e00d70063670545b04c530145900c580325f0146100c6001a5700d6a00a4f0085c21a4701458008541056b0103600834014700087c0dd670103600834014600086c0267401c5800b4a008540956300b4907c5b00b6106c5700b5101d64),
    (20, 0xa6600924009660714700c6805d6f00c700157600c5803d6b0147200c700256700c580156300b6a00946f71231945b18c5700d6417c5300c6400b6f1624f00d680236f0084e00d7000b671324700c5804d6b0083600c70035670083600c600167400c5800d630da3700b5400a5f0213f00b4800c53009270a16e00c580295f00c600195700b500092706846009440545b0096c04457015640094402c5300944),
    (17, 0x632095c828f00c6805bf1f14c48b61c53062902d38a6d43a4f192582d40448e126c05260290c14c00b66bd1a0759428f00c68acbf275f41d188d6f0ac603160eac66c70323003588a8b4446d06be0d17c28f80b480e2983148169409245cbb031c09cec083606380d5d816a824720e340516016f4616e2a3d1318086f40d7019bb08da834d40c60),
    (19, 0x2b10035e006474056304ad60758c06b100c5e7b8f4f51d8263504469078d00d19815b502366024b00295004b320d6f028b203160fab585c710126c131c01d268324901298089140d20809400124c029c0cab381d7e028b203160bab196c6e016cc571acaa350146c014c04f19805b312c63248c4119f81f390357a05ae4051e006340137e016e43716c06b10cc5a188ac119f806320357a),
    (19, 0x30cc02920042f00844cd29e025901eb78095405ad6025f00eb38095401ac78852826bd0457907af00d5d8163d02476026d002d9004bb5667f02ad2035a2a73d81d810128c03602973b81e8e02ad2035a28739809649fafc031da76bdce57a02af8025f266bb00c7697ae72d5c823c703f8206d140ba080ac400d780291c0320a36b580e728bad4025b226b30478e01ae80da2806ba02682),
    (18, 0x32321e7709a381d640519008647d9cded76791f9dc7675198246607190136602d90fd6f02d50ed6b0adf01a39048d4092e029c0bd67095f81c5404d5008542558c2a4f0892c1a47029b00a43029805c6614db8324f0a92c2247049b008240290c0a6004d980b562c8d0146402dd0997e091f01b6c04d58087c1c5d80c7c071d8137e02d90496e0f5ac0c5b0a4900a60),
    (20, 0x9240d96e0ab710158000b8c0934b00d800834700c700145400b8c06343052610147000a7c03a3b00c7002a3700b600134400a7c00a33009240287e01b4300a33009240087c9a9670137c00b5605b4b00d7004b470146000b4e02c540237c01b6c00a600083400b4393966009440545b0096c044570095c0256400b4d00c540094401453009448d9620357602d740247601c7400c640097623e7f00c6422e7b),
    (17, 0xe3e839c018ab6b5f05b20b5f446f80d7009ab020d266a62d7e12b906df826f80b5681a58f5f818d82d7912b9075c4128c0d7061a3831f158fca47c22370317068d22c6212308251828c00b4e2e2a14df822bc085e1dbe028e01adc236c09310298010680b43b11a02e30f6960d8035a3831c028a80b8c25a18e8ec18e02a3705b004d1014f80a33),
    (19, 0x3b1a03e0006b2ccc6f018e80ba34124600e80028cc021124a318368e0131809a080e470148c018cd1716c234700d7c06d120ba0813408095602d00025ba0a2b80d8c15b1c2963022bf00d6c06af20b5c812b881d70028bc025782eb20548e01af8045b804370348c01cfc091f009b900b7001088d714c06b20147d018aa76dbce9b681464016c8095f40eb880c70016ac66d8c16be00d64),
    (20, 0xe46500c660d45b016790096e0bc5701d690145e0095e00d64094530224f01a4b0124700a4300a6005b5500b5604b4b015690095e0334701c590134e0094e00c5400b4300a34fa96f00b6403b4b00d6802b4701c540137400b6400b43f616e01466009440445b0096c0345700c5e01d64011440084400c53f096a00e740158d00d655447f53c7d0157400c7402e8d0268100d80014660098c4fc7302e8c00e74),
    (21, 0x36b7802d500bad60147c005be01159c038a8013540042a00958c036dc01356005310628fc014c80556f0052a0115ac014f8035670052a00958c034dc00c620052b04a8ec018d00556f0062c0115ac018e0035670062c00958c038c400d6a0062d0328dc028c800a64056b780295013ad600a7c046b38069500129800854036b1818db8018ca0526e00635010958048be01c5b00a2b80314c0324800c5b004120028cc0125b09234),
    (18, 0x91900c58051500b6408d0c0a5c028cc0854ec97c0a442516c0a6c2115c0a5c095901a44024f008441514c0b5210918234b06d1c0c5402d0c192402d0c0824c496c536d02df0434b035c03347091501b7c04db0083402d0eba5702910ac5b029b09c57075900c54029107c530cd2c2b47071500b44028d00b4310d900b5a0c918234b06d1c0c5402d0c09248094c0b64),
    (19, 0xbf68e0253c6e2a0d36e014c030d985c9a8a25b0e48a1a8f405220592a0327204078040903928012500a0a8040c01826014b402090152981b6a024dc029980417811340106944d0c162d82457038aa0496c052bcdb5f016ad32d6c0e368126c014c12ad5c0db7013560106922d4c09b700b568e6960497c0529c5b470369c0493c052181c54026dc020d211a186b55016c816d2c06b404b47),
    (19, 0x24c0025b7f5ab80b5434ad606df0051c80a7030ace0ed7c051c02b5b012d806d5c049a00b530a6d81093c1d258135c012b80891c09220092401486029807a330eb6e1c6ac364d405248b45b024c2025804e2b8413f0727602900149b8093c03266044bc049180950096ac0258006330324b012c00719805ab0092801486064d0062d80834c76a608db80db3013560126b84d2c08af8095d),
    (17, 0x2d279492c38f8147004ae0c91c44f80d6c0936024901487ba62052ce717f26bc136e04a2de93c48dc1b5d092b02496a496956945b7035a0f6bc72490ab402970b2bc515d052f1057072a41568042e0817826b8095c04292e91c88dc0a5c19aa8a9b0447c192505af02490e4862b5e11ad06d5826a40a5620978cd6854bc225a0d2b04948125c0927),
    (21, 0x9b5802d8c01289c745b014b78085b402ace00856004b671115c012c80b47e004be0291d81328a0836b025aa810d34014700313a0141d0020a00306c00b6a0041a00cd8c048f400b78009bf002dd80107e01144004226e114c0128a0445b004be80d15c058aa014590062a80455c012aaaa35f026b78111b80349e0092400521802980036cc013560049aa94d6c4c8de25c6d004a209318c488be23b5e03e368025100d8c200d7c),
    (21, 0x4aa02d5cc15ade0095404e370051f4014f80827e016be80255003ae20137c005b80149c8028fa00c7101cbf00c5f4018be0217c00abe8035c4012e5dd467006320419ec029180098c0773b802550088de0094401a358025f0048ce0094400a318025b8018f8095760463f0025b00f8cc07145005ac8135ac026e200b7001ab380b19801aec01b5b006bb002d4c0328800d6b0042273118c012c80447e004be00d1d8058cc02145),
    (22, 0x1b5ac014720029f8055670045600085800f58c00c540055ac00d6700718800c6e0031480a34a008d6c013660028d000b4301e0f001c5b00515c00c55014d7c013560020d003b53004db800b56008d2c0136e0020d000b430020c2ef1270025540856b002634075670025f0065650165a8015690035940416700e5980316500917c01c5300417800852002591ef46f0119fc0096400d5f802c760025b001c66004514009447ab1ac0d57f0025900c57d),
    (17, 0x2a3782d2088d60b701a3382d2048c61469063082d88a8f8425f1d2d831b054ae1b64052a0295014a60b7046bb02da0f8fc0b603633055ac1ace53480eb582dc01ace31481424075ac18b60a3004227918c16d02c7e05b8071d828cc0b48d62d82d2338a63c610e3e0519814881c5b05220314eb6d434690a3a0291038b60a440629c8d88fade0d76),
    (18, 0x1696c158c036004257029702b64029501a8c039f00a7c0294d6b72029a5556f531b80c7e4e97c2d7e08db40a5504db00a664296c5679131f80e780f1b832590a5880e78061b80c6c02188b257295f80a6c24d946d69191b85c5e14978104e021083a5c02970295202570185e02970085208d901a7c048f809280294c0b70d319c0c64579ec1c8c029240b804f9dc0b58),
    (22, 0x35ac0084403718c0094403316c00b64002d2c0b16e002df000b4b02659803d6f0035d802d6b0051c800b7200559c00d6301651800c660111ac01c7e0051980084400918c0147e00319800c5b0024bb5112b00d5ac02d67002dc001d65004da800b6817b1bc06e7f0195f800a6800897c00a5c002d9000a53002dc002c76002d8001c660031b800b4815f1ac22d7f002da021d7d004d60009580815cc1fd6f07d1b80857d01f5c400e8c01a97c00b6c),
    (18, 0xbb1bc3e7f0d5f8097c091d8096c051980944ab1acf57f04590092e375f40954335ccc56f2f1b8757d1b5c40e8c16d7c158c0360043570d5f40b58095c4147c031c00a56024d84372035bc3370051f40c71065f80c5f025f1b46703190ce7b07230138002630ae7702550446f02510346b025f02467025101463025b80c7c155d80964111f8096c0d198156b0359c1944),
    (22, 0x71f00146c00211003a4f00c92c00d7000891c0127c0029b000a430585980546a0035a00426f0029b00326b0035c0022670049b000a3e00298c10956002d980856f01f5ac00c7c01b59c0157e0021500556300d1b400d7c00917c0147c00211000c53006d9800d6a002d580793e0035940636f002d980536b0035f404367002d980336300ad7c00b77006d6c00b4e002d4c0092ee124cc0092e0115ac0092e00d59c0117c0024b801d6500459800964),
    (18, 0xecd8c09640b5f8097c075d81154021537b5f16dfc096412df809340ede83377025f02376024d01372024d31b5b025b30b57329bc0c7c231f8847c1e9b81c7c04df00a7c165f8157c02dc04172021f0307e0a1f01c7c049f0097c021c8326708de81b72029800a760209c09348cd4c1d6e049bc0a6313194147403190324f0a92c0d680691c0a640290dc96e035b45c5d),
    (17, 0x4b67ed981269eb4ef1a682990e6de0c7c31b5829f0a6ce0a6c063a0ed8c14d22a6e0e370496414a20a66b09b029569ad6147c053ecd59e56d5236609bd02dda14be347a163b08db414aa136c05333496ca8dc4c6c21bd035c066ec0b6c11b7031b026c40a593d2b82910c8f40a7c2a3b029b086ca2c5e11a90294024bc0a5c09b2028f814a60934),
    (19, 0x12ce602590423f01164010c81adbc31b38096c0a6cc029a0112f80a5c016c80294c049a01b4e0226c024d391b589d7d01d18235bc16c600c7d032a8031c0042a05d63038de02510063183c7c048be051f0042200c53022f8021f341b380b6458cf60763009c60098c54cee025502a3780944088d6025f01a3380944048c604db405b28096e016f88f1d919b78257e03af8045f804be20b67),
    (20, 0xc8c0d37f02d8c00d8c0193600c7c009340a37300a630093408b710237c01a7d0092400a710627e0247c011360093400b7103a720127d00a710217e0126f00a630097c8dd67009640436f009340336b0097c0236700934013630096e00d7c07676009640657e05b590456600e760324b00d7001e760156800b5c00a470115400854815630357b0148c0098c01d7701565009647db6f0b67f00a560116400864),
    (23, 0x36e2004d7c005ad8149670018f800493c005258129660012a8004d7c005ad810962007cfe00d9ec0173b8026730036fc004dd8005b300c93f0014c80115bc0052a00356b0014f800959c00abf000a54001ac601e4f80063c00667f0018d00159ec00a40000b80007cee0051a0005b40026730038f40051c80063500093785327600edac0049a002b690012f8006d9c008b3000964142ade0025900173f00097c003aec004d64004aa09dd6b0012a803d5b80763f00e47c),
    (18, 0x2590336f0ad9c2366064e81136024d32b6b115f40e8c0d5bc0d8c0958c145f0314c097cb8d9c0b644d9ec0b8c499dc0954111bc09440d1ac097c0919c09440518c096e02df0cc7630dbc1d72045f8097c28d9c9b6624d341b6e025b00b661c8e81462025b80a66148d80b66104e81a6e031880a66084d8156b0359c093468d8c1576025518b5f044dc09345cd6c257d),
    (23, 0x18f804299c005b600fa6600dad600252002eb1800d620098bc0109b801a2c802c510046dc006db000628000b4e0014cc02295400eb5800970001ace01a95000937000a6600a48a00b5ac004b8001d670028be00315c01122000a4400247c0028f405d31800c7c0026ec002d5004d2f803d6f006ad60025c0012b380157e0010a800358c02d1c8009490088b600257c018ad800a600042ae0051980052400094f00106918c4fc00ebd8015650012c80dedbc0273f80447e),
    (23, 0x326e0044b800496c9e1530756cc0075ec00ab2800b640714de01b9fc031bf001c640016b800219002137803a670016d800a99801122801a440014880028f818d3580bd7d001d1802b5bc006c6009d630038de0031b000631807b7c004ade005150005aa000d6300a2e00121f001eb78014540016a800958c00a2f800c530010680021c012d33800a64032cf6002a300c33b800a540088de00291001a35800a7c0048ce00291000a31800a6e0014f804add80913780147e),
    (17, 0x151d888dc14780b440519851c014e27567093302970b4d64d7d1daf831b056b6235705ae0319016a60c700533dc51916ac1466052a1c578cad65d6a2ab1835a886bc0d6219a90318444cc156a06b10297812ace13f0a330291048d6157d053e0319d527c8c5a3eb59d5a826900a482eb18558414bc436a0ab50358856a4156a06b10494814a00956),
    (19, 0x836d6051f404be40367016de1c97c352d86257028de0318c25298126f014c60c57c14ad82157026de02d8c04a98096c6f4cc0b19811a48136401472025b9a4a780b491ead63b5a805a48dd63028a802d20073d0bb5f03cf4059c8049b09b53126a2071a0092c80a410e2dc1918c2e308536e096c4055c006b40324f03ae005580053e01243014820259924a381458014b2315ac1d1f80b4c),
    (23, 0x86ac0071980092a0008440042bc0055a80053300095600c27e00559400532000c6f00827c00b16800eb500136a0014a00025580089b80092e9eb2b6040db401ebe00347d001ce000915400abe800a7c0014b2030d7c00dbe000d7d001472028d4c00ab2800a640048de00519800522000c6300d4c2006df400636800b550094be0101b00062a802b5f0016ac006d4c005aa800a5f0010c139455c004b6001c660026920025102263580097c0878ce002570009ab000934),
    (23, 0x10dac00524800c5b0056aa00519800522000c6b0014b343c57c0ca37800c650306de05e9b802233003b490026c80028e4010b7000a480010bc002110098a7804d6a0086a20091a000d2c800a540014820065b80052080096601c28e0051a00053480256f002aca0031a00053780a946)] 6) 11
def cert_links : Nat → Nat → Option Nat := unpackLinksPaged (unpackPaged [
    0x52020a4001460828c00518009b2013600268104c820970812e00258104b00094081260824420480208f0411c0823410468008c041160821c4043020850410a002140042800820c0fe181d4a03a80074040e8001cc103980072040e4001c4103880070040d6281ac00350206a000d2081a4003402068000cc101980032820620c0c400184103002060000c00017820299603d58003e00001,
    0x8e8a11b0822c2845410880a10f04212304144081060fa201f4003e8007b860f7001ee003cc4079020f2001e4003b84077000ed041da003b01074080e11c1c200384006f060de001bc0036c306d800db001ae2033c8067800cf00198183300066000c90c192003240063840c118182002fc205f800be04174202e4105a880b014160002bc1056060ac00158002a82054820a90014a202940,
    0xcb821970032e0064460c880190043200063c10c78018e0431c0063020c60018c003141060880b82416c102ce2859c00b3021630c2c60058810af8615f002bc0856840ad00159042aa2055400aa80155002a02853c10a70214d042980853000a58214a0428c2051410a280144042880051000a10414104278284f0009e0013c00278004f0009b8a1370026c084d8009a821320c248704882,
    0xfc821f4143e6087ac80f5801eb003d0187a000f3821e3103c60078420f0801e1003b63076c00ed021da003b20875440e70e1ce0039c0072c30e5801cb003901872000e4001c6083803070000e0001bd0c37a006f400dd061ba00374006e020d90c1b200362086c400d8021b000360006a080d4001a70434e0069420d2801a5003461068c00d1021a2003420866480cc8019900330086600,
    0x1358e26b004d6009a0313400267044c428984112f8425f004bc08978012e82257184ae0095c012b80252144a400944112880250044a00093c11278024e0449c0093411230e2460048a089140122022410c48008900011f0423e0047a088ec211c0623800470008dc111a842350046a008cc21190222e1045c008b021160022b0445018859210a0420f1441a1082051038220214400107e86,
    0x17d002f5145e808bd0017a002f2085e010bc00177822e7205bc48b74116e802db085b600b64216c802d9005b008b58216b002d6005a810b308166002ca0859400b1c3163022c50458220b040160022c00057e08afc015f022be0057c00af0215c082ae2853698a64214a0a2901051040a200144002850c50a00a1011400828000500009f4313e8027c044f0209e0013c002750c4ea009c83,
    0x1c9803920471440dd941ba82371106de10da851b482365106c808d7c51ab12355046a028d3c11a78034f0069c08d3801a40c3411c67e10cf8119d0833a0067010cd4319a023340066800cd00199043320066400cc021980032f0465428c945192803250064028c7c118f0231b0c63408c50618a003140062410c4801868a30a0c61400c20218010300005fc10bf4117d842fb005f408be80,
    0x2150c4222081aa903402058440b008140902802040440800810010182203004050480a0100051efc23dc0c7b020f5431e80a3cf0479a10f1c61e3803c60478c00f1411e2023c01078000efc11df023bc0877410ee801dc823b80476e08ed031d5923ab0075408ea411d4803a80474e08e8461d0803a00474000e7c11cf8039e0473228e6401cc023980072c10e5801cb003940872800e4c1,
    0x24402488009100121822408a4810090009200023f8247b108f6011ec023d8047a048f4011e8023c04474108e411181223000460008c001174322e0245b048b211160122b82453108a60114c022902450088a00114002278244f0089e0113032260044b0488e2110072200043f0487e010f8121e8243d00878090f0021e0043c0086c310d4121a8043404866090c422188043100862010c01,
    0x274824e60c9c03137c126e844dc049b4113506269044d2009a4013480268824d00499e0933c0267804cd08984593080261004bf0c97e012fc025e844bd0097a012f4025e024bb04976012e8125a8a4b01495e092bc0257024a818950012982251864a2049440128802500449f049362126c024d8049b0093211264024c804990092e1125812478e48e049181123002460048c00912192240,
    0x2c10058104afa215bce2b78056e04adc015b412b68056b08ad6015a812b30856504ac80958c12b08455f08aba1157012ad825580ca986152c12a50254610a8a0951012a00853a18a70114dc129a8452e1ca5c014b022948652510a422148012900051d0ca361145852890851104a200943432860250b04a140941c3282844fd209f6113d8527b004f4089e6093c81277084ed049d6113a81,
    0x2ec8a5d804bae0975812ea825d014b9a1972442e2885c110b820170402e0805c100b78296f002dd045ba00b74016e412dc025b50cb64196c802d9005b200b64016b842d7005ae00b5c016b802d6825a910b50096a002d4005a800b50016a002d4005a608b442168412d08059824b300166002ca8659500b2a0165402ca8058f18b1e0163812c70058e00b0a4961012c20058304b06016081,
    0x32d0a65808cae0995813298665108c9c1993413258464a04c8e1991813230064600c881190c13208464100c8009900031f0463818c62398c013180062f04c562184993090061200c201183c13068460d00c1a0182c23058060b00c160182813030860210c04018041300025fe08bfc017f022fe005fb04bf4097e022fc005f218be0117bc12f7025ed04bda017b012f28e5e404bc0217782,
    0x371006e104dba21b74036e026db04db601b68136d006d514daa01b501369826d300da409b288364046c704d8a11b083360826c004d7a19ad0935a006b208d6401ac41358806b004d5c11ab80357006ac08d5801a8c9350846a100d4201a78334f0069d04d3809a70034e0069a08d1a699dd633b8067508ce6119c033378266d08cd8099a433348066804ccc1199803328266500cc61197c4,
    0x3c30278408efe29df813be0477a08ef209ddc23bb0277018ede09dbc03b6067690cece11d9423ae127590ceae11d5033a80874e08e9811d2043a38273c2ce7609ce0339b8273508e6809cc823978672d08e5419ca413948071e2ce3619c6c038c8471804e2821c4c13888471004e1e09c30337f1c6fe00df811be8237a0c6f010de001bc00377046eb0cdd601ba423720a6e304dc601b881,
    0x40f8281b110321205c24071280d050180a02c14020e800110000200004000080000ff821fec13fd807f80cfee09fd813f78e7ef00fde01fbc03f48c7e60cfb851f34f3e6807cc04f9801f2823e5007ca00f9401f1c33e1887c300f8601f0423e0807be0cf7c01ef413de807bd00f7419ed843da827b20cf5e19ea073d08e7a004f3e09e7033cc0879704f2819e4c13c60e78a08f1209e1c2,
    0x44c008970512e0225c044a848950112a02254044906892011240224804458e88b011140a228044482889011100a2200443048860110c02214143f8c87f010fc0a1f8043e0487c010f60a1ec043d0287a010f4021e414398c873010e6021c034380086c110d8021a4343480869010d00a194343280865010c80a190043182863010c60218c04318085f110be02178142a9283d61048ca0804,
    0x484009070520e02408548100901052000a3dc947b808f5091e80a3c43478808ef091de023bc0477028e71d1ce023981473008e5051ca023901470088e0011be0a35c846b808d7011aa123540469068d1051a2023440468808cc1518a3a3140460888c10117a222e8345c828b709166222cc0459028b105162022c01457048aa11154022a41454808a8051500229c14518889929132022601,
    0x4c7889881d30c1261804c282985013041a60414c002980012f8225f004be0097c012f0225e004bb82977012ea125d404ba0296b252d6025ac04b5809680d2c62a58424ab16956012ac0255414aa80955012965252c04a30a9450528a02514049e9093d012780a4e824998e93301266024b464960292b052405a4800490009200122e4a458148a0490d1d2180a43004858290a05210124200,
    0x50a82a024d404027fc34ff809ff013fa127e834fd009fa013f20a7e404fc029f8013ee0a7cc44f9029f1053e2027c404f7069ee013dc027ac34f30a9e30d3c01a77434ee809dd013b80a77004ee009da093b40276804ed009d9053b20276014ec009d8013a04273434e6809cc053960a72c04e4849c9013900a71824e08a9c10137a226c4c4d8029b00135a1a6b404d30e9a0193400264cd,
    0x54e82a9d0153a02a70154c08a980153002a5c154b02a92115163aa2c054502a861150c02a18053e92a7d014f80a9ec153d80a6f314d81a9ac153580a680d4d0029a0053400a64114c802990053104a61054c202984052f84a5f014be02974252526a490549202920152304a460148c02918052204a392d472028e4051c80a39014700a8bc951780a2f0145e028bc051780a2f0144c4a8590,
    0x5ae80b5b0969e62d1c85a302b460168c02d08459728b2e0165422ca8059386b260564422c84158f84b1f0163a12c70158e00b181162e0ac54258594b090961202c1c258302b02115f832be045749eae8055c822b90056f0cadb0d5b40ab64156a88ad5015888ab0c156102ac20158402b04155e88abc055760aaec055798aae0555a0aaac255484aa70954c0aa8c355180aa00d54002a782,
    0x5f88cbee0d7dc02fb025f600bec017d21afa405f480be8057d002f9c15f188be3017c602f8425f002be0017bc12f7805ee82bda0d780d2efc15dd88bba0577402ed845db00bb40976802ec825d882baf0975c0aeb025d600ba6197461ae7855cf00b981972e0ae5815ca04b930572602e4035c686b8c0571412e2415c384b81197000adf045b71cb6e016d61adac05b484b5e2d6ba0ad740,
    0x65300ca6019461b28c065180ca00d9400327c164f80c9d0993a03270164b0cc960192c03258064a04c910d92203244064880c8d1191a03234064584c8b0191603224264480c890190c1b1f8862fbec5d098b22316016290cc520189a2b130162504c470d88233100161f82c3f0187e030fc061f80c3919846b3084261080c1e0d8361b06c060c84c180582c1301905ff8ebff017f81afdc5,
    0x69d02d370da6e034d4269a80d320da64034c8069804d2a19a520b4a0169382d240da460b48c069084d1e0da322b458368b00d1409a2803444368880d1101a1a23434068680d0c05a121b420168304d0601a0a0b4083678a2cf1019da233b4067506ce6119c813368a66b08cc34d9860330c066180cc3019801b300065d8acb51996a032d4065a80cb3099640b2bc36548cca805950032982,
    0x6f482de805bc62b78c06f006de001bbc1377416ed84dd615b9c4373416e584dc615b8a0b6fc66df02dbc09b78036e826dc82db121b5a236ac26d502da611b4a0b68c26d102d9f0db3c0b66c36c69cd8b09b140b62026c400d8801b100361046c200d8401b041360806c082d8101b000b60006bf82d7529ae80b5cc16b980d6a25ac24b54ce6a884d4a1da920b52016a208d3d1da7a034ec2,
    0x74c84e9025d2003a24774480e8805d0823a10074104e7e11cfa0b9f4073e02e7c01cf8039e8273d00e7611cec039d0273a00e7401ce8039c0473800e7001cda1b984c7252ee4809c8c13918072186e4301c82138c1171704e2b0dc540b8a0271400e2705c4a13880570e86e1d01c361386c070c06e0c31c1413828070404e0801c0e0b80466ff06dfc09bf0237cc56f902dee11bda0b7a83,
    0x77e82efc05df803be8277d00ef809dec13bb0a77504eea01dd403ba0277400ee411dc21bb84076f06edc09db803b6c176d02ed905dac1bb54176a80ed309da603b4c076884ece0dd922bb24076384ec701d8e03b14276280ec309d648bac8075786eaf01d5e03abc075588eab01d540baa8075482ea901d500baa0075382ea701d442ba84175080e9f09d3e03a74274e80e9d01d3613a6c0,
    0x7b480f6901ecc1bd9417b280f6405ec803d9007b104f5d15eba03d7407ae02f5c01eb413d6807ac04f5801eb003d5437a80af5001e9c13d3807a700f4c09e9803d2c17a406f4801e9003d1c17a380f4701e8a13d0837a100f4105e7633cec079d02f3a01e720bce4079c02f3801e6e0bcdc079b80f3509e6a03cd0179418f115de2203c40178800f0f05e1e03c3c078684f0d01e1a03bf8f,
    0x7ed00fd809fb003f5827ea04fd305f944bf2417e480fc805f9003f1c17e302fc601f8a0bf1407e202fc401f725bee407d812fae09f5c03ea457d480fa805f5003ea007d400fa315f4603e8c07d084fa101f3e13e7c07cf80f9f01f3e03e6857c61cf8c01f160be2c07c502f870df042bde497bc80f7901ef203dd837bb00f7601ee813dcc17b980f7109ee203dbc27b50af6a01ed20bda40,
    0x8250504a020901411c1823810440e0860c0fc481f8103c0e078040ec181c070380206c140d8081b01036020622c0a878150102906052040a40813850231203e2407c080f8101a1603404068080c830190202e1405c08080f00d0e01a0403408068100c060180402c1805810090a01203ff8b7ff00ffd05ffa03ff017fe00ffb05ff603fe817fd00ff905ff203fd447fa80ff015fd043f68e,
    0x85b010b40a168042d00859050b202164042c02857830ae0615c042b41856030a81214e0c29c085285095421261424818470908c0a118042243844810860e1003420008400107f060fa141f4083e8107d020f6141dc483b8106a360d4041a0283383067020ce0418c4831810610a0c20418018300105e0a0bc04174182e8105d020b614158582a05053060a40c144182881051020982c1300,
    0x8908911f0a23e04474288e8111a0e2263c44c0889031100a2200444008880110f062181c43008860110c02214144202884011080220c14418088301102121de9c3bc0877030ee021da0c3b40876030ec021d60c3ac08730b0e40a1c8043882870830df0a1be04378186f010dd061ba04374086d070d5161a41c3249864030c802190043143862030c306176442e8185d010b906172042d83,
    0x8d2811a40633c3467808ce8319a0e32c2465808ca831930a31e2463c08c78118f0231e0463c08c78118f023103c62008c3051860230a0c61408c107182023040460028be0917c022f60c5ec08bd0317a022f4045e028bc01178022ec145d808bb01175062dc3c551a8aa01154022a41454808a80514f0629a144f8f89f0113c0a278044ec189d031380a25a5c4b40896031281224a1c4940,
    0x9160522c024560c8ac09158122b0242ea4854290a812130a426048403908012100241c1480cb901812010a402047f838ff011fd063fa047f018fe011fb063f6047e818fd011f5163e80c7c438f7851ee063da0c79878f2051e4023c80479008f1831e10a3c20478408ef851de063bc0477418ee811dd023b80c76828ed011da023b01470968e1011c20236e5c6dc08db811a54a34a046940,
    0x95a092b4025660cac81959012af0e55c0cab02956012ac025560caac0955812ab025540ca9459500b2a00254004a78294d8729b0253604a64294c81299025300ca60094c012941252804a4829490128146502049fc293d8926e364da0c9b409368126b0a4d6049ac093485265124ca04990193201263064c604988193101262024c01496c591ebd23c064760c8ec09181722f0645c0c8b80,
    0x9ad1934e3265914ca04993833260664814c68a98c833180663004c60098b833140e62804c500989833130262214c440988032fe4a5fc04bf8097d092f9065e43cbc80979012ef0e5d624bac0975812eb025d01cb982973012e5065ca04b940970892e1025c204b7c296d892ce3659c04b2c3965812c61658c04b141962812c40658804b0c1961812c20658404af4595e032ba0a5720cae01,
    0x9fa833f5027e80cfcc19f7893ee067d61cfac09f5813e80e7d004f9c19f3033e5067c80cf9009f1833e2067bc24f6c39e8953ce0e79c04f3809e38f3c50a78a04f0c29e1813c10a78204efc29df813be0677c04ef809de053ad3e73a84e7409ce8139a0e73404e6809cb8738d2a71614e2429c4813890271204e0c69c1813830270214e0409c08137f0a6fe04dfc09be0737c026e064d98a,
    0xa73854e3129b44d3680a69114ce12994253280a65014c222984053080a5d114b612964252c80a59014aa22924c5214da41074800a900052000a3c1146d2e8d61518c8a2f0b45c0a8a8451500a2a0144f168942d1202a218b44302876450dc4a1b814370286e050c07a180142e0a858150a82a150142a02850150a00a14014280284a1d0940a082b3fc527f804ff009fc873f8067ee0cfd81,
    0xb018160302c06057fc4aff815ff02bf81d7c0caf8015f002bdc157988af2835e502bca057940af0895d922b9a656968acd9559712b2a156540ac90759202b24056402ac31558212b04056002aba9757502aea055c44ab80357002ad825588aab00556002abc15550aaa78b54f02a981d52c1aa38954702a82354d0da8abf51502a26154481a870950526a02253e09a7c014f60a9e4253a49,
    0xb4d1369a02d320da448b488169102d1e15a1c8b353b66126cc00d95c9b251b64612c88159100b220163d1ec7a058f01b1c0962e2ac54258984b130162602c4c058941b108962102c3c1d848cb090161202c20158400b080160e0ac0c4580c3] 19 6)
  (unpackPaged [
    0x21053c0dd34f0370d2c0d43470310d0c0bd24f026491c0bc23f02608dc08104602000d807846801c1160068468018116005846001d15bc06c56301909bc05c25f015095c04c264011091003c24400b114003426c00801b802c56400a091001c07e00804d001c343005118801045a01255bc04156301211bc04046300e517c03845b00c115c02445300601b800d05600301181f956f07c558c1f846f07c118c1e945f07a116c1e0457075114c19436f05b4d7c14535705b0d3c14434704c05b8125156049051810013e03901b807c066014415805004600200fa7aec5fa1eb16e4f2c579cab14e7ae35fa1e8d6e4f23579ca8d4da8a34f6a2ad2c7ba3475de8d0e878a5f9eb296e728a5793c294e319a4f853692dc27a47709690e318a3f85328edc2723770928ce87815f9eb056e72815793c054e31914f853452dc26947709450e31813f85304edc2613770904cda8892f6a204ad7781271ee048c6ee05f1bb016c552057154014c2ba84f107a12c006847080a10c2ba03f10780ec00603708080cc41c82f0ae20ac200827001208c41c01f0ae006c200017001004c00003f,
    0x4f05f811813e03c01f80c4076076011002403e07411d01a807407301101c467806e11401a407407001b01a006406e15901b447406701d01b00440680d001a045406a4d3c1a834b0690d1c19c343072517c1c845b06f115c1ac4530660190065056019011819047406301d0178044061119018006405d011017856f05d158c13806e04b415818867f05f19cc13417e04a45980ec07e02f01d805d06605c011016857805901d015005c05715a0158064053017015056f053158c16067f05519cc0e807e02601d8055066052017014003400700b813803404f0d0c13524f04d08fc01802e0228d8808647204b916008407604b0150082462003916812825f020019800c02e04405b810c27e048091011c0440450d901100340430d0c11845304209b810525604109180f434003d11500fd34f03f0d2c0f834703c0d0c0ed24f03a491c0ec23f03a08dc0e037c0340d400d85700330d000d046003311500c837c02441180c037c02141580b436802a0d500b446c0290d400a835c02911900b835f02c0d6c0ac3570280d4c09c470023053c09047c0230dc00883480250d8001634a,
    0x10511bc40c463101517c40445b0ff115c3ec4530ea0dbc38135f0d64d5c38034f0d60d1c33c06e0c301982ed0560bb01182bc03e0a44dbc28536308b49a82102320aa0dec29c37709f09e824c27208208c82ac3540aa158c22926a08a09682a048c0a7114c22525a08909282944640a419ec27827a09109c822126a0a20d9028467b09d09e823427208749a827c45309e4d7c27535309e0d3c27434309a092025c23409a0d3025823009708f025834409b08fc26423b09808dc2542330940510248144090097c23c25308e04d024c4530914d7c2353530910d3c23434308b15ac22836b0890d9c22035f0870d4c214144083051021156b08411ac2084530ad55ac2b446b0ac114c2a436b0a60d9c28d35f0a04d4c28c34f0a00d0c27026a08c098821925a0860928204232063493c1652470624d7c16135707f019007505601200f818125f056495c17d36f0554d9c06d06607d011004003e07309bc1c837f03f01f80dc07607b011003803e07009bc1dc45006f0dfc0f807e03501d81e406c00c00f81b836f03d01b80cc06600b00f81b026f05001b811c02e07715901ac37f,
    0xfd11403d437f0d401f832c07610001b02cc03e0f4097c3cc36f0d301b83280660fe01702c803e0f109bc3f45640f00dfc34807e0c801d83010640c001503f00440b000f83e84740ef01d03e40440f40d003dc6780f311403b80740f601b03b40640f401703cc5640f211d03b00740bf41902fc0540f101103b43400ed11503bd34f0ef0d2c3b83470ec0d0c3e145f0f8116c3d44570f0114c3ac0640be41582f80460e911d03a00740e301103984640e501903880440e315bc3885630e719fc3906730d101f83180760bd41983840440df15e03780740d901703705680db019036005c0d915bc3605630dd19fc3686730d001f83100760bc419835c05c0d30d0034c4540d54d3c35434b0d40d1c3483430d1493c3412470d108fc3402370ce0df03305700ca0d003284540c90df031c37c0c511c033534f0cd0d2c32c3470c80d0c31924f0c4491c31823f0c408dc2fc26f0bf0d4830856f0c1158c3003520be09bc2f425f0bc095c2e82640b809102d82440b211402d026c0b215902c42440b955bc2dd5630b911bc2dc4630b5517c2d445b0b3115c2c045310555bc40d563,
    0x149123051818c1480510518343147114c51417c127455849c1461431190508164140051050056b115018843285a14119ec4d017e12f05d849516613f051044807210b41a84f436413c05904e813413a15ac4ec67b13205f84b817612345984e413404520884dc36404320884d436413309904d8343134493c4c924313408fc4c823304220884c034312f493c4b924312f08fc4b823312c11604a825c12811c049845812409704ac56b12909ac49c267125097c48c253109a168104822121091047c24412055ac48046b11e114c44002e11b0130464034119049446823711800d8470144117011043c03e1140d7c4541441130110444244110011043c453116114c44935f1120d3c43803e10c855043005410a015842c35f109855842403e15255ac54846b150114c52836b1440d9c4f935f1384d4c4f834f1380d0c4c416e12d0598489156122051847413e10d018842105a10801281008320e8493c3792470e74d7c37535710601903090560b900f839525f0db495c39136f0da4d9c30506610401102dc03e0f909bc3e037f0d501f833407610201102d403e0fe0d003d826f,
    0x1774d8461434918115806004501830d8460435118015905f136917c0d645fc34917e0d205ec46817b15805e823417c15885e446a17715b861145f184116c60845717d114c5e135b1764d4c5e034b1760d0c65156f19415ac63c567186158c5a106616801585d404c15620f055802c16a049c5c845816e28f45c046016c28f45b436c16e097c5b025716a11885a43501730d485c4a5f16f295c5aca3d171057c5bc15716b04f45a012715b08d8598144162114056823616405b056423611120b858856415708d858414410f20f857c14415d0570564450159159056034815b517c56c45b15a115c55c453165517c59445b163115c58045315e4d7c57135715e0d3c57034715608d843883e1b9517c6e445b1b7115c6c84531a96d7c65db571a92d3c65cb471a9497c65d2571a9093c65c24717408dc43493e10d04b859d056167011855483e15500b850925f13c494c50536f13b4d8c4ad166153051048013e14e09ac52026711c018812082214d0dec51c37713605f84c0176151051047813e11601c811883214f0d5053815414c04d053045314d158c4a5166129055852c134,
    0x1e7093c7842471d608dc73c16e04ca5581321461c841587200461bc20f86f002e195049c6502371ba011059483e16500b86d8340190049c6d445018f08dc6e006c16320f858c02e18b049c6282371b6017058883e16200b846882e1b428dc6d0137187049c45c82e11700786d456418608dc45893e11604b85cd06417301506cc04416020f858002e1ad01906c446416e61d06b186416e01506b004411420b86b43541af0d7c6b83571ac097c69da571ab08dc44c82e1b00dbc699b6711224f85c506616b01506a804415e20f85b586419f013067c4581a815a05b18741a7019067805c1a5013867004c1a415c066d87c19b017066825d1a0116467c45819d118467046019a15a868845b1a1114c67825f19b095c66424f1a60dbc68c36716f419866005c15c20f8658458195015061004c15b20f056c02c18e158063445018c158064c03619200d062c45018a158064447019001f060804c15a20f056802c18e00d863403418c118062c06c180013056483c15900b056084c17e00f056002c1880d285f834818a19d062445816a41d05a806418701505f404c15720f055c02c,
    0x5cc55bd70d56b5a8559d6195635cc11bd70c46b5a8119d61846357c517d5f045b576115d57845340008d0f8c16f3da05b8f3c16a323059cc541663090588aed15f2b245687f11571ef4558aec14f2b205287f01471ef05187b206f1b7819c3fe85f078a15c3fe04f078811c77c2371c620f871802e1eb11407702371c420f871002e1d908dc70c83e1c300b87ac5641d708dc74217e1c120f870402e1d505f87a44641d406387a036f1e56d9c74c17e04da5987350661bf20f87985681e4013878c5701e50dbc7883671cb41986f483e1e0116076c5601da15807780361d915807744701db00d87684601d205f87646741d8116074418e1df55bc77c56b1dc159c75c5631d005f813e96604f85587250661c901587543541d4097c7483481d1114c7423431d3693c74ca3f1d3453c74c13f1d0049c7384581cc11807283501cd297c72ca571cd057c72c1571c9049c71c1441c3114071416c1c315907081441c005106f815c1c6517c71845b1c4115c7044531bf4d7c6f53571bf0d3c6f43471ed517c7b445b1ec115c7a84531e76d7c785b571e72d3c784b471e7497c785257,
    0x23711488e445b238114c8d834e20105588c835023009b08bc24c234093c8cc24b231091c8b824322d09807fc14626c15bc9a456b25d159c96456325811b895846b25511a8948466250118c93c462246116c91045a24311588e84532350da88b036621405987f815622a15948a447822811a087012421b049089468c21a0490864124218049088c58c21e11a0888458217049085812421e158885412421b15f086447c2160d60860348216114887046d21a117c85c4532150d2889857d22415bc88456322011c087c46021d116885012421211c084003620f11c083435421119d883857620c11c882c46820a116082437a202049080412420004908105701ff049080046020255a880546a1ff519880836a20109a87fc26620759e881557a20355d881c47a206118081437a2030dd87f81242a819fca9467b2a119dca7467329b15f8a6457b29815e8a5457629315cca4857228915aca1c56a28515989f056327711e89d847622b08d089c17e21305d882016e1fd05987e05651fb11a07e44701f815d87dc4581f511c87d04701f211607e856f1f615ac7cc5671f1158c7c036a,
    0x28b1238a2848224608d091423421e05d8a2067224408d087417620b05b082814424308d0a1816c24208d090423428315d09fc48c27e115090023423f08d0a0457423e08d08f423423c08d09fc58827e15e08ec2342841e38a0868a2801a089e858a27d12388e823423908d09e456c23808d08dc23427915888d823427b15ac9e856327811788d423420905b881416622c08d080c15623c15b09bc16426e05509bc25826e09509d446a27411a49cc468272119891c46124e11649084512710da89c036621a05d89b416626b11649a8458201459080115426704d898c14c26004d09801402650934990249262091498424125f049897057d26811c499847025e09c07fd15423c11a086016625c15f893446924511a096c45925a116085c17623c118090445024c15a89005622570d9880815625411b094c26023f114092c56a23e158891c36a2510d9892847c2490d1092847824911a08f035c24e19f893467224c15e892c57223911e892037e2470dc8858166245158885416624111908f437c23c0d108fc46423d11e08f046824219f890057a23e15c88e047a23b0df88dc45c,
    0x2c10490afc0662bd0178c0867f30019ecbf86772f919ccbe05762f711f8bd84762f51198b442342ce05f8b241762c405b88211662bc0110ae81642b80550ad817c1f80518ad01542b915bcadc56b2b5159cacc56327508d09d023427308d09f867c27208d09c42342ab05d09c02342aa05909bc12426e0490aac3682aa0d909b41242b115e8ac05792af15e0ab857628a15c4a445692841584ab447a2ac11d89b02342240618aa417626b08d09a82342a715a4a9856826908d081517426808d099c12426608d084816c2044590a8c1462a01a34a905812a2160097423421105b080d16427e15e097023425b08d096823422205d8a8068e29015e4a2057829f15a4a7856825908d088418625808d0a7016427e15c0a0c56025708d0a3c67a28219c8a6847625608d095423422905f081c166228051095023429715f094823429605f0a0456025108d0a3867a28019c8a2847a29411d894023424f08d087c17420c05b888014424e08d093423428d1630a3045424c08d092c23424a08d092423428d1620a3057824808d09f846c24708d0a4478e2901e08a3c68a28e1a089ec58a,
    0x30f1140c4816c3100570c3414430e0d34c3445430f1590c30144313517cc4c45b311115cc2c45330a4550c281442f408d0c101642f308d0bc82342f108d0c1046430815d8c1c57430611d8c144742f008d0c0c1762a00514bbc2343011190bb823420945d0b0c0442ed08d0b2115c2fd1a34bfc48c2e808d0b1d16c1f80510b9c2342e608d0b942342e40490bf468e2fc1590bec4642e308d0be80642dc08d0b1c15e2114558b6c2342cc05d0a701642c60578b4c23429605f0b3c16c20e4558b482342cb05d8a1816c2c50570bd04662f31190bc83662f10d909701352ef0d50b08034263053098c1342ec08e4bac2352ea04b8b9c57d2ed0df0ba42702e715f8b984542e50d50b900542df09b0b8824f2e1092cb802472de090cb742602d709b0b580242da093cb6424b2d8091cb542432d40980bc056f2ee15acba05672e3158cb704662db0db8b4c3662d20d58b040342d01190b3c3742960d90b3447c29c0df0b3036c2cb0d58b2807c2bf00d0b2047c2c759d8b1957e2c711d8b154542c60df8b143642860d50af50542bd00d0b081242c2116cb002602be0920b0c56b,
    0x36f0d2cd9c3473500d0ccfc16e33f057885114621404d8ca406e32501b0d3838c3460490d283503450490d305803490d00d101243430490d284703420490d041243491150d2038c3400490d0c24034511c0d082303430d80d0834434109f0d1923f34608ecd1023734008ccd3534f34d0d2cd2c3473470d0ccfc12433c5178ccc1243320490cc412433c1600cec38c3300490cdc35032f0490ce45803360d00cb812432d0490cdc47032c0490cac1243361150cd438c32a0490cc934e33211c0cc427c32d0900cbc47032c08c0cb436032c0d10cac27c3334d84ccc26133048fccc023b32e08dcca823333d51c4cf437133a4d3cce834b3380d1ccd03433290490c9812432608ccc9c3433250490b2904e2ca00f8f2d57f3ca55f4a555753c255ccef156f3b5558cf2c47f3ca11f4a544753c211ccef046f3b5118ceb945f3ae116ce9445738e114cd3c23433e05f8cf816e2c9457884d1562c9053884c14632801f8c9007c3220df0c8435631d0d40c7c57031b0d00c7446031c0d38c6026031b1150c6837c3190db0c5c0343204d3cc8034b31e0d1cc583433140510c40340,
    0x3270230e3c04438d1590d9834038759c0e2146038c11f4e1947136e1174e2c4553744d38d9434237f51bcde94633640d088711463881190e1c3643845150e1036436d0d50db457038411c0e1857d38515c4dcd45e3830d58ccc07c21b4558e0056437e19c0e0457c37f11f4df445521a4518dec3642194518de057037a15f4de437c3770d5885d15637600d0cc807c33101f0db457037415f8dcc5723720df8dc437c3700d58d1817e34605b8cc007e36d15f0d8c3403620d40db446c3610d40d8035034505f0cbc07c35f0d40d7825035d0d40d1416e3690518db857e36c15e4dac57236a15c4da057035b0d00d1017e34405b8cb807e36611f0d8c45c36211b0d8845c34305b0cb406c3430578d7814636311b8d844693601188d7c46135d1180d7034e34205b8d0815e32c01b8d0417c32b01f0d0416e3590578d6005e35608e0d5456e3530988d4826036555f8d9157c36511f8d9047c35b1150d6837e3570df0d5036c34005f8d0016e32a01f8c9807c35100d0e2946f38951b4949465382518cdf145f375514ce2836f3890db49483653820d8cdf035f3750d4cdbd34f,
    0x2244558dec2343bb11d0de823437908d088d15637808d0ee068037708d0dd81243ba1a34ee448c3b71198dd42342214598ed804437408d0dcc2343b30630cf008c37208d0d3818c33b0230dc423434e05f8eb068037008d0ed068e3b21a08ec448e3b01230ebc46636f08d0d3418e34d05f8ce808e3ac1a30e8445036e08d0e8046036d08d0eb057c39f1180db023439e1180dac23434c0630ce408c39d1180da82343698d80da412439c1180da023434c05f8ea015639a0d00eb468e3ab1a24ea86823a91a04e9c6803991140d9c23434b0638d2c17e3a605b8ce008e36608d0e9058c3a115b0d9423436408d0e8057c36308d0d882343a015b0d8423436008d0d2817c33701f0d7c23436d8550d7423434a05b8da615635c08d0e8457e39f15e4e7857239d15c4e7057039b1178d6c23434905f8d2416e39a0578cd807e35a08d0d2018c3350230e5c57c3590490d6012435708d0d2017e39605b8e5406e35508d0e4c67e35408d0d4c1243520490e443723900dc0d441243a35a38e8968c3a31638e8858c3991590e6048e3941230e4847c35008d0d1c18e34705f8cd008e,
    0x3f4093cfcc24b3f2091cfc42433f00980fb835634605d8d181663e90d40f9c2303ec15a4e7e5613e60d00d101763440598dc01653eb0578fa44593619144fa034e3420598d081563e70538f9845434005d8d001662585174fbd4552580d74fbc3553ed4d3cfb434b3ea0d1cf9434333f0598cfc15629b55b4ffd56529b11b4ffc4653fd517cff445b3fa115cfd44533e408d0cf817633e0598b3915e2274558b3814e2270518f883643e015a0f783403de1150f743743dc0d90f8534f3e10d2cf7c3473db0d0cf644663d80510f4c45032105d8f5816c3d41178f4c5643d20510f440443d7517cf5c45b3d5115cf4045338d08d0f386743a41140e302343c85e00f2557038b08d0f3458d3c75604eb456d3cc1594ed145e3a31148e282343bf55fcee95733a21148e2423429c05908991562cd0530e2023438708d0f245743c811d0e182343c55590f144743ac1190e1423438408d0eb06803c51600e0c2343b35178f1c68d3c61a04ec956e3c41198e082343c30630cf408c38108d089516638008d0f0067437f08d0df82343be1e00df42343c11a30efc58d3bd1594df0234,
    0x427095909446841c11a108c45842111c107c45841c15a909056f42215ad08056741e158d07446241b1169064464418099102412440b0991058254408049101002441409f103426c407049104414c4120951018124410015103446540b11a902445f408116d01c457406114d01045b41715bd05456b413159d03c56340e0db903026e40a0959014124403009127145f49a516d259457492514d27035f49a0d6d2583574920d4d23d34f48f0d2d2303474850d0d1dc25f463096d160257441094d0c924f426492d069247402490d0c823f42608ed06823740208cd55145f54a516d3f54574c7514d55035f54a0d6d3f43574c70d4d30934f4c20d2d2fc3474a20d0cf9015f34f055cb4514f22b451cb4413f22b04dd00412d1eb817c6d60570fda13c1de8470fd80fc1de0373ef08d0a5817c22a4558b4014c3ee08d0ff84663ed08d0d3418634d05d8fe44603ec08d0fdc3403eb0490ff06793ab99c4fd84503ea08d0d2c18634b05d8ebc17532105d0fec16e3e908d0fa02343e70490fe456936c9584fe045e3e608d0d241763490598fdc15e3f61590f942343470618d1c176,
    0x48451552103554824d3d20834b4800d1d1ec34340e490903823247801511d824446a04911c834047111411d026c46904911c825c46804911bc13c47115911b126446c09511c024446704911b804446500911b03524680d011a045446a4d3d1a834b4690d1d19c3434650d0d1d545f475116d1cc45746d114d1ad25646b0919198124464009118437c44f098117c57045d0d0113826044d094117445445c0df116c36c44a098116803446251b518836d4604d3d18034b45e0d1d164343449094113c374448095115c244446049114c45044e0dd115426c4450491134364452091111012444c095114845444b099114c56444a0dd1144244443049113434044c08d113034444d115112c23444f4d3d13c34b44e0d1d1283434480d69110340444115111934f4460d2d1143474430d0d15945f456116d150457450114d1243644334d790cc34e447495911c246442049110036443e0d510f047c43b0df10e44544380d510dc05443f15bd0f456b43a159d0d85634350db90d035643309890c426442f09510b427c42809910ac25442811890c056f42e15ad0b056742a158d0a426e,
    0x4b549512d42444af00a12b40244b345252cc1394b200792c40124af04a12ac13c4ad00612ac25a4b60da92dd2554b709152d823d4b404a92c01284ae00a92b00264aa00912a036a4a709b92982664b8096d2a42531da817c6320574a500bcd4405748600752f44544bc0db92e83663e505bcd401674b904d529013448504b476606f18a819d28c0344194904f5245d4a1116d28045749f115527825b49d095d0fd24f430492d091247417490d26c35643d497d0b925b422495d05525343c493526446d4950db526026c49709810e924f42c492d081247413490d0e524d437453d0411434950db9250356436497d0a925b41e495d03d25349300d124436e4900d5920826f47509ad180267456098d2283404891140f5256e3f895ace6e56331c958922034048009bd1cc26b45e099d15026348e097d2342533e8916cd7245348b0d391f425f471096d174257453094d22824f489090d16c26546e056d168157488115121c36e47b09bd1b426b459099d14026348600d11fc3424830d911f835048115a11f434047e11611fd56447f11911f445447c0d911e406447a09711e4233,
    0x4c900d13e42394de04d13e837c4f809c13741344f508e13cc16c4f104d13d835f4f40d6d3c83574f00d4d3701344db05113b035c4eb05713641344e9091135c1444e804913b824f4ed092d3a82474e7090d3501344ef0db13982604d304d0b9d14f25c451d25412d377059cb9914d49404b53842494df09853781604da090136013c4d208ed33c2334dc04fd36c13b4d904dd35c1334d604bd3541234d108ed3382334d405413481604d1119933c1604cd04a13343564ce11993301284e0116d3744574d30d5934024b4cb090d32445b376015cb9104f49300753ec56b4f7159d3944664e40db938c356375059cb8d15f259455d3881354ca04d124812d4c800d124412d3ee05bcdc016749004b531836e4c50d993103563ed05bcdbc1674c304d523c12d3f799e8e6a67236c15e8e7e5724be0d00fac17e3d395b8fda56b3de95a8c3e566399958cc6e5624bd0d00fa816f367059d30415f4c0057490c15548c04b4f9e56a36111a8d864623e705b8f9a45b35b914d22234e3e6057cd6c1574be053d22012d354059521c12d4bb09812d83624b608f52a003d4b504a12ac024,
    0x23404d543012d505049545025426345714b446e4ed11894b035d5240d554ac2565240954b8414d233051542c13d50404d499112d52a049549836c52305b147006c51f0531498568522057146405052315a148825c51b017146005051f09793ac252263457147056851b017146435c51805714a0569524117944445d5270db93a83625250d79490249513090548415e520057547815c26245554741522e004f48c413550a04b540c12551a017945c05250f049145025c2df04f48c013550f0d793a035251511b939c4625130d5544826c51108f8b7814d22e051542413d50204d544012550e049098d15c50c0d7942c35a50a0d5942435226449694202562ea4579404136501049941835a2624d5941425e504096940c256502094897d15650104f940412e532117d3e14535310d7939835252e093d4a424b516091d4342432e9453c9791472dd04f48b413550704bd25c12d500049c94c125497098152446f54811b4c3e465546118d51445f4f7514d51036e4e40db551035e4e50d494d02624ff09813f816d2520594ba114f25d451cb7013d22c04d525812d4fc0d51380134,
    0x4a4049077606f191819d58403f4a30490f4406a38f019cc5c0664bf95915d047e57211d92882343f505fcf6c17e3d005e8e3817731605d8c2c17257105155801441dc81fc63e07755f01108f146855805949c515555d051528412d55b05f49c91755570554bd114d270451528012d37d055cbcd14d49f04b49bd15426e45109c9465558116555c45526d451954d46b545519cf4e45d55c116d568457559115554836a5440d9951035654d0d54df016725805755581575550554bc114f26c451d27012d4fa4d913bc354550049154424f511092d4ac24754f090d53826049b04b554c56f4fb558d54846e54d0d995303562ee457c9a5157235051552c13549a04b43ce85f06ea15d50c27049904b499d361542058150427054705113f157c53209c14c4260511094550024d53d09154f0255511092550814454015f14c037c52d11f147c26c53d11f14f04705270df14ec15c53815b143c36c51511f14e427c53709b14d812454311b55044615310db14fc24f53e092d4e8247535090d4cc25953008fd4b423b52708dd4542335300db93b836252c09654ac24552f0514b8813d,
    0x58815ad3201243b6019cbe905f5a619ed68c67759815d965c47e595119931c2343b505dcbe516f2b345a8a751671f14599650145589051161c0443d995b5318234585059131423458305f0f6667e3fe99ecebe67332199c93124504c408d0ff817f3d905e8ebc17732105d8a1816c4c308d15fc36b57e0d8d61047e58211d96044664c208d0ff417f3e105f8f5c17a3ae05dcc8017631305c960014557d0510fee78a3a69e08eac68a3ab9a093064504c108d0fec18e3a6061930023457995bd5e456757881695e00563d599f8fea67b3df99e8c466763a599ccc7a6724bf91412fc2343fa05fcf7c17e3d505e8e9417731e05d8c4417257b05bd5ea16e57a05b55dc16c2850594a161624bc08d0e4817531905d15d41644ba08d15cc17c3dd05b12e423456e11c95b834d4b8049159404d4b704912d812456800d15b423856a00d12b812456809315a892856a00a12b00144ab00515a036a4aa00515b847a56f4d955bc35556e0d355b0a3a56c04e92a412456b00e95a403656700d159047c4a804915903784a7049129812456511e958c37e5620dd92941245700dad598363,
    0x5ab0600f6646d54808d17041642a351c47e54705b629c16d817054704916d4b805b50a015182345b006316a81805bf055169d68c54508d16b418c54408d16f01545ba11f56e427c5b429c16d815454e08d16dc57d5b515c56d037c5b30dc16c447d5b011c53f82345ad117d6914531f945516ac57d5aa15c4a5817c5c215fd70057d31195d56f85735bd15bd68d5635bb11f965c47d5bb11b96604625b82df96c8b725b809f96c82724fd08d16bc17e5ae05f56b017c29505d56a41722fe457cad515a2a1455c7cd1562f805349d81454fc08d169c4644fb08d164814458801113e82345a512313dc2345a4063163c1444f608d16881544f408d16801444f304913c823459e05f13c41244f008d16701445a111bd67c46b59d119d66c4634ef08d166816e59911f139423458e0510f6656d4e408d0a701642fd457ca811573d999f8c866724e308d0edc17759605b0bf115d4e208d13841245930d653801244df04916443715900dc137412458d0d2d62c3434d3049134412458d15d93401244ce049162c5764cb049164856b58f159d63846658c0d6d6283534ca0491324124,
    0x55f8d1d78034369b55bda3556b647559d86956369b11bda3446b647119d868463613517d84c45b55e915d8444536090da98083625f24d697c834a40004807aa06f1d601ac6ca067174018c3ee85f150a16c1d68570aca14c3ee04f150812c1d60470ac810d7b403c5df00c09f957855d08d15702345d605d4ab51655dd055556c23455a08d176c18d2ae46157541653084574ab11553d995f55642345d905f0ef41673074574a7016455808d0aad16455708d0c1115c2aa4550ab95755d615a575456555608d0c0d15e2a945596f035455508d174445f5d0114d72836a5bc0d9973c05e5ce014972d57b5bd55dcf5656d5dc15ad7685675d8159572447a5bb11d96ec4665c811955502343bc05dca6c16d5d705a97501675d305997481655cd0590c0915f2b94568aa11571fa455969547455308d166446455208d172816454d08d0a5817c1f845595302345c705b152c2340f7a17c1c68575cb19fd6996735c915f97204765c6119952823430045bcadd16a2a5459c7d916627705547c01545c505157101440f5a1bc1be8675ba2e316dcb805ba0a316dc28054908d16c418c,
    0x62b15d98a447e62711998403785f94da97d43586240d21880a48620052131c120147a1ac29e86361f012186c0445e600c183c3786190da13181205e500c185c3706070d8131412060e0de881a3604c404817900301e001ac65806361811f9858476615119983037a6050dc98503484c2048077c07b19401cd78c0301d881bc76006b189819c6240634a2959182a47e60391d982837a6030dc97cd3685f30d618483485f3c9217ce1484a2048075e07f1d701ec61a07718601cd7ba0485e081117b803c5e000c183c47c60e11998342444bc95917d334860b09117d21485e28111841561610118583145f60c116d5d245760a114d81c47460609112ee4544ba95918102445f0812182156960811a581545f605116d5ca457603114d80056560015d97dc4725fe11c97d84625fd09f97ecb585fb05617e80585f811517dc56b5f6159d7d046e60115bd7fc56b5fc159d7e45635f511897cc4525f00d997bc2345f1516d7c435b5ee0d0cf4645d5ec116d7ac4575ea11557a03565e700d179436e5e40d5928e4545e20db97840345e9517d7994535e90d7d7983535e34d3d78c34b,
    0x64f097196856965911b98c04626581179948b52657097995025c652054994005e64e0149448130511050197457e62d15c996c36564d0d9193027c64a293192c23e50d050192812867215bd90956367111b98b046266f097d9a425b65e095d9242534ff04c1a3057f68a15f4c2e57568715cda1856f641558da1447e62911f5a1446e62b11899d03726480dc17f135a4fd04817e03484fc04819184645f70d61898348623292188c1484fb04818780444fa04813e41406222d2190c24962205213e013064412319083805f60d6189434862129218841484f704819003584f604813d41306380dc18f83484f404818f03704f204818dc37063a0d213c012063811a58dc46163f11bd8f446b63b119d8e44636360d893bc1204ee04c13b41404ec04c18c846c63009413a813062f09118bc2544e904c18c036462e095139c140634097d8cc25b631095d8b42534e604c18d447c62c0dc139412062a0da13901206280d8138c1205e800c189856b625159c52685b0a8a14d88837062315ad8845675fb4d697e935a61d08c132401061d116d87856b61c08c132001064519ed904677,
    0x6720e015141206710dc151012064b0985a0825d67e095550c13064a2d619f426564b096592815854104c15001306821a319c048c68009a14fc13067b09519b858c6800db14f814053d04c14f013067e16319f458066712319e825053a04c196447c67909f19ec25c67909514e413053804c19dc67c53704c197458c67a0d919e028c67609f14d414068415f5a0c57167111f1a0425f67f096d9f0257675094d4d013053305019cc26953204c19c024f66e092d99c24765d090d4c413053004c19c047e63411c99b426966b09a19a825552e04c14b414065c09914b014066c095595025452b04c19b857e63315c99b436d66b0db199036566a0999990265529050199847c65a09814a013066201f196424052704c149813066619e196025052504c1980060524050194825051d04c147002066219e194014051a008146413066011b193825051704c19a067966415b992c56d66711f98c447266511b998cb62664096596c25164d094198c16251604c198406e65f0189964354515050145013065c09b144c140653294194c150651017193c0506560139954042653097194415c,
    0x584cd1d8633436b31595acc5766b111c9ac03726b415bdac856b6af159dab85636ac11988a01446aa11f9aa44662200511aa00446a611f9a9446620a051165d56f6ab55ad7215676a7558d65c46f6ab11ad7204676a7118da9145f6a4116d604457615914dbfd56f6f755adb615676bd558dbfc46f6f711adb604676bd118daed45f6bb116d5f3457613d14dae016e6b50599ab51566ad0519a8c12e1edc1bc6e7067101e17c1eb857101c13c1eb04755c04817b003055a04817ac03069f0dc15641205ea00c053e85b0aba14da6957b68655dcf4256d6a115ada8056769e1595a6447a68511d9a144666921195a7436a69c0da180535a554048053685b0aaa14d7a403064451d154c1206351191a3c3485520481a5825469809a15441306960971a5436454f0501a5c25f64b096d9a8257694094d5381306930dc180135a54d0481a4436054c0481a3c46e0f2a17c1b685769a19fd91567369915f9a4847669011998203705ff4da9a3834854a04803c286f06ba19d7c403c6840e0152412068b0da152012064a0dc1a0c3805fe4da1a243586882961a20158546048191968c,
    0x62904d965c12e6d551d1b204646fc05f1acd1566fa05b1ab012e0fae17c1d38576fe19fdb596736fd15f9bec4766f91199ac91666f80511aac12e0f8e1bc1cb8676ee0e01b7418c6f50591bd012e6ed0e01b7018c6b04591bc81546d75a31b7c3806da0631bb035d6ea0d55b9c1366e90d95b941366ec1a31b901346e304d1ba858c6e91601b881346e40951b983586e30991b9047c6e311c1b9c57d6e515c5b882566ee15f5bb45716eb0d7dba03576e104d9b7c56f6d4558db7447d6dc11c5b6845f6d3514dbd857f6f315f4c4f5756f115cdbc056f6d2558dbbc47e6c511f5bbc46e6c71189b803726de0dc1b6c17e6d905f1abd15669204d972012e6d71191b081446bf0111b5448c6d40e01b4c18c6c10511b441546cf0511b3417c6cb0511b4046f6ce11adb304676ca118db2416e6c811f1b181646aa04b9b1016c6a904b9b0856b6c1159dafc56b6a80079b5867b6d219ddb1c5766c511f9b0c4666ae4599b001446a704b9af80446b6f1f9ae7c766a4d199ae417e6b605d9af01446a404b9ae83646b94d3dae434b582cd1d85b3436b70df1a9b3566b64d3dad834b,
    0x70b6d39d0c17e73605d9d4013470b04b878a07f1a381ddd3856e74d09bdd3026374a11d1d24464715e5a5d1856871aed71cdda747440991d2c465748093dd1c24b745091dd0c24374115b5cfc47c73e11b1cf4044711e5c5ce857073809f1cdc26c7401175cf024f73b092dce4247736090dccc5686aad195cc426c72c19f5cbc57072d09b1cb023e1f88585cd046a73209bdcc026b72e099dcac26371f0dd9ca436672415f5c9847c71d0999c9057e71c0dd9c8c05472015f1c7847c71d0111c8446d71f117dc7045371a15a9ca056f72715adc94567722158dc6c3667190d59c5c5657150d99c4c57d7110d99c3a37f70e0dddc3034e71495bdc5a56b710959dc4a5637160dbdc5036b7120d9dc4036370f0d7dc3435b70b8d5dc2c35384b15be11056b824159e02c5638040dbdfb436b7d90d9ddfc3637780d7ddb035b76a0d5dd3c35374205b9cd416672a0559c6013e70a04b878606f197819c35a85f051a15c4e083f0a020ddc2012e70604b9c1017c70304b9bf957b6f055dcf5f56d70715adc145677021595bf447a6ef11d9bbc4666fb1195c041667000591ad1156,
    0x7890945e0c25078e0911e3027c78a09b1e1825c7860941e2045e7870d49e1425e7840971e3447a78b11d9e243657830d91e0823e7a915ade985677a50da9e903667a1097de6825b78f095de042537d719edf4c6777bb11e9f184767c50dbddb836a7c00d9def83667bc0d39eec34d72b0599eac13678004d1c4012e73e05d1df816477c05f1d2816c1e681bc6a206773d0199df457e77b15d9d2017e73c05d9de815470f04b879607f1a681ddde405470e84b9dd816477404d1c3812e77105f1dbc1347770dfddd437e7730de9dc83777700dd9db837274705f9cec17670f6579db413470d04b9d17e7a739f9c9c2dd6d719f1b1d1417e73905d9dac16c71904f1c2e12e76509d9d9426676811f1d91b7c7606dc1d8c17c75a01c1d6407076411f1d8c37c76209f1d7407c75801c1d8057c75f0dc1d75a7c75d01f1d69d7c75a11f1d61b7c75909f1d6017c76775f9d99d7c76711f9d9847c7616df9d79b7276509f9d9426e76105f9d7817275c01f9d6c07c75701c9d480257530dd1d4c2607550de9d5037275209d9da426f756099c78e06f1a4819dd440277436df9cd9b76,
    0x7e20511f8c46f7e1118df7847c7dd0111f7c45f7dc114c37284f057a11def067d7ec15f5fa856f7e4158df8047c7c60d89f6c17c72e0559c6c13c71204b9f6807c0daa17c1568577d80d91ea41347a804d1f5858c7d50e31f5018c7a604d1f2817c7d20551f401447ce05f1f2416c7cc0511f2836d7c90d95f4446f7cf11adf344677cb118df2016e7c70df1e901347b004d1ebc13479804d1f1057e7c315f1f0817e7c105f1eb01347bf05b1c4412e72c0599ef41347a504d1ee03787ba0991e8c24c7b40991ee047c7b10df1eb83747a00d71ecc3607b609f1e5c24c7b409b1ecc4747ad0dd1e3435c7b109a5e6c2557af11b9e6046c79b0995eb82597ad0945ee436f7b70daded43677b20d8dec026e7ac0999e9424c7aa0955ea047c7a709f5e8c25f7a0096de5c25778d094de8824f79f092de5424778b090de8c37a7a20dd9e7826979c09a1e6c25578a0991e742557840951e8047a79f11d9e7836d79c0db1e4036579b0999e402657940db1e483607880941e585707940db1e4846c7870941e4056e78215b5e6446e79811b1e5c37a7950dd9e4c36e7910d89e40259,
    0x84215ba06456284111fa10047c83e0dfddcc3798380dce0d43718070dbdf4c36383009fa0ac27282805fa09417c74b05b1c9413e71084ba08c16482104d207c17c81d04d208836f8200dae07836781c0d8e06c16e81a15f20541548180591c9013e71384ba05024b811091e05067681215c204467681015a203c35c815159a00426b7e7099e04c24b80e091e00026b7e5099dc8c02e81919da05c57e7ff0dedf903778160d6603415472204f9c4a12e80c0151f545747d81a3202448c8080631c5c12e7fe09a9fc067e80a15ee01c5778061595ff437a8050591cc815671604b9fa43748020959fac36480105920000647c70d91ff81647fc0591fec0647f805b1c5412e7f40951fd82687f40971fcc3647f5097de0825b79b095dfc82537f104d037e85f05aa15e00c67f7ff19cdff447e7bb11c9fe836f7730da9fe43677f70d99fc034e7bb0d35cc01667ef04d9fb813471404b837686f058a19dc8413c71304b9c8013c7eb1a31f8c48c7df0631c7c13c7de05b1c7813c7e811f5f7847c7e20df1f984707dd01f1c7402c7e91631f8448c7dc0631f9c15471c04f1f94054,
    0x86a15be1a056b866159e18c56386111e217c46885d120217038085a11a216436870c0d0a18067f85e19ee16c67785819ce15c47a85611ca15446a8b895be30a56b887959e2be5638c20dbe2e036b8af0d9e21c3638840d7e20435b76ced5ddb1b5387c85be1e216e87485aa1f0167878059a1d0162854857caca15a86c855e18a15686c04fe18813e85404dcac813285104d1c5612e84f05f1ca413c843115212846a843119a12457a84215da108566847159600c37b7ea0dde14836b8500da613836776e0d85d0017484d059a13016472804f9c5212e81a159212816484805f1c5e12e13d20bc28882784919fa11c57680a0dfdf5c3738460d65cd01648450551c9c13e71684b84ec83f0a120de10c15483f0df60f437183409f20bc2708090d7df5835372604fa0fc48c8330a320a818c74d05b20f013683a04d20f058c82e06020e847c83205f20b417083d16320c428c82c0a020a418c74c05f20ec13683904d20dc26383604d1c4612e83204920d037c83309f60c427182e04da0b413482f11f20b037182a09f60a427182709be098263808097df5025384215fa05c57d,
    0x88986322241348aa05522a01448a605f22901448a911be29c46b8a5119e28c4638a205ba28437c7110d9226023888e04d225023488d04d224c12489704a227857289608e224823489d05fa27017c89004e22301347118d8617215d89705b226036e8960d9a25046289305ba2482668900d9a23446288e09ba23026688a15ae2245678ad19ee2ac67789911ea2804767160dfa27c36f8756daa26c36789a0d99c5034e8990d3625423a89108da16e16f2b585aa1c6167866859a11e15688f04ea22c13688804d1fc012e88695fa21857670b15b9c2e35587e85fe1ea17e87685ea1f817787a05da1d817288505521f7b7f879edfa1d7b7a87d6dde1e5b768756dc9c2e36670b0d3a1f617f87985fa1d617a87d05de1e417687505c9c2f95688304de20813470b64b9c3b98d88015f61fc37187e0d7e1f435b777ed5ddc9b5387b11f1c4dc7d717e5c5c3994b87a093e1e424b775e91ddc1a438770551c45956715e4ba1d835f8750d6ddcfb5776e6d4e1cc67f87219ee1c467787019ce1bc37e86e0dda1b436686b0991c90929869095219457d86709f1acca4686515fa190254,
    0x8ca61107a606f1e901ac6c60671b1018e36fd7e8db75da36e37e8db0dda3683541e881fc7a007b1b081dc6c00738c8e1623218548c880e23200346aa448635057d8d605c235057e8d3015236056f8d715ae3545678d2158e3401498ce057e3302608ca119a3242488cf116e33415b8cb055e32014f779650e4a656f93795ae376567911958e4ee36e93b0d9a34635693709be4a426b911099e3742638d9097e211a5b778e95dde1a538d108e479e06f1e701ac6a60671a9018c38285f13ea16c16e8570a3a14e31e0388c700d04f882f0e020ac28c82705b208e2b057470c0de5c4067e8c515ee2b65778c4159630037a7120d9630c16485e857cade15a872855e1a21568b40dd22843647150d922fc1647158d8630467f8b599ce30047e89911c9c483768be0dbe1d7b6a8bd0d9e2f03667100d3a26434d86085bcae616a873859e1aa166817855a2ec13a8ba04da2e41347bc04b9c3036185985762d868c8b206322d058c8b106322c61548b2117e2c445371419f62dc57d8b515be2cc5637160df62803628b005f216215f2b3856a1c2157863855a2b836488a04d22b038c,
    0x62a19e3340449271a3248c38c91f06024640809220db249458c91c915248438c9218d52470180916020245a05492211b2476344917811248c46f921118c39a84f061a11e47845491d0d5246205491f15be47056391500d24604549170d5008d85491400d245445f914114e46456f916158e34e35691300d237c67d92815f649856f924158e48037c8d28d5a40826291b05c246807c91201c039285f05fa15e32c03491009923b42548e6091239248c90e0a323ac2548e409123ae18090c095242824490809f241824490b11be42446b907119e41446390409ba40c27c8f609523a42448f309123c824490011fa3fc47c8ef09523a02448fd0db23d42748f815b23d02748fa05223c43648f8158a3c03668f111723c44508f511663d04518f30dba3c836c8f00d3a3ec56b8f9158e3dc45e8f609ba3bc2668e58df23b01708ed15ae3ac5678d68d5a3a426e8e8099a3941708e615ae3905678e3117e3884578d4919a38024490f19ee4346778d59199fc045e8de0dea40837690109be1d9a6a8fe099e3f02668ee09563a82548e709163842448df08fa37823d847851637047c,
    0x946158a51056a9431589ba6c6a94f15ae53856a5aa959a52c5636edb1a96d64669480daa5143527f12d42249a6a942094a5042506f195bdbc6d6b5be959da1e56395051aa54045a8916daa244b5a940459a5001566c5917db16c5b597915d8a64538df6d7dc51b5b817ed5def1b538df2d3dc50b4b817cd1def0b436ef917dbbec5b5bb915da164538de6d7e265b5b842ed5deedb538de2d3e264b4b842cd1deecb439c555ae70d5679c511ae70c4676d8917db62c5b5a8915d91e4539bf0dae6f03678dd6d7e21db5b824ed5ddfdb538dd2d3e21cb4b824cd1ddfcb4393d09aa6ac2669a5457e1d115a985455e5a91569a5053e1d014a985051e5a814695804fe54413e93f04dcc2413293e04ba4f412d8db093e219a4b77de91ddeda4390e15d2342038143a12c29684392a19fa4e857b90f95de4e45659380d9235e35693509e850685b0a4a14e33e03892509d240c2649330d724d0464932019233804492f0db03a685f064a15e4ac24493619fe49a6738d89199ef045e9350dfa37837293109be1dba6a930099e4b826692d09164b024492a08fa37823d817851439e86f,
    0x99305ba61816695904fa500136984116260c2598ed28f660024897d08d260034c97c08c25f423c97c0d1260423f97f08ee5f823797b08ce3b0b4c97a11c25e42718eb28f5b7ec6a977099a5d825c9720da25bc35497211b25b835096f0d725b84649730d7e5c435b9700d5e5b435397415f65b04706d4ed6a60856b978159db7ab5a97509ae5ac2678fc697e269a5b835e95def9a538ea28f6575166848c57259c14c5ba959a5a04668986daa0ffb66834cd5259c254848c91258836c95c09b258036095b09b258856a6ecb1aa5805626eab1aa57846195c15aa56c56296515ae59056a5ab959a58c5636eeb1a96de4668966daa0f7b669610d7a57c35282fcd12241a6a95d099a56825e92b2971bda56f6f6b5ad70a56768c958e255c6a841f19a254c5a841d15a23db6a9694d9a23cb5a9690d5a59916e959459a59815e959055a55c466809ed9a55824495415f5f5bb5695309f255556b952559e55446b952119dbce45f6f3b16d70245768a914e103b56840cd19a22562948459a51c36094409825283789460d8253434889469e250c26094c0922528561949097a51c56a,
    0x5b991926a14549a80d90a5a354833e99669d259833c91669c2395b8959a6a84669016dbe27db6b83eed9df15b63830cd566a43499a605ba64d16696604fa67846c99f0db1f11b7199d0db666c3618fb2d7669034999045d259413e94f04d9f0db6199605b1bf294496404fa5381368fa317253014489e6de66683618f92d7668434998f45d264414496304fa52c13699f115267834898d05d257015496204f267467a6ebb5ea63017695a051258413c944051251c13498a05d262c154960053250c14494604d266c67a99a19c9ba2d7a98805da57c14c942051266413694504d265016e987059a5041447f124d26584686fcb1616d2364831e99665425999409063d8a3d98e097662c25198d49b63d5a5d98a49863d1a5d98e15c263456898b15c262856098909f2648463991518a644461693918264145998f514664036e98f0d896ce35498c49be241a69988498e61d2618ef69760b3a5598c093e240a49988090e61c2418ef28f60b32359a315ae68856a5a9959a6805636e0b1a96ca4668fe6dbe26db6b838ed9df01b6399c0d7e23cb599980d4e65c3518ee2d360af345,
    0x978cdc6435b5f8ab6d6df4fb577d36d4e71017c978455a54813e977459a70815c6d7d17db5fc5b5a7d15d91b4536f095bdbc2d6b5bd959da1a5639c14d9a704356975459a5d41569c004d18874529744559b5734f6d5ed2d697347644cd0e6f957d9be11f5b4b45f6d2f16d68f457641d14e6f417c96b455a5ac1469bb0dbe6dd3639b405be6bc16390b64fe2a593b81ce4ddf45933909653e29d94b81ee51df3d94390764fe29593b820e4ddf359339b711be6d84639b305be6b8163905653e28d94b822e51df2d9439b44dbe6cd3639b409be6cc2636ca88fdb2aa3b59b88dd8e62336cc8d3db32b4b59d8d1d8ee3436ce88fdb3aa3b59f88dd8f62339af51be6b94639af0dbe6b83636d08d3db42b4b5a18d1d8fe3439ba4d7e6e535b9b84d5e6d53539ba097e6e425b9b8095e6d42536c888fdb22a3b59988dd8d62339b2057e6c415b9b0055e6b415390364fe28593b81ae4ddf1d93390324be28492b81ac49df1c9236c78d3db1eb4b5988d1d8ae343902693e281a4b819e91df19a4390228fe280a3b819c8ddf18a339ac05b0a5a16c9a805725a013e9a705ba655166,
    0x9df95f678437c9d88d5a760271924697e2cda5b7e4e95df91a539df08e67380709ce80d277456591f6d7a7702646aa0486479b5c9da119a471b6e9d9091273e0449db55be7615639db11be7604636c3917db0ec5b595915d89e45391b6d7a46cb4e9d5519588e3429d511b67340609c035f275947d9d4515675837d9d40d55b5a34f6d6ad2d69a3476458d0e73007061f88ce46993f7da64ce46892f7da248e744455919693e003a47918693673c356916697df97a5702500d27354559cd0d55afe34f6bfad2d62234761e8d0e74145f9ce514e74035f9ce0d4dafa34f6bead2d61e34761b8d0e73025f912693e033a4791228fe03323793e15b67a946d9e2517e7794539ea0db678835f9de0d4daf634f6bdad2d61a34761a8d0e75c2619d3097e6f0a53911693e2bda4b80be91df65a4391128fe2bca3b80bc8ddf64a339ab054a74806c9cb018040e84f07ca11c40e03f07c80dc51082f0a6209e72416c95704fa60d166910697e2b9a5b7d8e95df61a539c8119a43db6f8ad6dae01fb677d76d8e71c349982459a71814495504fa439a4f8ac692df57a477d5690e54a57d,
    0x9fc01127e856a9f9099a380a5c70595bdc16d6b5da959da825638bb6daa7fd3668bb2d6a7fc3569fb45ba7e11669fb057a7e01569f615967d42649f455be79ad639f411be79a463702917dc0ac5b5d8915da7a4539f0459a7c456a9f00da9ef4b509ef0941c1e56f707b5ad7725676a1958e7c946a9f2116a7b91669ee0559bee45f6fbb16d722457692914e4a9b5f7106d6e11fb577f06d4e4a8b4f7102d2e11f3477f02d0e87556f9e2b58e87446f9e2918dbfe45f6ffb16d73245769b914e86c36f9bf2d8e4a5b5f8b86d6e12fb577ed6d4e4a4b4f8b82d2e12f3477ed2d0e86826e93d098a84515f874a56a81d157a00455a84414f874852a81c147a00051a7dc13f9f304fa7b41373cf04ca7b012e93d04b441685f07ea15c41604f07e811c52883f0a920de7a146f9dfb18d8823429d609be6f8a63928693e2dda4b816e91dfb1a437e028c649da5f8b6696dfafa577eb694e7942697e3690679c6709dd09867440609e515f679027c9e915f27a047d9e6115676c2719e30966499a4f8b5692dfffa477ea690e740070925693e2d1a4b7e9e91dfa5a439e015f5f87b56,
    0x6f78d3dbdeb4b5c38d1da36343a1b29ae74ca67a1f09664dda4f8c2692e113a47804690e4dca3f8c228ee11323780428ce86816a152a12c2b684315280ec2b60330ea20ac1948239f495968133699366d7e305b5b803ed5e00db539e105928111569f404fa80d156a1c55968704656fed17dbfbc5b5cbd15da6b4539bd2592805156a010519bf634f6fdad2d7263476998d0e4d5a4f8c0692e127a477fd690e4d4a3f8c028ee1272377fd28ce6b01546aa9194a7216ca1705727f813ea1605ba835166a17515285c36429c8d52859259a1608e684d054a1300d2850248932697dfeda53a13017a7f002ea19119a4c5b6f8be6dae13bb677fa6d8e860349a1505ba8291669fb04fa848044a0e05b1b1a9449fa04fa7c4136a0b05ba8241669ef0511ef4934a0c09528384686c6b162834259a0b09058aa460a094986824241a1015a975e5669306dbe2f5b6b852ed9dfe5b638bb2d6683c351a0a05ba8201669f804fa7b8136a0611a2814269a031596808468a0415be78ed63a0109be704a6392e697e2f1a5b850e95dfdda539f9459a06315c9fd05327f84669fd0952063244,
    0x28915659c40d92882356a2009a64e9a5f8c5696e02ba5780a694e893239a25092689045b9c7b15e870a5b9d4295e4e5a4f8c4692e11ba47806690e888466a21091288156b9c8b59e88046b9c8919dbe645f6f9b16d71a457690914e7b056ea2651ae716c67a23515689836b9c58d9e88c355] 26 7) 6 11 7
def cert_trace := dagTraceF cert_mask cert_stock 12 cert_forest
set_option maxHeartbeats 0 in
def cert_sym0 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def cert_sym1 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78beeb6caeaa68df6d74cf2c709e69648e28607de75c6da6583ce34c2ca2485d65544d24501c61440c2040
  invFun := decodeRows 0xffef7cefae78beeb6caeaa68df6d74cf2c709e69648e28607de75c6da6583ce34c2ca2485d65544d24501c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def cert_sym2 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffeefaf7ce78df6cf2d74c70beeaeab6ca689e68e29648607de6da75c6585d64d25544503ce2ca34c2481c60c2144040
  invFun := decodeRows 0xffeefaf7ce78df6cf2d74c70beeaeab6ca689e68e29648607de6da75c6585d64d25544503ce2ca34c2481c60c2144040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def cert_sym3 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffeefaf7ce78beeaeab6ca68df6cf2d74c709e68e29648607de6da75c6583ce2ca34c2485d64d25544501c60c2144040
  invFun := decodeRows 0xffeefaf7ce78beeaeab6ca68df6cf2d74c709e68e29648607de6da75c6583ce2ca34c2485d64d25544501c60c2144040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def cert_sym4 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0x120941161908328b49369b10530d51571d18738f59779f821a29c31e398a3aabcb3ebb925b2dd35f3d9a7bafdb7fbf
  invFun := decodeRows 0x120941161908328b49369b10530d51571d18738f59779f821a29c31e398a3aabcb3ebb925b2dd35f3d9a7bafdb7fbf
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def cert_sym5 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0x120941161910530d51571d08328b49369b18738f59779f821a29c31e39925b2dd35f3d8a3aabcb3ebb9a7bafdb7fbf
  invFun := decodeRows 0x141120961908349328b69b10551530d71d18759738f79f821c31a29e398a3cb3aabebb925d35b2df3d9a7db7baffbf
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def cert_sym6 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0x141120961908349328b69b10551530d71d18759738f79f821c31a29e398a3cb3aabebb925d35b2df3d9a7db7baffbf
  invFun := decodeRows 0x120941161910530d51571d08328b49369b18738f59779f821a29c31e39925b2dd35f3d8a3aabcb3ebb9a7bafdb7fbf
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def cert_sym7 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0x141120961910551530d71d08349328b69b18759738f79f821c31a29e39925d35b2df3d8a3cb3aabebb9a7db7baffbf
  invFun := decodeRows 0x141120961910551530d71d08349328b69b18759738f79f821c31a29e39925d35b2df3d8a3cb3aabebb9a7db7baffbf
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel


private def axis12 : RowAction64 := maskedRow64
  0x0c0c0c0c0c0c0c0c 0x3030303030303030 0xc3c3c3c3c3c3c3c3 2
  (by unfold goodMaskLanes; decide +kernel)
private def axis34 : RowAction64 := maskedRow64
  0x0000ff000000ff00 0x00ff000000ff0000 0xff0000ffff0000ff 8
  (by unfold goodMaskLanes; decide +kernel)
private def flipSwap13 : RowAction64 := maskedRow64
  0x0033003300330033 0xcc00cc00cc00cc00 0x33cc33cc33cc33cc 10
  (by unfold goodMaskLanes; decide +kernel)
private def flipSwap24 : RowAction64 := maskedRow64
  0x00000f0f00000f0f 0xf0f00000f0f00000 0x0f0ff0f00f0ff0f0 20
  (by unfold goodMaskLanes; decide +kernel)
private def flip0 : RowAction64 := maskedRow64
  0x5555555555555555 0xaaaaaaaaaaaaaaaa 0 1 (by unfold goodMaskLanes; decide +kernel)
private def flip5 : RowAction64 := maskedRow64
  0x00000000ffffffff 0xffffffff00000000 0 32 (by unfold goodMaskLanes; decide +kernel)

private def reversePairs : RowAction64 := flipSwap13.comp (flipSwap24.comp (flip0.comp flip5))

def certifiedFastRows (i : Nat) : RowAction64 :=
  [RowAction64.id, axis34, axis12, axis12.comp axis34, reversePairs,
    axis34.comp reversePairs, axis12.comp reversePairs,
    axis12.comp (axis34.comp reversePairs)].getD i RowAction64.id

def certifiedPermutations (i : Nat) : Equiv.Perm (Fin 64) :=
  [cert_sym0, cert_sym1, cert_sym2, cert_sym3, cert_sym4, cert_sym5, cert_sym6, cert_sym7].getD i (Equiv.refl _)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
theorem certifiedFastRows_source : ∀ k : Fin 8, ∀ i : Fin 64,
    (certifiedFastRows k.val).source i = certifiedPermutations k.val i := by
  decide +kernel

def certifiedFastCanon (k w : Nat) : Nat := canonF fullMask ((certifiedFastRows k).apply w)

theorem certifiedFastCanon_eq (k : Fin 8) (w : Nat) :
    certifiedFastCanon k.val w = rowCanon (certifiedPermutations k.val) fullMask w :=
  (certifiedFastRows k.val).canon_eq (certifiedFastRows_source k) w

set_option maxHeartbeats 0 in
def cert_syms : List (TableSymmetry cert_mask cert_goal) := [
  ⟨(⟨cert_sym0, by decide +kernel⟩, certifiedFastCanon 0),
    fun w => certifiedFastCanon_eq (⟨0, by decide⟩ : Fin 8) w⟩,
  ⟨(⟨cert_sym1, by decide +kernel⟩, certifiedFastCanon 1),
    fun w => certifiedFastCanon_eq (⟨1, by decide⟩ : Fin 8) w⟩,
  ⟨(⟨cert_sym2, by decide +kernel⟩, certifiedFastCanon 2),
    fun w => certifiedFastCanon_eq (⟨2, by decide⟩ : Fin 8) w⟩,
  ⟨(⟨cert_sym3, by decide +kernel⟩, certifiedFastCanon 3),
    fun w => certifiedFastCanon_eq (⟨3, by decide⟩ : Fin 8) w⟩,
  ⟨(⟨cert_sym4, by decide +kernel⟩, certifiedFastCanon 4),
    fun w => certifiedFastCanon_eq (⟨4, by decide⟩ : Fin 8) w⟩,
  ⟨(⟨cert_sym5, by decide +kernel⟩, certifiedFastCanon 5),
    fun w => certifiedFastCanon_eq (⟨5, by decide⟩ : Fin 8) w⟩,
  ⟨(⟨cert_sym6, by decide +kernel⟩, certifiedFastCanon 6),
    fun w => certifiedFastCanon_eq (⟨6, by decide⟩ : Fin 8) w⟩,
  ⟨(⟨cert_sym7, by decide +kernel⟩, certifiedFastCanon 7),
    fun w => certifiedFastCanon_eq (⟨7, by decide⟩ : Fin 8) w⟩]
def cert_hint_pages : List (Nat × Nat × Nat) := [
  (0x2c30ac26a609eb66f2902632a8225f8673ddc3c68658e0609552a4f7d1ce44dcfc83cc4cb42f0ca421fec7ac1b345b812d433407140d4001c000, 14, 0x103011880808c28880c0d4e2a04614449862c0c426880008ca0335c2010232c0d4398911cad284c047416023a009c328ad5818a025a00c43688938f811beb0096c3e04a11d60235448102508e184859c583013860661d560c046b160404611d63604612ce0331aa445600046b170230a25162404e701a87112641544ac5850118470c5012849587120213809c3989125afa84c047416023a009c328ad5818a02549401385111a2a562c380b425ac58701684b0ceb162e04a14562c640d5602d0ca24ca1c062302031a40cd602511631d8020058198550ca20511be0c5012a40621b4e360627230350a6b0902108a30df0628094e0310dab082404701a8510e6214519274d27800233d3816845581819ac0527a703308a2acf50a090108470e624562c0808462a500d4299c600cc288a71c6b0303338b100230a61a562e4808560299808c4a8b1296b1f02358b0a0230a6b000230822d562404eb81a871593819ac74d8138415c0d4488cb40ab270255c0a5703111af9f0606af815873a0fa70350a619434e04b381486d9d28602308b4250210a62c5f2c3809c20ae052f830330aaf973e05215438be18a019ae600cc288837cba60330861a485be38085f4e06a14df347809df0297c0ac40ae06a345414066a814be0408570350e230d02be9c09570295c0c446aaa0e8e0270834012889080c55069c0942ad06009c288b318700027080a400237c0ac52d87c09570290d3812ce5050128430d381284b1523d4a9847c30128535c0d521c04a71202508ea8158c0809420270d2f980335c0943a9613e230e0213818a0250aa1cc61c06ac016b00561000330863040a04e481027096205716066154729b14c9a70350a69890234c0811845dc9926e04a12c3089522270806280942986b3c50129004e1b6d24042108025086c120606ac0128675549402d0aa08a03508a28c999a96070802b380cc3ada9c08ce0330d271f3a04e901986b6072d1804615439889202788021387001c06a10c3380380d4258d320abc4e0005672803108b3b70a042146712200a420ee06221674e1408422ce9d18108450d7b920210a241cfa9c000ac84e0467812c674095d4604a11c004000c480250c622c8096900701380052181aa4380ac0025409c20869387121804611c3089526340002128701885510a8cdf4e06af840a04ef815865102fb73e04215438aa20ea802d3809c8025102a814900040128410d64d40243809c002b00095502914219518046144a160621145a9738d3850804e10670251271b72adc09420875123288035940ad54a06a116d02994181a82280d422b001601a8450e23cd21c04a71202508f6016aa2c09c29aa056c01492100c018ce083018841a4601085320c8198451ea5142a04a124b5804a144569c3540150210a24165005a70139004a20550005212d42a06250b03108a24cba829d3840a04e10432ce05b3a71004211675ca00a4228671965d405004bb88021dc0af76e0400148410d7b8128a722a544110202930250821c4e1004a11c1029013820006210480251062accad005a0120213809c316062154002b04029180421543188950a81884d00501ad02c08e802d00581a84116239539ee55681a84338c8168453860e0270920150210960021e04aba93204a14439aa05630ca02921a70c1c04e12d81c38a81484b0cab818aea4c8128510e660e0272c0cd903110670109b51470802d09368a02d0876a80251528109c052401890a450128510e660119152972ad031952a90330a21d454a0667013861b5281ad0b409c2488b949010d00632a56a06214e55aa009c2486b1aba8119454870129c480942398380d42080b4096d0004a11d702915a62d0004ab950210a6ba93204a14c388f5300a495b204670806066b8188a200b4e027044813801809c2488b1c240a1606214c329b5381818ae280c4229c2c0d41000523830406211c369604a30489fe),
  (0x1face97f06b69b8d0b71d34a79f272893c1f9eaeeae6d5b2e9672a5a43fa1090768223e99f30f8a72e2cd9218772346169898034a000, 13, 0x7428e027082e9d3604612438ba74a01185574c011851166e9e5206610c32406212456ba5808cb02d000a445ba7450168497540b0210a61c5d5005ab2802709222ca2a052b8e0330a2e8002108e30d02ba1870502708ae818ac0c5012853089019ae04a1c46a943601920312858188451122b562c5800149c04a71602508e2d46186280940242c0942987115b416035580cee2c04341d02109222c50005628188a600c4298a338e96023580a4358870c01e023480cc3888d38e8a0350a6b0a02b280b43394000950350a61a441aea0e8b03508340b02d0862cc68a0578f013a04e105e025116f034e04a12c39bc000ac24d6788019c005a1d5b4e280b42a8651470138004a184a1bc600a5602ba009572e7890118470c225488ac9cb81884358b1d0204e10432ac0d38128535c0c44a90b784862006615564006612c51ac0808d703558b920330861ac68bc6cc0a02b0aa18ce0a04eb81a8711ca9a450605a90188a3809c3033487013851156705027280cd71c38901384b0e624472a64c18168554c98a02d0aa1953262c0a426a64d401984d0ca345f0e05af93025086f8b02d4cf81284310e42d3062809550310da98402724181a8530008a0350a6195304480cd7160661144a8b1306a930234c0a435888cd8503360b8188451062ad8062c0c590250d223552a1008422b06808431404a14c4a88600b5502bb0101a8435c09552a4808cb0250ea24ca8a64c581584d4c9ac02b09a1963062c0c590250da22532a0429940350a698a03308a9932a05212db0235c0955268c08cb0350ca24c98b44c9820235c09438a614c8128430e698b02b09a4d5a062c0c590250da2253342c0b425a60c5818b204a1b444a64820138004a18490204a18a0250aa24d30406ac120350a601716066154328f13c69930606a14d3269c0d4298654c4811a60408c22ae4c58128410ea3c532668084f0290d69842a05610433a60c0ad3029ac801a8431669934e06a14c0369c0d42986318b3a91404a10c36a65c9822406610d70251022d46882240aef1804e14ff12040d6f029c0c42a923c0c422fefc9130274c781384b3c094902904c81aa404e1cc11204e1819a44c0acf5e05611e702d15248f0290809302909619c44e06a14c72ce3c0953021bcc01aa6bc58108550ca2cc88882408c436046115704082153404e12c308851663458062809429ae60b8128410e2354e28a5401285154b812a80621cc64a8a14812d2a00942388915b42e02d387190310aa1cce4a056105a5ea40c68025080940350a21cc619ca0095202b10b812aa280ac28893689152e04a14c31b43809ef2e05a0012d264094298b51e271202338b812853380150330861c4e24540cc65206614444a44c0c571c640d42887314a52cb244c3013849a40c449ae640c4228ed),
  (0x22fa87060e27fc5e94732dbfe6bed90e610572c54fd4604bc51b8404cf7c387cdac2f44aaa284c8a41cd462015dc3c00e0c334099c1be0454000, 14, 0x22460601a8430e6d8302700581a8530400158411a201714062701987510ab922a046701286911a9291c500d429aa9c0a4228a354001484b6c9180230a6a1703508a2c52064809c26d26c0c672e062115b20056c018a8640d4228b3246d8002b092700031a4b8188a1009c2033044813a8066001488b1c33891c0522810005212c338a15c0c472846409421a55600120213809c0025409c208695c0ac789c500cc00210cab940604738a02308a245703360d8018046001886b126b943006212436ae04a484faa038c015ae05aa9a2c04f481186b1123cce24280c570330d621581c08b8128550e27031404a1558306892c02908eb81aaa6809c258c11ca444b9a438801a80800c425b0480ad81606aa820e052135802b54d816ac05619c709312e67bd8245408138490c25974e06210c3a9c0409d738062154e033156614e36052d872404e12436b00c0b5b20a40cd714062114418a91d671b0454084228204e224204a570138410ca22d8040632120310a600a0335c0c4328f504c019b054080023093201388114ad9802b010018b804a90b3604e144e02512739003160d8b0270a21cd74e062114749c342ab921c480d4239c04a22456b06cb81285148b01a9c9c0c415206211693204a15461aa600a425953487013829c08c25a4613818d206618c4a82580d5b0310d270102ba40270335c0c43a883389019b6b809c2888928ac0e529c0942ab004624e70a1009c11204e12c40d2102813920409c2588114ab982e04a14c3a9b138c019ae0c0c570330eac0c0236cc0158515cc01484d182c0e2404ea81027092205703539381ab05c0d42989160b8a0310861acd28038a81580a40a426ae04a2cc152380842a871554180330a270004a40cd732066114418ad1aaa98023096c151c04ec1716066154388a30c5012960621b494805c0cce520567013d2380842a8b1380010215409c35d000084229c0c501284b0e619902509ac1702d60b8159c04e18c54ae600cd726600a420b05cb800215c09433b00562cc669352e260e02738c031606214d50271162a43302c0ccc02b0e2234e18540a425b2066b8e0330a23141520520970350a631702d0009691c04214c58a45c0a4e0270409552a0408422871601018805c0c422aa5c08c24865d197029540ac10271022c592e062114899d560c0b02b092a830350a600e2404ec81a87310a6003004e90e0272c0cc34982c0ccc0215409c45ae2c0cc22975322a98031dc1819ee05bb92021dc09c38d2047b9202129b816ee0621cc5299554c01484b040018d25c0c69033494970290a6a980290962848aae55401685160181aa43809c28ae05ac0a035a071b0354809c3089118a5cd53006a12d500056c141606215775206612d73206611471929809176405a1543890bd401984bb1481a85100a830350a7a012b05c0d428a43809d2029380013851540ac60aa4809581c48a81484b0ca18a0250a6b8c0210a245582a0c0d4e2404fb01a865166c1703548a815841122a9803138a815a404e195706066b8b2406610572a600a4258671a2b991606214c32975),
  (0x2bb2a99e8e69cbe58a8e760c67bf5d7c707d9b45c05622555540a4c651f24134f3839acd682deca78261c926208c6b414844300cb41e203c4000, 14, 0xe30a4c8128490db7930272408d35e04e08118656018a0250a77930270808d20335c70198451a24d4f5a40808d802b48181a8515c501884548a81025600c431b00567121c040ac28a40809c26a43008d80310d2404e0252aa7cce520448139c052184000480cc2a8711d67282e0625280310a6481027380cce02910242c92d0a409c20235c09541404a90e0250a224c869c000ad204046b8128628094288a950501284d007012a04e901286910290c0233870102998901484d00701684b1823c4e0252aa7cd5507c095f5004a11c46842009421be380c543e04e12e82e06211450005670129c1400158450ce304c4aa500d5f2a06a14552a280d6816042144448a5266c1502154901085150a814aa2ca8148510e62d402806aa81486b3871802b500c551698085802b0e224c7aaa08a81984354601184154a831606610c3589125289d52e280c42ab05009c25d0066a8b035082a9402d5c5018843112615830b1481ac6280d422893152284025102812847102717025600b635804b62302508e10802508632d516042a814aa5458108450cec0168f3422715033540ad8045460138530c622572a2c0842986560a8e2404e115503310218b04540ad80290c224ca160661147a99154717025000ac34a82809428aa00581a966c08550290da2c5500046a016d000084248ab55401896042194e982000c6e520548168510cf4819d2500ae91c000ae90330e221c649751408002909670138200a01584d000a449901080019843a120a03590a01484b126ba80335c08c389c1458158472c0cc40985380814800561011b0066a812805a15401804612c50aa009010853540ace027600a54166c08429a86009c25a80c08ee1604614c1021540b4649754632171406215554804e12402806212e80335c501884300581a84130aa8e00066146620a40cd71406211441aa0c0b425a42c096602b0d2554e2a056115033086a80031a5a8129c0621d6652a0094218612121182a480ac208735418b0330aa92602b540a4308d100a818ae280c4e0210ea2957245c70188450d2234e2a052c0189c3cb01384b4148198435c0b553005612551406258198652ea92c30a40cc2a863580ad2468da8198550c738158a5381011aa740ac29aeb848158490ca3c5204540120350921cd828400a4b0336c11d02b08eb816b00522848a93135e11502b90c120210a3aac0330aa28d71c9c08c2886928a1150336ca0b0330aa9010aa0008db0290d6b8702909a4c5528062b8b140461443a8a5047000330a2d9052066b8a03108a20c5aae05a90e025980ac349c6cb81284d6c181684b980a690406341703108a080031a4d816b204a1d4599236cd8702909ad9b0605a1243384600cd52806a0120212cd81085512634641406b40198652c68124c2cd8108490e224d21c04e701a86d38ba7031086194b59c4809e71e04e001286954001484b98f810cc04ae98031a40b633206a1145990304c0119c080ad70250e2a8e1e9c09c24c6046214324062c8e02108a254999c4809d502b6cb150250a618db2005b91c02d08a0170350a290e027480c4e025040ae71e04e00158004a22490ce3c094f4e04a11c60004a7018920409520350e630ce529c09572e480cc2387115632694e04ab972406611c388ad4891202000c4218651129153006210d202510eb834e2808c22871380cd21c6c0ac28ae05a90c02349301585111270129213aa71003578d013aa000a425aaa40d421ae480a4269130090a0312c0cc3a885381016aa05612c3404e00158004a20454a60c0d580318cc81a8454870128411e67000335400128413808118005e1ac22e04a18a0250a259218046a8002b0a2b9202909a304e025226654e36052d872404e12436a048501884500da90230c0b4b02512a2cc002925670002b3810188205212e5204e00148004a20455c8480c591c04211449995),
  (0x20ba7dbddee731dc30705dc106fddb606d65b526aa59dc60956ec551d51c537d3ee472d0b63cd4cdc28ec9021d2c62416c44660ef42180454000, 14, 0x13480629922604a13532a06a14550231a699502d0972142a081818a40661d4439e500c4e0330ca40c94a0600acf2604211532806a145326600d428a44c0953345409d30354c094448b108a01484d242798035480a4e02510684d3284820129e600d428893146a1a2a04e10540254c9010a604a7980350a22cd402d3c0acb48854c01484b0c0c52300627151c06a12c328b3201018fe20101890080c4e3a052a18031096b1402b380d4338f3fdf942c5009d42c04e12e40405690138691e241903308b2144806612450405aa320350a628b2e04613432c8500a42593114a015c8062a140a05aa818875747013a804aa01a906c095b0a04a11c469013272143c0c0c552406a14c43ae140cd90315009c42923292f1002dc4f01485178c81184578089027082f012a805281462500b42a87150c1402d0a21947998b78a18025600b435bc600ad43006610c43a890a81384150095e36aca0158470c2f0502308aa182805660e02508624c58975500b504aa0409c902b540950270925812bcc009412a04aa8102508ea014ae05a34452806aa3328042b81287512234c528787013841500954485409c20a804ab14031096324aaa878a010851602980316d5813ae056184548d550b01a8a04381402b600d4388c550a120276409431b00562b5498a54c01484b0c0c52305409520350d64020270c0a411204e00602709222d902520264d22a052f9f2e04611435a4540a5f04046f81286b14f2018be7c901a8510e690f3604e135f2804612df0c0461164029202902023b43010a40661aed1c042a0602508623561c180cc2a80b40d422825409550204a11c40a4b4b8108530d618169a949803023c00ad902512a90e0275c0a6d02b4890302108e1d47999138910060461443aa40808d20270d2802060623014865116a960c04214660404610002b7ca01884310e315202908a0118c6808425ae05a11502b08e90302d092b0602108a9123204211d2240c0842386d1a28d5b9a05408c2025900c5f3e540d428873487013bc6809c202d0eaf812be506018b204a18c45c80525864243809df0257c0ad5029142f851e04e105502b7c09552e056f8128697d2140237c30118451022b573e056f95027092aa40210aa34539aa480946031483019aa180a460330d628402704a81384b201013860521b46025202c8189d54078129e400d429a8c480108550e27943006610d43004e901686b51215027082a0129e695813a8056184f100461154240661448aa805a6a642040205027082195402b1532019a8c480108550e241402b900c54243c09c20a8056a01290149812a61409423881540c5402b1eaa8169b390a102a4060188550e621c83206211471909549012901420138605a089027003013849116401290126ac122a05611590351229153005212d52404a181a8736091502b08a6030404a18100052181986510e3047a951),
  (0x2600963648a8d4610a7fd5f3a7535cb66c8da9e611579c550d3f84d8527045b50a03c7cdd434acc162a0c9a4211c65a167c49c0c6c24e052c000, 14, 0x90b170350a2b1d033082a0e02509ab170404e14562a046b1f02308a181ab058b1d3604e12c30a8046701a8c51e264df48587013841900a64025166f860237cd1e0277c0a5f02b102a0118c55d2180235c094308953223002a056114023092216c2e053201abe0c0d4302d640a4428f340f819ac180cc60293848158405219c609c400a6c02b083019ac7410148530c320158c75008ca2ae7c18198410eaac461c0c0d4298c380d5802d600ac20006610c6081409c90204e12c40ae2c0cc2a8e53629932006a14d31204698102308bb82023dc581184512a44421c48a811849500d4499e38924023092c81a89314a7083e7409c2086b3968159c0c0842a8935008ed20046c0109c066224f10042a0e021380d4398a54a27102024081390052194408b551b900210aa1c421e04aa0e0210a67080295080119e04a1ad41c06a14ce485409d40258ce812ba8c094238951d2a0018066b81286311660538be408040a04e10432be057b900210a23d65107498138410eaa016a8056a121c04e105402b505818a8540c42689522729458200b42887340a0368062155502d12628d5021293288023500ce44a06a4010a8a00d429a85c08c258f128b1900a1009c20a004a24e36e0808f7160461144a8b194401aca056aa503508aa016da4040128430d290e025389012847500b5502b6030802508e1a490ca500d5402990c81ac8500a425885b4a012c80432014aab05811d805a181088516a4c509aa500b482c4c09c20a805622651004211552806aa1503550a810d8500a5402d0ea2ae828042114989734080f0a8c0ac2386110b2019a8dc80108550e24144804214e42e06a91402d3809e402950a0c0230a61ad42e06a11490971384030335c2840270c0b430ae04ab811204e00602709220570250c0b4759913aa7170250c0c4e16081812860520800292c0b430251163848a93338a015a8066a9403338117025086a01988b1927010a4380cd2485409d20350d270e02052156602d50c81184b18a504c8a4500cd402b90c022e04aa0198751062a642a06aa121c04ea814873540ae43605aa015b2046214909715c18199c5c0b5502930a143c4c09c248651022ac889c500ce41c04a1041063809426b06409422406ab81287314644542e05691702309a224e1c90a81384938094409c50c013a405270128811567182a04a1243035126917033487010296408c01c066b81486b18a38498a00c0b6402538d815b605a1819cc0c0b424b064a0b0350a6194419516c90e027082d816a85408c259c900bd22005eb812b05009540350e6a9403339201284748c8128551a260ce49c5408ce48046114e1c6008c299c5008c228b160a81284b488015ae04a9018a438c811b6980a4258405a29460a00c08d9025380c521c2c08c238611e68d4e36056d8303309aa8002b09210303360c9703308a1c451a43809c224062d8002b5cc81884310aa0048000ac20a804a90e0250aa344799af40c015ae5008422a8066a920255090e027500ad4025102a242a04e10540251124cd8306c1016a8056c81188514235518c8380814b074f814a604e184458c55c0b522804a19803108624d21c04ea242a04e7014a804ac0158a104a016a85c0a425a46409570330c63c4d7a8487013c85409c24881500cd402550b81484b549012ae5008429b060a1902304b81584910a2846a951),
  (0x2246862e0be7e5df007885ce870b5b72689d8825a9d5c8550d37a49950423e1cede37b4d202d5ca0c25d483c1e0467e148438e0b041be025c000, 14, 0xe0405aa8e025092c0b02d5c19a2c04e10430251222a475b0381170250aa1c4e0606ac0234540ae03405611c428a11a244ce02046718033609154804e1243088519e0030335c08c32a600ad724052134e0251423449a9c600ad702d5c1818c86da0118604a1ac408c9607240350a61021c540a7402b812014847142314230066b8128752a21240316059836062c01586112a2cd82a04a0118499009c40ae0c0c42a8e55c90e2406211c3488d4890e2006211c16806211451aa056c030335c181685112ac0e4804614d202400cf40250c60814ae60b8128410ea44582e062710031142013822409c2588139a018881409c90204e12c408c551a0202308ac170270a22d5199c60c0e2404e10432b0062c182a9009c208651124cd728042a190250a2b9736042b8128695cc010ae04a1ac799755cc170250921b5d2806a28e027082a1d36046e950230a625458ba500d575006614442ba5008d40290d6a1416052145e06480c42986350a280290a2b99033086294b6ba1870502708ae818ac0c0cc224066b81287116a48c3300c0ac2886d58a1b1004aa819871106a141606212436c85870138419009640a500ace02750094408a950281a8aa00cc22a8789019ae04a18c46c85008c25a838d950330861d5402b5d40198451d28c5e56046f1b02308aa0548500a4259c740ac23a804a3047aa85ca120235c09430895162b102c5c0d4229c1409c208a358b1d4804e10432ac0c0cd706042b81387116a4ade2c24a01a8530c6b0202378b819855122f1b009c0cd902b0ea20ce0a04eb81a87120a82451c04a70502508e1819a43809d71c4858168470e621468a84cf9f26046115f26046f812867196a0b02909a4c5328540c426aa4c0c5408042a01284480cd70250e235481aa4c08d30290d7020462c0a42886d8cd950330869a00338cb81185110b001690bb0a810de680ad40330ea9840270c0b5502b51184021640d43988320b6042604e155502b50d81a84056a81988390bac0335c08c3a885600b4d8a850a81084b5009d3262c0a426b6540cc21a64d401484d4d19703508e18c62a6a008d402d540a4459f15101a02968095a40680a42286750581484d22321a26052200025086205a2605299b2a066155310a00cc23865186a0224066b8128632c0a4569b1508131606aa8118733c9a0027a00d43988551b81484d2a29ab0234cd8118455021a2a04e781486b50094508d54cb97264808c2386112a2c6f40400c5016800b428b004624c6ac041b81884d4d781384b15211a02b24b81484710300f26bc0d42987110a2093604a10ef263c0ac24a804aa190250a6355020080cc20270c27822a04212c40230901a02b480a43088720ab930210aa74440c04620002308a1819880808ce2a04614c402046b81a8651e2b152c05212df0c50094e0606a14c230066a1703508a244849230cc0302b0a21b5f483808429ac7c0a5f0406ad814ae04ab0e0350a6c141606a114309235872402b0a61b4e8c81808640c2c0d4219c5c0958033180ac448f1),
  (0x1e68e2bef0360b9dec40ded2e175aea67ce5a5272208b2c261fdee926f4b5019e2c48563a5a915e7d03669890ad24661cc8b783da000, 13, 0x38a819aa056b9503308ac180604211c22a066a813ae04a20c74b054712027540cc32881501812865009429840c095502b0c23d58300c0d421b004ec1902308a32528a8b0701ac6b009c24c65c0d422a8540a42691154a1b2a056a01286112271702554a010853500ad40311932050804e106402590a01484b9010003308721702308a717025500ad46806b40128731925c4e30066a015aea00cc22c8487013b606aa012802c0b4258c11e320230066a01898040c420ae640c4228e3212a952e04e15662a05692602b092a3402148a019b206a1945193148a9f2804aa01987598b81a851186a94025980a43584600ce802554a01a85198914025086a9b3a04aa8138750c0b454901998970250c0c43acc38094e02d0c23ace2a052c018ae1c0b431c540a632c04e12c3025142b8302909a444aab0500a6023096196c2806ba1602b08a28f0253c281284710244ce04046a9d02b0a6bae02908a34522a066c1524040cc228611221170250c0c4e1608a815b0052184e02515e34c9aa4500d4258540d429c65c0d4228b138d816aa056d8302d0921150336ca01aac500942089118720e28066145706062db40235c0b4302510235521c04b301586938d815cc053a240339009431cc5c0d521c04a10448b6900a4248062c14206c0d420871a0094598e3409144c04214439a4380d4e0270da7174e062701986310a5ad52806a0170350a271502b4000159e04e1a54025182a8f4004f181186504c011860661d572a0c0b42987154d811a454a0168510e72002e06a14524805680002b3c09c34a8380b4228e1390180233c8019b004619c5a9c3d0013e80660020330862d4629c4078129e400942388b2408128435c9019ae04e1d4a8a45408d2480461152246008c24a45008c228b15c80302364094389c06691b4c05212d724052134e0251825d4e2a056b816aa5c0d54031ad68138605ba0118604a28484843901a02754001484b000c400251aa384e2806a00e2404e154388b33808119c000cd728062154024066a8002b5c181484d12230542e0c0c42a86535e71b02b5c0b640005612582e04b23402150094388a3507206804e12c30a804ad8002b09200224066b81287512211230300d42187390a01982000ac2089150b830310aa1957243890188470d223522ad08012a80661d441aa000a42582500cd7242c0942087516291402dd08012c8066d98285c0d42287312238c100056124e28142013841500954022409c20a804aa0148ab26aa17280008c20875122a17283008d70250c2254e28492014a8056a012881166a1b0005610542e0661145a9c500cd4035500a4e2a052a01286150a1703308a1aca3ae500a426af1),
  (0x216e835de2473adba06e65b5c6d55b186a4d8945bbd6e8567539e4dcd3364a7d20844150383854da233e4bd22a1c9061d8465e11c436e0574000, 14, 0x14e9c7854605611c3288116a0312e04a15438aa609001e04211c38aa05798002108a3cc8244c09531004a11c40aa05a18a02554a9702108e1c459b005665551005aa818e40009425aa200b5503101901284b14f3820006210480256150c0310aaa016b204a2cc91a69549012b048a8158450e24030335c0c4832066115202000a425aa10c0158490ce6019ae04a404daaa600c6a24a80b428aa600a425d4555016b005218449d41008525405a145554066c01486b5c08c82a35fcb832e06214ca027c890850052501886d55417025640cc36a464b81084d600ac44aa48c014d0000842289348a814aa0669150204612438a4540a42391554b810aa04f4014b20622b5800052117025540cd53200c0139605a581489316a3449196b48c018d4c55019851a98818d4066c2a0330922ac42a600a428da400ac268a1a8201084a80b428d4080c6a033600a445ae0464956aaa30a970290974152405210432ae06291902b48c015e64c084228916569702b08351702b086b8148cd326b98021609810b06000108470d6b8168d348c015ae05ac814a4000810aa04e1a5702ba0001084560b816ae5ca9002d08219c44ae60b8002709218445955466ac522e056c8198a54c014853a80b5200056c8168208b812ae062c190350a628c64a45ca810ae600842488b48c15025096c81a89348a980295c09435a430b81084d0e6c982a04a5950210aa918021092c8168f322399703104c81ae6389012847ccb81484d54b816e60521ac889535ca810a43809c10255c0a552a8c08550250d6a8e02056105502910e454c9aa600cd802b64b920215c095702042b8128671a63d5530056124c8ae5c8010ae04a19d802b15ac25033952990350a61c580216408d21c04a71202508eb95021600a593006214c55b205a90e02754c01484b5c09590315471202708a601ab006271802b48a8158515cc81884d1825cd22a600a425862809428aa480947035040014842c0a4268e04a285824540ac229830381484d0ea344e9b038c016c04c09c20235c094458d1809813920469a00270408c32b006a714035380c4e68380c42ae8380c4268a52127cd22408a81986380cc2888790a018ae640c42a88524618e040427012a438094248b319ac1706062701021380b4e0251263558029216a011204e10582805a14421806610d42ea070168530e2214e28380c426a805622541c04290e2e380cc248655010c0335c0943188b22a912485409c20a404a224e02b507261c04a13541c05a12c50a8049016a405618541c066114649954a2a050213809d40404613542e06211552805212d52806aa1502b54581385512234ce30066a015aa487013841500ad44c042a0b02d09625488aea00cd52806a14442aa6008d402b5008002b0821c55280808d5033500c4458a754a010ae640c4218853d2c1502138b812b005b1ac025b118128470840128431964c6c2806ba1502b08aa8188a1009440a04a11c40933),
  (0x3302c40eebcb69ec5cab6e9fca1ee6fa998e50690e631287f5fda7a85c9068058025add60e4fad33044c4f5633acbe8236c7b414dc3800bec000, 14, 0x2a2a500d4298a04001484b10a8158471429270352808c42a0562810005212c338a120a11803360c020250821b6730052c01984600a582805ac01387314a42cd8ce600ad7300421155280c08c2aa49c0d4a0230ca3458365c101384d000ac4080487013825409c248815c0ad80351e2a0002160b940210a2c170404214433b0000a590230d64d4b2af3487013aa052b880e05214436a05c5018845600cd33a7c0a4c0310ce38e03108a304a5ac94301884760094e2e05b215031092e001c06614432b65c0c5702570e812ba700942380052284859f504a813800121203308ec81288315a01802709601803338085462066c0108715cc019ce5c0cc28885487013ae05e1acd4a43809c1029600800299d5018a8600c429f0640cc228c322a4ad702d5cc010aa500d521406a115702d1675053605621502b08e2058033cc21502b1408002909619c50a85c0d4299055c0b4f8ae487013825409c248815c09402e05212d50606a90a03508a24580004b816ae0561a440ae6008428b05c58118510ca54c038066e021004a10dc0205212c002d540cc78805418a0250aa1cc51c04e28148004aa8158a1140016aa080d570250c6a98029096c15003808c228611265c563c06399e03108ae333c5408de5c04611444b8300a4258f1226f053c04e1012d60c0d580318cc81a84516640de025409de025600a440869c09580310e642d63c062e1c12047981a8711279b803170e2e0230a2e1c1605214435b205a3cc9290042c1e04046f015800622812a04ec01486b102455602de0001084559c0168a280b4228a0c0b567005a11443862809580290d75944005a155b1406a11451b06040108470e29cd5300c0cd824052282023300cd50291163448a8a00401884314a815849600b4502046c81a87324a9920214c201084754a01aa6a808c26a60c0b4248d34c0011a64c90118470e650168c54cc130210a699b0352009421e04a135830380b4228732065c5530046981486b4c90402708299a2a04e104f02911698302b4c0a6b2006a10c59a64d381a85300da70350a618c62cea850128430db393029600b4f100467930210962158303808422b0052c0e02109ac1826042114339334227ab0234c0c4f46046114f1e4820138410c67940230a67aa3006210c349e5cc8148430ca654f345409cf0254c0a44086600c5302928c0e0214c0a4388851e662d5300c0cd20810a81484b600b443980663448a8810a81484b600b4a1c06214d224640a425b205a21ca2ba0d9b10230a2e331c042b81187110a3b5f6605a12d22a046f814be181018a8600c42988348f9b0230a2fa40230a62a4a5a4540a5f285c0c5f3206a14c41be0408423be3c70198430d252cc28670095f244870108470e624466bc78b812ae04e18de345409de0250c219c025cc0c4398eb4890202308eb9f0215409ed1c04211454da18085e0c04240128631569062a18d0108470ca2243382808dc02b0ca25562406a9015a400901a84938084428f1426b1c2c06211f3380679a702909b98303309600118a680ac42a05611c40cecc0cc289b5cce163806a11c39b85809f302d09981984b5c08ce0211e259560004a9014aa08f811845480a5c2828094218670094258b50ce012ce0521b4c9a4583012853498816e2056b9203308a2d420c0461012a4052d0902518d0128471169121c6408c2986512a60548be7c181abe0561cf33e9c0d4298650d3812ce0521b674a5c08c22e694084298b17c90e027082f814be0c0cc2abec4a8148550e2a9f0406215553e04e125f3e68f013aa0521c440ce540c42a8f330af86280663150350a220e73e9008c298697cf943206615431be0408423be5c08c24905416fa70259c0a5f2a5410108470e624476be7c181abe0561cf33e280d5f02b0e621733e04ab813ae05223423e057c012e6b4084298b108f953e05611c34be4870138417c0a5f0c04e12c68be0cf8158559008df2a06a14469be3c48148a040a423881b4f81094540c4298957cb8a0290861acc2ae54aad02108e1c5f28300c590250c622486aa18181985518901ab005a1c4606066a98033181011980661a4588eb1890a0350a6a9802d60201084948c016b00408425ae04629c989855878129e9c0d429acc47010e204e1d4489e600a4f1e5408424863c0b4299e700cc228f53c79a029082781021480d4399e380cc229e3c7920330aa1a4f2aac90198550d278128a124e8c5828052e0e03108a20d23006a7800213c78202108619cf5404690188733c419033086194b49ab),
  (0x28649f7e52c929e302891e19e84f6112803df1e7795cac6cad8f65dd552e50f52f245c50c83e84d4831a4b8a25547c2179c3fa0c24218037c000, 14, 0x813812ce06302d5004a12ea4e04215459bc38094e3c04a11c51c04f3812861787013ce04b39e0215c0cc388d55d3813800673970330a22ac04e6c08675604338158679c50118451eb3a72e06a14c12a04f3920230aa20674e5c0cc2ace056c8118a5322a25702d580012ce06302702b80096a3c04215459ce147013825409c24b0056b8168c19c7050275408138495c501985518239561c04a71602508f39e0210aac1824046b812875126545604052f1c02700094002b540011849640d479846408c26aa70f013845540cc03006210d60405a11903308625552c000ac202d0eaa1902d086f1b0335c08c53804ae0502508e0814800561170310809c040300c590250ea24c71846408c26bc0809450215c50168517870129c7809423b25c1170275c0a43888116a4cd724052c8100052104359c64101084d644860290821ac639c640b453205a11d714066c81886b1ca28e02538281284714b8169c04e58199a300c410005212c206052581586d1c2b990312c0cc329d5580810b8062a9602d08aa9602d70081084510e10802508671802b09271403538501a84560a0e03508ac0e02d08e2c499a439301684148095802354c0102160094e02d1262a581c3811203308619ce2e04690198651d242ce280c08c2a9c700d4a0230ca712025409d20350d2204e1c2c08c2586522674725404e1011a8540c429d40008720275c08c42aa1c0b425a4c82010845a82010a404a19d528280942ab006224d802b2d2a98240070108470e2a815a800084228f348a0a0250a2c015aa6c085802b5409580311664d55000808c02e04611540628094218711d6c1500540c425826408c2296500c4268e122682570628094289c5c0b5802b0499e02709750118e04a5816aa38094289092e671b023500b642405a11502908f9985405211de023116b1302b7009d503512664521c5cc8168430ea2141005410199cc00c520330ea29dc2e640d42886524601702b092a8e029505012ae0661c4e2664094219c480c4238a129a70002b040a5e7004ac2a2a06212d902512630d702d38c1502579c012d470094e0310e62d411204a48102508e006025180012847112404f5ae05a70e06062b8e2406a11c39b204a30ce006009c209c04a19c0250a2b920004290129c4809c288b51a662ce30480d429865c0cc28825409ce02d5c0ad20311427152406a14dc2e066144529e938d816aa056a980319882a033a40c7232062114518d52c381884d29270e54080c722e0621144a8a3540ad530062a1503138c81184512a34ce3605ad8b02d09271b02d6c0a433cc056718033083930210a61d732e480cc27865206a942005e15411406a11520205330159c04e901ad0380bce1c50581a8430da2046297342249b54040adc0270c225405c04611533606ac019aa4cd8108530ca3440060568310315ce0e0310a6194518ed487013800561a6a3804ae2a02508e300025480c4319c60a812840621a4458405a72a0351008d52406a9015aa046245c14046e2a027380d4e02b04101a8431a2414f99c38a980310861cce025387010006210c3288760a81284b493815ae04a90199c6d301484b5c101384d4809460867050118454870b023380a4328931e28d4e3605aa8b0e06213434a070095b0605a0014d4600c472e062114418f3256900031381018aa05211c3a04e00148004a20455c82809521c04a1444999508c019b60c9019b204a1d448b6000ad31c480d428a8640d4228a31c2d8302b389013aa0461a4569c38181384d6d5015b6600cc28ce080c543206a14c429036c0015849),
  (0x251693f64788bde2968a3e28888e611283e5fe478fdc526b8d91a57ed52e491518a453502639bcd2430cc9ec208c79e194c5740fcc2de0574000, 14, 0x142e04e12402b50a1502508e69402d64094398c998f04027000acd2805a15459a8cc09c01606a14c60004f40168631cad9e120409d70310ca02018062155902512640c94bc800cdf2a06aa2f027096224618040018c605a48603108ef183c7c09428825409d80250ea326030800d42386b7900198078c01a853a9781084716238de3006af1e025409c2a80ad1813851000d4428e901001a84b78f180290a3514021a809c398c3780890252408128470810502508e0060251800128471163a4b0ae062f0e02538f012847641810b204ec991a04211d702d1123d4b9bc08084e0454084248460084258a5387020310a62820204212420004212c529075cc8189a30a0158515c101384d6c1816843008c20310d62a570252c26d451c04e0170290c08c36821800118490d601f3206a14c32820808c51c04eb8128c05622583024581a8410ca24ca8be7c28118417d001a853a0fb50c046154398857d00e0257c0ae8033a0fa803308ac01088d390012be056fa802509b40d021a00943990742a8c5f0a7c0c420c006af814be38a090297c0ac388817cb818b20661d482be800cce3e06a105f1c7c0a42abe056f980350a6345f40063001abe052214e38c080c5920062125f2e06380148657cc81a8536058102708a184c1be64c98021092c812b204e2cc66ba3809d55005212e80404613682e062115d0606ac280270a224dd0a3809420ba380942aba38281284138e81285514e18148c05af9d025180a5d3e052f8602908a21c132052104958c08301685164801884b00b8188451c6e990297c3012851640d592aac09460604a1255027162f98031640943a9213a731d3e052f81586180f814a60c0d423b0062f9903508a3ce02a7c08d90250eab130254cb012847780d660004a125f0c053301186b5501f02d0aac018d0640d5702d0ca3ce01c04a72002508e3018c080b8188458070002d0a30012887140842023000810ae062c860310922ad9326009c28b26008590250da34d4a8c0c0d4226180ad65005611d53e04e00158691c2c81692508f01029600d580004612c59bc5c0d42291108f0e02538f0128470c0d459d0593013822409c60290d62858033a009488bc0809451c04a70502508ef9502508f8128471121060251809c3596178a0128c78094238c6c48128c6c09423881152c970210aa5cde1c04a71e02508e3014ae64c019ae04a1844a9311471802108e70e16042154502710ac1730062c8b03108a224568c18101185118b818845603030232c0c4348c24081384164581885514a4cce5c07c0ae054c408c28aa04351702308a33451c04e70502708aa800230920004e800c590330ceb8a031640cc328e3216c973604ea8188616409456c08d501484d8cd811c68c40118510cb1aa0604750b02308a2545994b147013aa05671d02b14081584710a0011b09c0200355409c39ae280cc2294600cc28903252c973604ea8188616409456ac00a8108515c1950330a290149c640b4229c58095936042c81286d14ea800290966d6040a98811851a85010d404eb8118851db72002da00a602ea00cc2894042214040040014851a80cc4adca00a4228e739628e025382812847000ad9106c09c20b204a2341009cb81294062c8198600901885364094409152465816969),
  (0x1a78cf9e25b11f82eb68da0ab6b45892cc5ea136f08777b919a62c0a53ba9c14669ae4709f30db66c22bb8e286e223810f835019a000, 13, 0x551815ca06729903308a81602b9409433ac040a6403190094448062b011acc80c4102b0ca31d6040630180310a61272006612c34d0640cd70290ca55422a080c5903360e1d02508e1a560804a11602508ea952c0621012863404815aa04ab011887226c02031a4c010a00561ce832066b81586522a0970255c1018aa06619d6025409c2025580ac44ae0809c21c080d814845617812851166c161c04eb01584046b812b005a34561c04a71602508ec018ac044812920409423881156c980316409c3a9b35870129c5809423ae640c424b008b812b206218c45b0602050275408138491022959303008d80319000158c04e1a460b204a454e9b2601013841640a5902515aa1503310281396066a814885980ad416056b9f0215009d90251063342265809c22aa0521023ea009c20865116a9402b0ca818b204a1d459a8541015aa0409d502b0ca28450804a00178814094002f0ce32422a066b812b26c4813cc05aa81598500bc24ae04a384889752d1814aa0008c50804aa813b005668198a9554811b204a1b450804ec015b0066d1e0272c0cc32aa0008d702b0d2a97462c0ac30290c2245902519aa82035501816b00621cc208540ad6029591814c605619c609ee009c28b204001184b0e66158280809428aa7808d50250c2284025102812847600bc55845460118535c09592a60101484b081814aa0561b570251c2444cac6340014aa2c09c269a300c4b462c09420a8052235b1605a12d4045918138450c2a042c04e00158651121192a042b81386311aa1903508a81984540d5402b5cd813a80521b468a65809c002b540a5732062154629c15020502708a68c0310a6d814969808425a82c0ad924042a1902508e20c66a82c0942265809c2282052a170310812802108a19c55b06c095b027341016855646010ae04e18d43204a12ca98250f155c04e114308831400178808c01084f0ca205025000bc339096c68302f092b8202730b812853106c83365cd81384d0e661402f092c8128e12227d541604ea153c04612552a040a423be0009c258a55c0c5e0804e001280056a80023092c95021640943a93354b813bc5409543204a14d73006614422a04aa815b07808c64604e11444aa3008c43c04e0970350a6214689a154a864604a11db03150a3202508e1a402a062a011b2a008c228b3),
  (0x2bd6a5f689e96464a08de620a7bf5dd66c45a32627d778562d20043f4fb23bdce3c36dcc362c8496a1dac6b016fc462116c2fe05f40d4001c000, 14, 0x13000529270330a291702b04a8138499c09450a49c096736ac09c20ce04a2267260429172404e124398b1013984e05214c33ce5c90108530e2ba70339cb8198519cc81184918a6ad8aae05b7a7031493818d4480842a893013818d449381ad40621a449b204639525e5c0ac29ce9cb8188539d3970310a61ac6aa49c18118404e1ac40ce9d7970350a61c674e6c4813b00561cc4aa4062304a4ce48a8102709218520006614674e5c0cc28ced80c574e0633970310a621c6593564b81484344b3970315c101384111a9192e0809c20b204a235902000a490c0529018867142b8a033640c43292b48b8168804eb9903108a9040251090128472c0d4c02000a425840c0a4b02b0da58128e1326e9f027540ac206000c4298635cc819aa2c0b4258857470129c7409423aa340cc20ae540c591606211446800565a582a042a850804e1055029122e8e027540cd5160408421aa04e2247aaa5d301096500842489115b4002a05a10551605a10d82a08181884354a8b0230a21cc648e731671d02761401384ba0a8b035000ac3089354b990310861a5950066581086d38aaa32c04e0820310871960270c08d5031126b0e027540ad702d112c15021640cd703110a85552a1028138410cab0e02538b01284712aa815ae6409426aa600c5502b2ca820270821b5530580d42896540ac208a52e6c0b02d086c022a066601086360c031606610c3ab004e58302109a3c58582c08426ae640c4218a5412b0e02538b0128478cb012ac8c09423800462a402a056b9902509223562e05a7013aa00a81a966ca0148410da2c469aa0008d516046a813875000a465aa640b680335ca819b2a00cc288892c08482b00d20d0330aa19d0280661354320860198510c622d732066996027a00d6802b640a4508e5b80813d02c0ac26820421030006214c318a3870d0210a219d702d000ac64d0b8c81adcb8c81a8490ce2cd75006614483206610ce02540a42396066204e2aa14c014b054084e0310ce2cc52e05a7013aa340855166c084268711677150272c0b412805a10411604e10c749f5a0a801605a15430b0000a42384300cc32a2c0d400210e62446198bb87190310aaa8148005770532062156e029a00ac53d006600b035040a4b02d000ac50ae640c421a45142013c804a68c031900ad702d12b2150235c09643204f3010c805ac8128b121200d04900a421806610d702515e35643206a28c0351009c14c056ba402909a23e40005ec81a86528264762a0470019c004a11b02d5c09605004722802509a24c78c00903602709ab812d00662c7602046a818c02c0cc228a19520129a940b42aec547812ec0421c445ecc91815c8980ac23881080c562604e6a402d0aab814aca40d641804610445933052170310ab3200234cc81a85311639606c057b02031093008021a06010a005a1c451c080a810270921cf65004f40108711cb02802b807013800561011ae04a2c450004a0013822409490204a11d902915640601c04e0015b23418168410ea720027a00c5903510a54e01c04e002023096b812c038094e4004a11c33204a1546880640d453006a081488540a4d0350ce0001804611c3580640d42296164ca60216409433b20522b529c8600d5c3c04e581a8655c0b5732062c240315c094308a9612014881409e40290d29e0270821ac62b05c0c59303008c20b204a24c6aac1009c102f600cd8081409c102f0c22142303008c29ae04aca40405b2014b09808df0270d6305902522265452e5408570252cb0f025540d64023102812aa05219c70840c0a426b2613011b004e185920042c8128691d68c423060a8158430e62050270ca81084f5c0d452aa600cd9049048138605a1a440b204ac984c0463013b204a20455975362b1530bc09c2a86958096027080b57025a80cc5a8c358b1803105781a845112b1502b800cdb0405ab812de0662447182),
  (0x2210828609a7d85de07765d6671d5bba689d870608579c57dd5a852dd31247f5154421cf2a326cb6226f4896204470e18744e40dd41e2037c000, 14, 0x50a8202b540813aa056194508a10094002f1028128005e19c64ae640c552e05aa9402f09290118a15cc81884526a21e3404ac0198814094d033600ac43aa0008d702b0d2aa31605614430292c095724042c81286321ac140404a145554046a812861142012881409423b005e2ad732062c1702d54a8302d080ac378894808c70ae640c422975fca8c46500a4268712c095b1605a12c2265809c22aa052a8b0250aaa015ae500a426a854085724042c812875146a040a04e114d2805a14d724042c812863900a661605a12c128a8a9a02708a184418a000bc40460084278651028128005e19c84b65c0b4c2805e1242060625920210a620d732062114aaa41009442404a11c2046000138410ca22d73230a015ae05ab812881162355704640d428846cc816855080ad2023540813ae06a194809691470139a480ac2a8804ab1e0353809cd2405690168714cb81984580c0e2634084288671070132404299e2406610c33a65c08c228f121b01a2a04e9812a60522055260669814ae4c0cc22b205a344b59a480b4e0a04e201986578715029c809d61e062981386b18aaa00354870d24056154338916409479c080701184780095e1c54b01484b0caf05344c0a42586510eb81992178f0e02308ec15025096ba024046b812bc3408c248a11aa5c523038681084b0ce29702d480c5808066a81386b1922052a05212d90335c701985118a99f0257c98128477d401684b4d535025a00c43688948f815be052f99033089019a60409d70350ca2c471b2600c426bea00b6c500434083206610c368a5b098202309af9302d08b5280317d401684524084599474c1a803109a1a6a3e483016860808c248917d60138c052c900310862acaaa4180a420887c0b520005a11ec3e04e12ea3e05619703108e017031086324c2aa7c3012851640d593e06a91528040ac2386052c81a8a51a2404c9eea80cc20606611535405a98602308a2268244c09520276d401292100a520334c094438cb242546a040421042a0523015a47c0a530004612c438e120a9173205a154388c48d8902518d812847112285702b64b920315c094308952e69060c0808c288c5c0c4228c0c08d9025483090204e104b03510a2c4899ab60b990250921b5f2406af815d4a98811851a8b81184515a90002b6441b027082c81288d540272e04a5018806409520270e6354719605a4a63248c0b6302b0e2d811c68c40118518cb81884914b1aa0354950128411269150004612d84e01501aaa04e1cd714066114106480cd90250ea244a196964b9b027082c81288d55a8a02d0a203558062155202dd540188451a6a883604ad8802508e23450a44c09532404a11c002b29401284d1d2d1300056145a540818198430db51203148085302b1129aa02da80800290a21aea2404214c73d448085754066145702314aa55200056c883604e105902511a0804e5c094a03100c812a404e1cc6a8e32c0b494a4b40c53244c0c423865a93818d44808429ce9c0010851a80cc42915),
  (0x2570943e4428abe1e28455f5e7c85e9c773dca87045b32687592c5fcd6de588d54449fcfde389cb5029349261ce466c14cc51a10142ba0334000, 14, 0x3c10169e4011803109619441a040d81284140a0802d5c0cc318c0009490204ab81a8731524c462005230802b08648a035280a5002d1268060235c0d43882400c492c748014853040ac438a1008000230925019ae0622d4c2a0200d410020501484d200944a8a11840158004ac880210aa2c5a2c04ad1802d096b1a02568c01684b10eb0324062c81286d112b012c05249602908e481027580a4328eb180012867c501a8450e6b020352009580c14481027096194408b322268c31404ac170250a223561e062e0e0310a6b0f03158f891e05210432b8380c42a8d374f812ba3c101284d0d2f9d0257410f02509a1a453be600b425be7c181a8537cb0108406ac0198917c7810ac200d428be102813be0520815881640d4699455848159e052496021700d4399e6078148530e23020313cb0158c04e781888524f812ac04219c0250aac0f0210a23cc62c0c0d429be080d580330e201f1406a14c83006614490204e7960a06211c348a128ab332c04e10df2405a12d610640cc21be5c0b4258a558192031640943688958f814ac24084102718001284200942886600c560204ec81a8651664acc1862809582e04a14446ac183000230961a561e04ea01a87370b1c03508e50118859878802308ac050210a62c4606280942984600cc830102813920409c2588116631488842009410005210430405213431404a1010ae640a4c1604a10c498f14ca814a4062915029540cc3aa610a81a841540a443aa5d301096500842489115ac011d000a81684154581684300a814840c0c520330c629ca5aa4c9013b04c09c25895a0a8b0350821cd52e640c421869654019960421b4e2a41009d5033540ad72a5458108470e6215804540ccc0215c094418a960a840a04ea819865102904027540cd70404213591606611551604612c9ab00c08d802760c120350861cd832046114b06042581286d2d2cc552e6c08428aa056a99502c0842986d10a00b0350869130254c9012847000ad5265408cb02d54a0168005618468aa4c0c4b0210ca54cf4a4680a532a05211d702d4c001384b08181884360d180232c0b4388a600a4103554201882540c42ab6500a4268c7243415002c0b42a86154581aa405218c75a934ca814a4680a423b205a0130270974019ae640c421802c0d420985053014aa046b812ac6809e6025312015ae05aca424046106602b64094549152e33010004a28002f1009e402511630573206322602d900a661a05a12d2023182b9903108a55520804e0012a04e10434a44c09d803364c24029082ca6021640a4368d126a992027000cd732066c81887518a01902d08b812b2062c920212c094398c3217218035102813b0056581a8855c0b57320632120235c094308a95898138205ec019b01028138205e1844284600cd70256520248052135802b4808c50b204a3c4aa964809d61e04ea81a840c0a426881409cb0355c0a442ae640c581605a8120232c094348b31d6a932c04e1158303ce813aa05e184428b308b812866409428965410302909ac015a404628570251e65d520804a21202508eb99031092c022e04ac818863116c18081409d50204e124408a564c1848052145802b4808c50b204a3d4d9b2641010b2052c81288715aa1503310281396066a814885500b661605a12d724042c812863),
  (0x10fa83ac129e6aed4766b9b1ccae4c710b7d9abec4a52ea88135a9a64aba34910678035996c0a5640419288d03821840918230056000, 13, 0x52004280198c000950245c094298751632955804a15503e0468013bc4c0acf0270d248129240f811845400d4499018a81ad65c0d42289316280f029407942e0661143888324f090293cb819801809c2589194f1703360a1703308b2972a056155e1005a80148c047295031408170230a2194599040f010a05008d00330d22d501e05630802d500957033407815a0066b81188122a54500c0468019a00008d03e280d42187314a3000253c084f2006a14c548c00094a033280a4459040b81aa06008c20a010805029680ac338815c0d4629532e2f9c0333d28158513c80199e042f8f0317cc81485311671f1e046e293204a13439be3c084f0317cc81aa03c095f02b0c22cdf20066aa50275c094388a400cdf2e06a14451e052f890277c0ac502512a797035482b202309a19c589617cb010be4008df20066b8189e0422246abe7cc019843400b445be408152005a14c38aa0468033206610d02e06212440a04e104729957c801684b70f970350a279f1c58c0198470c625450be588018be0523011a07cd019851040a4102b14a485f10062c819be00b819b004e18c408f53c816023082d890277440138491167812b8400b462604a701a871166d9403140c819a84188118510da8040a04e105002d5c0c452c8500a425995708170350a27902c04678138691027863806610cf031407970330a278f10046154308c400ccf2006a79b1e04612c34ae400ac268f13c80f0294078b0330a218c5a9e080b50023),
  (0xdd0dc9d56d4fd48cf9c3ec25c0cc05b92ab3aacaa5a9ea4fa48a419f293786a78b6f466f5d84b139c34d2a42551f4181000, 12, 0x40f0f0276c0950365c0d580270e224ff7e3c8019bc5040198550ca79002b04095b1204210c62004612503006209703508a24d028056790027507900333c094f2806aa18033096244f2806278f28052c0e0250a222c59a83cb8119e04e1cd41e04612466fefdf8f20600c42aa85c0d423fefcb901eb40ad80330e221d40c06278f1c046144f0c046781886719630f0335c0c4349e1808c61004610f0210a27980310a6325430062b820210922346100424011a804a1018a06c085728042b812ae5010148410da35489ac3c0c5620244a302308e184f02914ac81a8f3587901e38b01484b3c801584d16234c7aa83c8013a0640cc259e640cc228d53ca01584958b06023082b163a0409c258617c80188a04218c72ac583011847580011845200c590331ea7861e05600128636c78129004e1c501e40d0902b74d01584710a2c460a0540c42a933184ab02b68a01a84710a7980296820902f096f1e3405e12c33805c0cc2a90560d2502794d01384b10ab1803310f013805c0d4298856021e34052f01586700b81985518af0f0253cf012847500ade20480c4269e400b4229e50801884d7881703109a19463a0404810270821959033500a465a35),
  (0x123e909c561faef6479cb9b1946c0c5deac094229c24839ea8efe67c2aa94a89fe48c1f18f707aa3981a48ac83ee118040815809e000, 13, 0x1420380c429803c0a5b1204a49b02508e78003309232c12e400842a863b4a012b60809428824078128515c0d4499e00101484d4078803508a18c609e080c5b1204a49b02508e0014ae04634c85da400cde4a6c09c25a8200cc2a8a56ca0199004ad8002d7800202d0a678138896c79e0275c0cc3488508b819843b47814b6062a0203108a0900204a12d7035126f0f1e200cc2a8653cf012847000b5b0296c780033092310033600c5b285c0cc2a8651864ad10bc180ad0031788093604a10c35ae780842a8d3b48019ca5040198550ca781029180acf3c04210d00333c401184540c170250a61c4f362409c209e04aa060273c094f0404214c5484601010805c0d4228931628060333c0ac92005a124f0c400c4f2004e701887315280f0c06214d00293c0ac56a0180ccf02b187900210a68101c05614c904300cc2a8631a200f0334080e02b0a6d902e066154318d120a8a501e940ac22a0040a4f1004e12d01e3c401a8410ca24c61e1808c20a060b812a00521cc4a8f178d89027082f012bc4078159004e18444bc1808c60004a12d73c5060188435c094408b526769036056155b20066c018829409cf20940b42a87378781284b78b81a8c400b4f2a06a14443829409cf02b7809444fe2079003378d81a84550b8199041a0188530ce3010253cd8158c0528018ae4008570250e63d655a06278102b2410188436cb812a0200b550310c62cc9a92787813a81809c259204a2842031243000250a2b822e04a1043a8d3188101e7809c209006a21459a05480108530e36a520066157f1e6c095b1e06a8013873),
  (0xc20c19c00b9fa9ca5fa34a2d9cc81569466963e59556a53f51450d5064ed33630b2aa19514613f08407d07606f032007000, 12, 0x408080253c82302b0aaf14031200d4328c408002005a10434a00562d501e04c01a8c2408c2088f1663441205c0cc2a865407812d6940ac24a0500a4802540c8f2805610501e280c4228693ca015b83cb81a8533c78e02308a1b4689e7078108513cb815b03c094268931ce30f035704011841707970350a6e0f2e06a14c338d129279c0293cf800290821acf10046114f38600cc25b83cc011853700a4469e04279c0293c50602908e18dc3006612c729f14079b0270972900332009d03c05278129e40f0148450ce101892080b570230e6a9b1606a11e55a200cc2aca51681a8539528f4a06a7861e056a0128636c1012851047814a0062b81a9e2080138557878129e400a5e0250ce2c5b1204a49b02508e00148ab00101484d3c29ccf202009429b63c10188493c11702309a1ccf5a3c0a540256c0c4419e4078128515c0d4f0005a80f1006a11431b6000ac248e12e678f00200b4298754009cf202409492004a11cf1e000ac298405a22422e4008429863fc83f1e540adb1606a11db3c04ea019fe),
  (0x1826bf4dc2ab134509dccd623d308c7e8ba619c2ca45d9a5692168aa41b9e80f3278038f9b88be251215c87682860f4076827810a000, 13, 0x1b0006a80159004a41903114d8148005768103508e40202909a785027200d4102910a585e1e04a79e02508e0811820400128430430118204a19cf02b1de4190310481803108640202909ab0002f096b8129012aa99320052135320062810240521443992600d421a63c0c5020480a428873200990350a618c829eb144860316c094318c05680802540901985112b69026056156528062781a8654079002f08e08602bb47810a03c28108430de2a501e4c80158410c6c0188b53c7880230927af0355c0a4388c54a63000253c21a02900b01384b3ce01484d18240129157078109c6ca0158413809581c24084249c04a21c899514048f2004a80f02508e235c0c05679c0c056144328a92a76850233c0c401e06240118654078129e40094238c3c0a426a070701485140e0e0290a219c659933c48119e04e782023400cc3a9e0c08cf0204614c42b83cc0118533c18c033086184f3204611503006612d01e0568013a03808c228ad3e282b02b3d28148454008199e2009c258c3c094f02f0d281000400ac21a005ac018ae04a34c7a8c410016a0780b42489500781a845807a003508e8015b878e01a847700ac42a40664c451e2009c25b61409493604a11c448a00301384b7428518046144358895c095e40780a42986d2ea906d3605282b0290ab2815da40c018855200adb5606a124f2006a0a5027780ac389e940a422bc3c09d00350528139e056c01489178b81a845408080253c82b02b0aaf14031200d4328041a0188475c09502004801a8450ce31000400b424a005625480253cc012e06a124378912a6b2b02b0409ed2006a10c8025947819825408c24891201014b20461b462006ae890290c101484dacf81384b1820250352008432924010108555428f02750401384b1024814aa05a3cc16a06aa819ae05a214e88c5c0d5020d00c42986b24085902d20c8188452471850804e10630258d1900335c0c434c66041903308a18d002d1564d490c1878502708219448a02009502a0661444ada940a5046052154802b40d8f031400d5b1006a116520052d86029400d5e1e600d4238716cb81a845),
  (0x16f4b0ad7aaa3b408967c8522470b07f1be51c4ad2263cae6962aad84c6a4b11ba87c43aa1b8fae5fc2d693c86522da169881810a000, 13, 0x4d6815b00469931806212e802310a9932a04614534604611500351a7190033d40c63643008f20250e319003548b815c604aa932004a144338c122768c0255c0c555a06291403108ac8c245c095702d0d33153005211d70251164049a9b300081090056a0002108a408140661248100008425902030108490c631d9105c00138530c2244dab458d012ac280ac26b4580956140561344391568401684958089027200956029116f8f0292028109004a1d451ac640d428ae280a426be3c0a5f3a04ae9f02508ee0168ab3cf9c02d0927811204e301286110679f3206a10df3805a124588c700cc93e04ab81a8715878f0204212cf10046114f12180942086722ae0f3000b81a8450c6c0158b31a2e1c3e046114f38180cc2886b192f9614056135f2c280ac2686758301031480cc31ac9808d62e046144429005a4a563e052f883206215412e04ac013861186b8a02909a4050804e104802520501484d2008902708240128c0522aca3006614502c6809c2a9004a7ab0356c281a847112f00035400ac802558d013b42409c249004a18202909a0162004611c8025116d8f0253cd81284794401384b08c8118552227ab1806215500296cb81a845956818ac4c0ac80250eaa250333cb2b02bb409434895952881e78d2502b08ad1e34056114338d11e7281a82140ccf0273cf0139006a19410233d29b4a04e12461e05610c598a240813849000c44290640c563e2409c24a0046001590080a4269004a404aaa8f3c800029400ac3a9e04a7813805a125c3e7409c208633cc818800409cf0250c22ac1023c0b4f025000ac4a9e000acf025700b44482400ccf0253cf900292009531e05212c508d524608f02d3c0cdc5a3c0ad40255c0d4498a32227900005280158753c094f1e640c4f022409490204a11dc02d1520062005211cf025116504f1e000ac2a822409490204a11dc02d3c00179e04a1ac84821878179e500c4228933cc818a04c0bc2090640c4228d52c769026056155e4a6c09c24a8062781a8a5),
  (0x12bc95ac9523570f07dbbec1f52f907c4be09e8aed26bab259822b68583a6f11ba8343bc9af8b0a55a2468f0060a22607f8278056000, 13, 0xfc7945a04e12d720600c4238733ca0f2e06214c34a818a0188533cb8188493c0ac66a83c084f1e5c0d4289e3c701a8510ca34d41e046781586d50a0f02708281e3c5408c23bc480ac248b13cf1b0235c0d5e24056124588c5504011900561b4f9fefc790027fdf942e06682d02b08e7941c05214541e06678e0290a222d4283c084239e3ca8119e04a1c4f1e380a42886b3c79b2e06a10c329e3c70148510d639d41e046781586d466a251204248f3c04e10432ae50401184d0eaa902a062b81286311664d436042a012a8052a17285c0942087512678f200467818b8066254f2040b8188530d222d002d3c78002b3c0c501c06214c5aa0147813d60467850278c08c3280062c81a91320281a82200a4259e740ad02404613443805c0b4229414c98f206808500254009c448ab400c50264cb81484b400b4488b332a9932006281026480a425a6400a5002b0da34479935948015a62408c20a68c08c22a6400c502a062c81287316b990183809c208634c99a2a04e10434a604a9900350a63ad3560469818a68c00188430ca810340569814a004a200025086305720042b813a05c08c268b132b68f6c06a14e31e062e236606b40128711267a302b6041903308a18e302d1831a320062c8198751448118a3c0ad32406a11c48c65c0ac229018c4813c606319003140aa302b8c8014a00561b4588d322a8133406a8015c60520811a0000ac228e18c0011ae5c80108470ea2c5202046e012a04e40168611138ad260400148474008c202d16a34cc2e062a190350a6214b59e6c0adb2805660f0330a220d4523009552404ab940210aa24c68d04c801a853),
  (0x17a8b6dd5b2a1743e9afc89a192fd86ecae9132697a47aa3b90f67423799898b665ac2c095e895a3501898ac847e1a804081e80e6000, 13, 0x9480129e06a7990350a36900238d581384b7168158493c094709e000ac11204a48102508e0015b805a324f00066781aa0ac09c80250c2080033640d502a06681903508a204789a3b48162406212c3aa85c0d422da149813da05a1d7602305b016849b4c01a84b004190310aa196d0a4c09c10290eb6815dad80a426a0600c5902d0c60083206215432bc1009c0025040a78031d16b80290861acf68149813b005ba01582000af802d0d3a01290126a54cf020476810217878139e05e1ac00251a641903104801190080a4268a4c09c02c480c42186f156b81294132a7880237078a023082780023b40ad40255c0d45991170786021000c43588940f2d0311408c399e1448118493c0c6d02b14e8050005699d2c05212c338a150f01484d50f010a40661c4ba8a6c08cf03520085400042e1e02d5c0cc3a8b124a78f340561042123c0d4298633c20108473cd88035086195c1e0c50138430c27920233c09cf2e046116d2804a701a9e3808c268ab2a6744f381008c002b0c2e14023000ac388e9948014da2408400230e28102a066145902d751814c6056a2602909b30912000a42587310e484da923c281384104a018853944010ea540cd702d0e24190310863d4c2a8480d6d2e06612d03308ef2502b51681185311282d2804aa01aa83c8012ae06a1cc41bc3c09db0316d281384b5009543c3c0ac20a804a224f02046794031092a172e480842386312a44ed2805aa012a85c0cc219e6c78158493d6813a004ad8188833c0814a8056a170230aa2ccf0406279e2004a14422e04615459fe3d2815b604e71b4a04e0012800660172e540842387310678002b04781a84311279b4a04e78148004a22cf283c8012a806219c4a8a33c094031086b8f0005aa014a0540c421ae04a3047a953b49016a8380b422da0009ed28b408c26873500c5b2eb4a0168410e6a142e06615432bc3c09c002d6da01484b00095b5ad00b428863056815a85c0cc2abc3c09db0296c0900230a6001488b50901184d242a1b03150b81a85310bfbf1eb48180310a61d54285c0cc2a867),
  (0x1b98d0be2eb047756b3bd6629df4b29e9c4ca03af9874ab6d9942c525cbadf965ea74494a3b0fae78835d99b0a6651a2418a583da000, 13, 0x109813c605718e02b0c701884911ad920330869a302b4c4018b206618e31006318446056154398a78c7015b20521b4d28c680ac40406a14440c046181a924c0ace18046154488f300d010900622044604e10ca1c2c08c288751a64953460529830404a10002508e70188a9380ac76be4c0ad32806a14d62a06614634a063aa326b008c2a871126315326500d429a6280cc22b6540cd346046b81a8654ca8b02708618488b44c98e02b09a202031480cd432066114519156818e0316409436889682811a6200c4a3406214c42c02809531c06614446b4a01b40250961b5a3068901a8530c6d28023e0d340350a21cc52a60da01284b300a446b44cd0e02d0961c5a2668701684b0e221c926100854033400b44ab6280b422a66ca8198555140198456000b03508e185018066b81286d2e290d3261008c20a64c40118470e29931404611c3986380c590250da62440c0462030350a610e12300d421873122200023280cc8080408ce16046154498b120ae883a04ef88027092f8198ab28b81884d74001580200800a04a12c61205211c50b20623d4819074a8b0250861aca02915ab161405613632c04e10d62c280ac2690640cc218a55918159005a1a5d2c05241d033044813801809c50250d228563206a144919058a8b0250861aca02915b1880295918149405a1ad600046419031584016965409c21ac280b4002b0d23849aae4809d6145c01203308e1c446ac14e8158491409c803114096023096c8a2406211c3a8d3140000a18084218671164052a2c0942186b11a096100448138a04a185914480cc238711ea40ca02d29230a0332090198511440a02909a4011204e28128612000602714094308892165120e04690b02308a24c58d6580ac8025509019851b400128a4c09ed02d8d581384bb40946aec052436031600ac31a0acd012b4ac09423895b4293027b40b439b4ac09c2580b40d422b2047b0f5a400842aa0200d4228a3b5481ab204a1c494ca480b484a067281ab43c901a8530ce01702d9409c32823c0c411e05e10c00a0009420b69409c00250d2f0f0273c0bc002511654c8320635a35604e125002320101484d149813805890188430de2ad7025302754f02700b424da0567813a7c0ac238613cc81a85118608f0353c09ed1e06aa0f03508a24dc5a4009570355c0ac498b1047815823c0b401e04a12c4a9e70001584f3c001a8513c81f02b0aa81703508a28ca4a01),
  (0x10d6816bab1be2dea6e8b579a8ace466eb28190ebde5acad49696afc57aab29586aaa551a8312a28843b79a88c3a4c01f98a582ba000, 13, 0x82006a7970235c0b438bc3c09de2e046f012873156796023400acf0253c780023400ac32887200c481e7408d002b3c094f1e0408d002b0ca21c88b23c9011ae04e1844a9b3387818825409c259e0527100350a6c8002b00781a85110a8101e04a5950333c0012855480c502e04a13d01e04a595033488017855207815845fc59503348401585540b81296540cd20353809c102560901aa005e01703508a2c4f1c04a8138004a1ac44a03c09426a0047fbf16540ccf035400012847405950333c097f16540d5716540cd824062154e2006611c0023c0d429865387953006210cf0253c09c54ae400d4f2004278128711667180233809570313c7150230a2801aa04808c209c640d42291300a920804ac015869389012aa600a425887202b80040564014944008590250c634c76805470138a3c09d50290d600128c108a17203c094238631222cd53006271502d4809c32845c10108510e6c0c1e540a425a404e21592e04214cc2e60b8128470daa8f2404e115724640b442a05211d7025142354959b1207810006210c3990204050230821cc81406612592e0421448aa64c401484d4c98202909a195326080a426a64c401484d0ca31df1c05af93025086f8e02d4cf81284310e42da2c900ac21a6580d550334c8340330aa1ac68a69440158514d1811ea4d60118510eac8158d324a9890234c98402108e18198954c101aa668084e18046154498d100981023280d439a62070b0230a61d448905),
  (0x7fafe7fb3d7f96e47be378eeaca793322dd2b9756257b76576ad120a283b2748ca96a1a62a0508640ba15827800, 11, 0x67e50a080235c0ac39aa5c09d410180ad50315c09542e04613469a8480d570255cb94282008d70256cba90215c094102912a2ac89fefca120204ea1702309ad9703508a34d204480814a8d008cc0290dba0128d1d0a01ab6d00d5224040a740250d6a3402909a30488906cf0002350095402b112a0f2804a104339156ca018ae06a090023500a5b28062b81a8651824ccf200809428a8080c421903cd8118515c1010ae04a1d4698094e810270a690f02700b81984512b28802794a8f205c0d423865127fa54a54b8138530e3a140295c09c83a580c429a43c90198470ea0802e06a14432a03c09d703320a100313cb81a847fcb973c3c09d42406ab812873),
  (0xbfcbbfbb8b69a78a719fe91f9188ed82071d6e06b568a6055c846b45244b4324073ca3c329c1511380d7052039032019000, 12, 0x6d2812820632813fe40a814ca040cd70350ca7ad1e056a012bc06220de1e06a79e0c04e15430a43809c28825c0d422933fd294025040ae50275c81503108e1cde5a066f0f02309368f4a480d4288673cd9e2e066156d02712229495a054d9703508aa342e04e14743c06aa8102579a011aa600b423e804a2d4789333cf011827809540290d6f000273c8010843007813a406a1c4128062b81a8652a6d9003554b813851948170310aaa100355c09c128046a0902b5c09651e04ab81a8631a6a8f005c0cc2386594a1e000561254025507810a804a19c7a926c09412804614572a000a420ae04aa172e400842386311a454c9aa5c09d02e5409e52006ab812803c0c410c066157f362409d802d6c81e1004f481a87112610802309a3a41280461018ca7878158475c0d4498e5b40815825008c22ca080d428bc3c09c9023000ad730080a492004612c408b53cf013b6062b81a8853672900353ca100350a60982e04e15438da2408cf0c056a011b64040148430e635552e04ff8b1804f297035),
  (0xcd4ca9c90c65bf2bc7b8aabda80a79a4ea1196893d84c8337c071759657d4f84bb3a62a329c2952342092021c50d4007000, 12, 0x5858c0270a32970358c30139004a0230004e1557025201014b20461b562a062b812aa940a632e06a11464a000cc2890640c562a06240202909a300029096b8128e126a8146806a1457025fc4122e04e1557244c09c2ae804a08803500c81a851044016cc4808c00270d2b8128c17840159406229b400660815bc8008d20330e2355e2604e00158696c401aa8640d42888549a014a449c340230921b416805a001486be0080031d0934025e00b416805a001486b1823d4999004001185304281029000acf0271022c4002062d9403308621483206240002b6828202f09a09002308eb8128c920255692e04ed94025040c652005a11c05a04e801486b40a814a85c0d4229e507818843040acf200667801e06611c32a040c01185340701984b40b8198451e265461e04230158406230f0311849b0250861ad41004a40138615c1170250821d4b9fefd2814a04e12d00335078168456c8019a804a7951e000a570310ca7800333c09d42e0667811e05212c6023400cc508f55000f0235c0d4398856d2812ca6c094239e06678f0c06612c34bc062f170337808436fe),
  (0x1178870c2da062ed474bb801a66d0864aaed93da98c4c2a52123a81a3dc98e0bf65e22d295e8a325121e38de03821a809a80c800e000, 13, 0x6d2812829409c29a068e81384b780a4f02516ae9a02b2409d04a480d5a1204e12c47ca040cd70350ca29a2605212cf26180ac208673cf01a9e700a42788d04401a8453c2ad1e05e14c0025649190250961d471911404012b47409c25bc68e813849400ae502052a81387150b81a8453cd015ca3c0d762004610444b63c0d4229e6568109c0561d448b4740ac90274129203568481384f11609703508bc1702554081280063a01abce00b5a2a04ef0168005222f40251c25cc01e06a78139e000ccf0355009446b8480cc13806ae0179c066214689e3c00158553c09413406a00159e000c422b805a32522005eb812863342e9302f6ca81985140b8128473d29003310b81384550801aae04a31b02520c81885500089027096f9302b0009c3490080a4269000401a8470ca58562005ea8189e000cd70350cb29b025000ce51206208500056144399e04e08003308a404832062d0902700801184b74a81890080a42788d5c0949097558a818a005eb812a02009502c300c425ae04b2900355c09401e040c429c61809c80250ea31e1004ed818825009c24905008138490008c4290640c6326240a500c05212c4390080a4269004a404aaaa94401484f8cb81a8459428f0271808cf0a04e11458ca000bed0205e145b020008c288651e64190316848139005a98202d1809d62a0628017863192b81294132b2900350008f03108eb18031400bd702512a7ad02b180a490006210d62604a99602508e0900230964020292808d802b11a55562a062b812fe),
  (0x169aad4d4029634629a6c9ba3af12e785b6b9932c265c7ab0950a9b8487a3910e281036291208824281e38e287063100fd847007a000, 13, 0x1d3a182812841581080250a219203164094398d524618a02558901985111ab0002358a01a9404a1cdb1004ab1200042154398b100e0199e04701a8530e201c0333c0920350a61c41001400128410c501285316a0800290962820352009402406a0972404e10c308b322228602314181a853089150230a61c450004650198a0408d70350e231656a600cc28b4940b76460463013a604a22460a67c095f1405a12df2604af8a02d09621d31005a1253344c0cc24a605608002b20501484d10299a0294c0ad702d1229934a240842a8694d3b003108698e0310a62ad702d28f2930334d29a0274c0ac348915c0b483206210c92c68c501584d8c41903308a18c42604b18159005a226346280ac268c540ce30250c69840258c0ac802d11251c426680c424b44cd0108450d64011204e401286b2118a02d1809c40251022a590312ab28e0314d19f0274c09435ea05a2a654604240168c04e4012a6640d428a6280b424a601481984368501684b4c419033086d0a02d09629531005a125a6805a9b802d09299702d69393033c09b40350a61c4002120c81884520650169491040a02909a4011204e0060270922048025640c475a0a40c57025956818a006a08f03594001985110a8252c540c42a86f50b81a8454078189e04a08f0314078802108a8170330a22d4f2c042010035600cd00254001903508a19c7892d4060060333c3090233c0c434da05629d02c1009df02b0c0b440a00808570330e2c811a040101684318101684140b8198511d2854f0c052d8119e06a4010ec700a480213cc013b0056b8149c05a2cc889a540808025940a5027092801a803c0d422b6400d401e06a11504a74a818855400bcf00066b81a8653c09d02574001284711680f0253c801284711280f027480b4f2004ec816865000ac799e000ccf1e1808c289e040a4278a14080e0330a21d50005c0d4298653cd1c02d0920060a05211c359e04a79b4a04b29b02508e22590231a280802568e81384b),
  (0x147e9abcb9227f0f0859bc81deaedc758b7d9932c92645b1817dab20520a7811ba8d645e9d80eb27523a59bf0baa4d21f08d280e6000, 13, 0xf1e7c084259e04ae0602b09249b0253c0d420c0664012861186e180333c18a02708618458ca4c80148553c801380200d4298859400120062f0002f09678138a11a601b2806610c32b650b013904c0842189304e8138405a0100230962a48025d411902309e1c4eaa08cb012ac8c09423895944014c604b2815ca940014853787813820663010290862c4f0a04ed8100046144398a520c818827409c802d4000158405ab01388920094809558cb013ca04b293029951a503508b2a50006214c832062b08025200b530405a00158691824548020620100205228002f09608f03108e00128e12264190314c081490080a426804090188430d6b8129012abfbf3040b81984740f0f027480cc02004e12c58ae04a7980313d68149e0667920290a22ac61e05600f0335c0c4348a53c30f0330810f02108e7893604a10d70351263c494845c10108530da80f02500790025200d43988794a1e000561054025507810a804a19c7aca6c09412804614422e04ab8118751e68084a05329e1e04a79e02508e20653604a0015871b40815a8062094023080c432845c095702341a018ae04a1ac69995fdfa52894a170255c08c3a89320a1e02150095b2805212d41e780942086722ad81280461457284090188435c094408b5226f0f0253cf0128475008c203120f0f0253cf0128476c08c58ae08b8128410ea4cc80a3c094f0a04a11c10006210c699064401085120504023082c8188891eae8f3a056114f3a056e8128677ce0159e0521b5d3a0c0b4249274a01985514085002d146e9d20046135d2404614dd36600cc21a405a22498ba5808d202d000a445ba74001584974e9602b092b1d0005212c338d1749015b20521b48320660a6035514019851112e8002108e40d42ac3c0a633a04aea302508ee0168ab),
  (0x7a0f33c9b3ee76b9b44a85d0496b2ba38c6a7eef79ebbd074ad59a7adc5aa8f912a0c40a7b0bc9722461581e800, 11, 0xfd6a7031600cd420062d970350a6215b4a04ef0f2004e12c34bc04a0018ceb4b8168530c7fa53c3c09c903350801384b9409464ce60b8128530e36900214008d40259ca0108519cb81ace3cd8158450c22cd87e7879203308ea1702d08bfa73606280e03308a7a71e062a819b69409c25a0380cc22aea409ff304881703308b3940233c8019820561a5028400cd03c5409db2e06a114498b1fca251e7809c22a006a24d04aa40d570250e624540c04e827027fcb98027508018a05ca10029400ac36891167f9468066a92025400d438a0407810a004a19d0364009540290c222d42e5c80138410ea24d70404211704052b815873),
  (0x6fedcbb7b50e9ad279131ee36c5f7cac8d1e97b05206b9a726da1b0b2463aaf109a0c30e2a0508881021a030800, 11, 0x1e2804bf8f2804a8270270a3f8f1e9c0c5428400d428865fdfbf3650a170350a619544e0673a53604ab81a873122a251e7809c22ce06a24e72a066144f20067381882000a425a004738f2804b3818b65009540290d630544e5c0c42a873fcf1b4a04e12d0025516813a806a1cff1e500cd00253d38f031500cd0025fd39b03150c01885340b819845b47812a0000b428a094f340230aad9703508a2c469aab528199e7809db0350ca8150330a28016a040a1b031082801288b407a702b0828012887b4a012ae500842a893fd39e025fd39b0253d6a703194d813a8400c42a885),
  (0x626c1b7d2f6de6bbf762c4cbc96b22a41c2283705206bd0792f09ddbb475ae0990b1a4768890da143f642803800, 11, 0x175204f28f025fdf90243ca012a09c09ce0330e278f3604611674e5008c22ce5c0c4298b53c8011ce5c0cc2488bfd39403140097f4e6ca0148519568148474009547e3ca1203340b819845fdfbf7efc80e2404e14cf203c084289e40b8188550e7fad204148188530c681803109af100313cf013ca6c09d70350d62cc72a09c09ff7e389013bc3c094f3c04a11de1e04a79e02508e8018a05cb90029400ac3689116655501e9c78168510c281b2805210500254009c55bc3c094f3c04a11d02e06215469fe),
  (0x76aec7d73a1f18d4ba7b4be12827031debb6716e11b5b52696d117aaee48a8f91ba303e6690c592a1020800c800, 11, 0x257e5ca8139e5d4813853787813b604a0142e4809c2a873123f952a600c4f2a05af013865d00a744e06a14d03c3c09c28bc3c09e7033787813ce480cc268911eb3a7209da0118510e621e72e066124759e7809d002340b81984d9d3902e06612438b650b8198550c63acc2fe6ca015aa04e79703308bf951e5c0cc22fe5ca813aea409ff249cd9402b0a281703308b28f2005b690031b47a90310ab29b0275c0d4328d3217fbf7e4138139c4809c299e3c8018a05c0c42989538a8139e60a812849d00ccf2006a14501e6ca01484b3c095002d1427972e4009c208751267a702d9d29b0255c0d439891fc794025),
  (0x118a870c292116eb0727b3818b6c0c5d5aa5944697a4719ef0e926c42ce9610a8e3fc1fa8fb87aa33e16589602f20be05b815809e000, 13, 0xf3c062f012da50096720940ac228715cf0168531eaf272e4809c2987140f01aa8b4096d2e04a12ed30062a2d02b08a21cf0213d3818a0d00c429b640b8198550ca38de2804278129e7809423a8046a1703109b6940255c0cc359693ca272004a14572805a14c5a9e3ca170310921b4f4e4009546806ab81287316230cf36500a4f0250c2a17035500a542e06aa0148673c0b47896b3d6940259d2814a004a1c570405a14c7ace3c0a6d0004ab81986db40012a00627902e062154399e9c8012843516812da500942388d3ca011da500942488b3c79b02308ab940210aa2cde5a9ca819b640b8198550ca2c461ca500d4f3c04e11544a0673a502940095503312232de1e04a79e02508ea016a855a016853d00c444bc3c094f3c04a11d402350d810a804aa014a85c0d4298cb51390025086b972804e104398cd513900250a328f0255ca0168551276a51e7809c22b606a20672004ab819871507810a804aa272004a10c38a86d2812ca6c09423891500a465ca6c09540315c0d5b021166825035953818ae5409c29ca6c094f021500aed28b409c28b69409c25b69c0c421da5009d00235129b0270a21a462ae066d8109f551f972a04ea142e06212544a06242502994b81a85112632db28793815a004a1c572805a14c6ab6509019e80621d5b02951a01484d6ca272004a10c36a83c0854025500ac44b6500c570356cb811841166f2d4e046a255206a145036062b81a8651a642675a04a137f4e5080188456cb81aaa04e1cff4e5c09553c400d422867),
  (0xab89919428e17f077d67a5bf54c4d94c04b94a049949248b47246b41c4153b43ad3942fd2f62ef2e82751cc135032019000, 12, 0x18d815a86c0842284062a140c04ea81598046255702554d815aa04ed9703508a10168c93272940235d29402d0821cd428540cc25a850b8158530caa1b3c5c095e36056125e20a40c421bc04af1b02b09231caa97350901584d50a1b1e06a14c35b63c701884d0d2a141e04211db1e3d48118513cb81184516ad8f0356c0a435a83c08cf02b0da64db204079e027082195402b152d940315c8170250821d459a04080c0290a658128916ca01484b0440139e05aa003006214d702511279002dfc094029fdfbf02000b7f02000a57027006018853fc095027000c403004e5816869fc6100314080c0335c09438b6500a4836500a422867156b97204080b0236c0ad8185c094298691a2a1036066d9b2e066154328b150a102e04a1243888d50d8c24d009429875122a016b651a01884d0d2d942e0561354285060188550e6a1703308a30db28062a142e500b42287312a325e4a062d9e031),
  (0xd2ed27d20c65c5ec57c50c01bfababba4b9db60adbad4acd9dc9d59aa9a399c8ab8147c57405e34aa44937c2c11760df000, 12, 0x3f1e0080189e04a79402508e79e243c09520270e220c59bc05bfbf7e4090199e5009ce0350cbf903c3c09d20313809445fefc79020380c42986d5080e0330a279402d7879403308e18c55fefc09002b40f0f027300cd402b1222a401006a09e2805614433a05c0c4218e5fcf0f027500cff00008100205a10d03c3c09d402b300cc488a9048011822c80158530e2294daa8409019ae78b8148470caa122e04a1243691178d9402b307819851106a0c3c5409d468052135e6806a114698f150a141804614c33a86c08542406a14c45bc500c5424500ad402d0e625464a878a018ae50b8118410ea2cc62a878f01029096f1e1205212c33bc248290310aa19c41bc6cb81a84378b81584914a7cd42405613541e54d9703508a1c54021166a1b021248011aa062c1402909a48f3c04e10572804215452953940812a80628172004214d01e7809c802b0c2b8198a522aa1b1005aa81386b50a141806a14c3388324a01aa850a9402d0aa1cc488c950d940315ca010855126296d5a2048202d0aa1a440ca080d552e04a14c488c50095003140f0f0270824818a06c0c422ae406011ae04a1844a953),
  (0xd2ec4fa869959468af86085974464163a63362c62560c6055c857956055955254b4fc4f54ee4b142c35f25c16b068061000, 12, 0xf0c080c4f281809c26b006224c6aa8180b540406211cf1c06214c62a04078118473c8013845080100290a67ad20052134329e4009502e066801486d14e5c4f2005a7813da400c502e06214c020062b8198651d252c62804a1018a83cd8118513ca06027080a436b03008c28ae04a10109152e6f0f3ca4b8128530e220cf02780d421b6500ac24bc3ca0e0350a218c49bc3c08de3c4808c29871fcda50276c0c5e0257879e0270a278158897879e1c04a144f1e540d428bc04a21c719133cda50273c0a5e025116f011bc7808149e06aa0f0213871502108e1d458903267fbf28fc917027fcf0f027480cd70253ca010a84870138530e2a0f027508102848794027380d4328934081e1e480cc23ae04af14025507815bc3c09c219e380c4248d33ca011bc3cf0e0290a278f1c052144338d31d6a0f0233c0ac36a83c085e20046f1e2a04611c38bc6cb81a8430caf0f2406212c3497350901584d50f1b2e06a11553c04a11d412404814d2062b81288316a32d42a056134d9a04049b02708219502020094208697878129e7809423a8056b902e04a1043a913fcf1b2805680f025380cc388a3),
  (0x692d179cb1ae2ec4f762e8dcaaf734a4ac8e90f1ba33c608b30b995b24616b393fa42332648bc9601fe2c054800, 11, 0x3f00400a4f3006a10e03108ffbf042c0c580404ec019875fdf8e1806a1021c066154338c08a011845507812843c0d42389304c0e0250a61c5e28480cc23ae04bfbf3c5008ff20fc01b031400cc0026cf0189e04e185b025040940c04e08128611122ac1026009d70250c6234eafe3c8019a040c170270a61d4f5a05680e3004e14439da5009cf031400ccf023c0cd40c04a31402508e22465805c80108550c678f2004e80f027408101e04e14c3ab03809c28ae407ad02b600cc38887387800233c80109e04ec0e0270a22b410c052781986b),
  (0x5bab1f5daaed44a7b37258caa94727226bc8782ca964ac25768910ea1638e670708b60ce1801a82e04e08003800, 11, 0x141e04e0812806c0d6d1c06368e03350a0f0250809d828380cc2386b3cf01a8204ff9e2850a2d027096b980270a630f02150781a8535030169c06670158917969402578084203178781a9c38f0138450e22cde1e066f0189e3878158510dbf905a50095b0310879402508e08c0275c094358d3fdf8f3006aa142e06615433a030581384904d8f3c056114f3c04b69402509621c748030b8128550e6a021c066154f36056a013a43809c2afe08a180330aa7bf7e3c1013a0),
  (0x15f8a29cb025071da8cec419fbefa27bbb989abec6e5d0ab995bead853ba6f12028343e099d8b2e4701ec8be8412106052827800e000, 13, 0xd0d81898e00c422e830085b2a04e12c10006291402b500b5436042c0188671aa425b28063a011805ad92031000ac348a11aa41549b62009412828095b0210ea24402e06a0015a85ca8b0250861c4468f3041000330c00c0350a61c483206211471b6640c4269493c8013a8200cc228c780c5b3c040ad20315c0944a8b378f090230a218504a04e801a9004af06023780c52025c0d422b6780c5e0290c234c62804a101880480adb4a4008c2aa406210168a924b81a84554c016bc5c10108550ca29ce9da4009db5a06a11505a0636812da3cf018a406619ed3c04901ada04e1cc488a578781abc06768169eb40d5e02d0d238462804a80189e042f0f0253cf0128474049b0250861ad7035406011ae04a184b98c50094203150f1b0230a2a06027480ad20405a124c0235c101084522a5cde369409de0293c09445823c0d4f0290c6f1e28380d421873122a1e0213cf018bc3c701884b0d22cd41e046a0129e056237f7e787813a4066a1e027096b8129e5070148515078109e3c70148513c78e0290a219c6990b507820230827940213c49b025086701a9c056a0108d122648f3604e11541e940ad5031414818ae04a18d42a056134899353ca018a03c09502e400842987116aa14283008c2986750b81684b6c0854285c0d429865507819a805aa015a85071402b500b43a8931624a4f0c3c101a8510c6d8f0290878118553c08f02108a701a8405a2c4998c5009420316c781a9e04f290023096006027080a436923c0d422aa3c085504052134489d34078129e3cd81a8430e679b3006a10c388405a7861e6c0d4288636c78e0310aa78f12046145b2e6009c218751824cde5a056a012bc3c0d4299e780d4209e7808de2a380adb1606a114418b31e2a0f3c046154f3c042f0e033780a5e1c066f0148671a2435e1e066f0189e05a22cf0c046d940270a278e0310a678f0c0460820270a27811e046c0e0250a222c59fe),
  (0x161cacbd29a6b71a488fc071e56eca6bfaed95d29c24b9a208f466c43169778bae57626693188ca45e2108b5850e28012a88a82de000, 13, 0x7d2812ca14085020540c42ab204a24c61a094095f4a7c4813a87c09c40290d628461a094a81185194c811845166655012500d4298a040ac40c05611c40cc7ca81a8530e2205027200c490204e001486b7ca018b206a1cc9284000810822409c002b0eaa2602909a3cc906980842a805460118550e63441000664090204e008023096205916046c814cc0422449a96595b014ca18401284128c250210a61c46192408060270921d503006628f027406011855102345002200d402e06a144498a5d9285023400d504a2808c2a8651831902a0672812ca94b8118450ce35478cad883603508abb60350962c4646056284027400d4398c0468150335408c38c640501a9405a1cc40a04e10632e06a14483206610ca28424081a8005248602908e18202909a3cc1102430149004001484b0ce2846a8e51818a025080843ab004601a84300b8b0230aa19410211e65c533440202031480cc31a6400c503204614c42915256d1002d09209b0a1480118470e628802308a355436052134028480cd90256c0844a8b1049016800521ac0380667811c06a14c389e04781684b70001584904781a84100cc80250c20031404a701987512248c12006a0100315c0d50286c0a4219e14d814a805619c803514a404b9a04080c1604a1443988d04801684900805023400c503204a14c548cb400003006214c3a822009cf02b0d241903308a80f0293c801484b38095002000aca2006211d03204a14c12e06200e029096b8003108e8001806215590251261012a04e5816a0066018027097f95200009424a006681020300c42986d20c8198450408802308e80168890000802308e804023400c5024062c8128731924ac40a5c09cc0330eab812fe4029702908a80e2404e1155002c0a425a006680c0354008d22a052b81aae05621478824028402510281284710200158c904a1b02128d81084512a2cdb02000a502e052c8159804623469a85c0d422931),
  (0x1c04ddaeebb707b7cd96eb7b3db920bd8da2a8f33649aec9b24cb204865c11a07eee2749b491722a8e45098d8aae3fa18d886019a000, 13, 0x78a018a606679c03108bf9324062b812fe68f0f027480d438ae04ae9a025700ccf1c066144f28480ace0250c679c263c09423b47409cf0250d6305c1c700b42987129279c029147813b806a18cf347409cf025000a440b8480cc288eb14a016bc7ce8138533ce9f027082194658c1449003508e18c636200d421865780b484a87009660216078108531631850204e10630258d19003340a819a0540cc2389119319b2a066a1903308a20d002d1966d661004a48f021505012cc0421d45892140840031142013a805a9018ae1028138410ca0890252409d5031116490023480c4902724b81184598a81884d000ac94a955e600f02140a2602908640128951478129e1409423a0066c81aa02049b02709219440951047810293c0ac1203c0c5d1e04e781886516a30cf3c052e001c06a144318b310f8f0257c0ad210640cc2286d3c0890252408128471167814bc040a5028066501287514678f202009c218610078109c06a1cc78b840e01284b3c084f1c480ace0270e6247f3c500acf0253cf0128005619c02006a14d002400cc258694129d02053581586710a81203340b81984512a4c5e1e062e019a03c0a423bc500ac82006211d0029400cc1120428019a04090198550e230c010062f9a02b08e081482400a42a90640cc21925140018a0980c4502000a42592200a4238a1513010a40621ccaa92200a4502500a425867200c45280008428b2980842a8b32ca6053c06ae01187348aa002d092e000290960800333c0d633a04fa0128611865c744c06263803108aa944c04215400a3809c2a98500a4268004a014cc05a1d553005211c6597114a018e85408139805b30e0a04e144002b1123848a9456273020232009452828095406280942186b980846a8f100901a8a1009c10290c2000003008c23869116a000215c20602b08229402b08eb8100056b8118611124d4b2a8980a520315c701184515accd326400c492406a09032046154328b31d69900314c801aa40621cc5492142900270861d4536200d42186550f01484d00a0a025480cde02112a2c411204a48102508e90168005232dd203c09501e380cc2886d3c8012a03c70198510da29caab8740a4259e04481384b3c095c0005612493604a781a8820094208a370781080380d42989104da502558085402d12a08158c50801a8c04e40128836c0b464ca500d4a025600ccf36066d81a8611e3281025400d4020062b81aa03c281390052401a885000ac60933),
  (0x1bbcd6ee52aedf70eb29d61a9733a498fcb423bf094819bde1d9edde688acd94ae9544439ee8db65002108d505561a801c808000e000, 13, 0x1809c0350a679002308278f20046104f0253c80119e04a701a89322278102b04e0168c0561a4f023c0d429926cd000291809c398951078178451c250c13806a78f4804615430b06070128410e6444f4a06678138204a2ad02700094389e7070198510ea78206062201990280c4228a31479a03508e79c02909ad0002974b01484711628f03508a5bd10a63ce0e0310a67814b80562b4f3805201c035086785347409cf0250d2205c2406614475b8180b4f0293cd01a84bb4a0129e68084299e08084e0330e238d020600b4289e600c5c6c5009c288690808c629e3c70118450d651c389008c228731878108c0c0a4f3404212cf0c04210c699e3c1814841380cc489953ce180330a2782023680acf3e06a12450da70c8189e400d420893b479c680661443a9e6c08c16804612cf3e06a124609e3ca015b206a1c4429e193814851193814845083016841b4e0189e3c70148510e601c0313c78e0290a21cc529c046d01098b3c21f02b082e180333c084389e3c2014be056301188170783035080b430b03c084298d118781882240c4f0273c49a031086195c1c062154898c3c0c5d1e04279d1e0567813863122e180310aa78102370701885510a64c6003c00118410ca40f0350a2e0f1e24d0128430d2701a8b11a680f0293c09d004100cc218613cd83035086194f1e0c0d421a03c0a4f0270e679902308a82d0004ab81a87311680f02b400950203c0942586719a94460004a785340422812863700d4599e2478139e0409c229c06a2cc68a03c09c01206210c6060661180330a22540382808c299e4009c10235c0d4488e53d2815ea180ac249e24d013b47409c258811467812b8600cc289e04e01684904301484b187990310449802b08eb8128811aa38cf1e6848138410d67812b83c0050251809c3088b152e181e04214c38843c28402708218202909a0800291809c35913001830404211c3ab03008c298d13c205027043000270921ac5082200d421806410e03309a1d4489853ce0e0330a27933a04e12cf025102781027408c23b805a204002b1920800333c0d5c2406614410005679c02909b19d0275c094318e114781ab8380cc28be7409cf02d3c095c0005612460804008159e0527a502b08e284002514e01a9404a1ccf0a00a8e0250aa18c498b11408178006679c1c0661443a9e000ac11204a48102508e2815b805b314031042815aa04e1cc832062114719a93c290e027747812fe),
  (0x23f68e9e2da8a2e07a80ade3e757db3c69759ea66b58e0598d51851bd3c64c2d286460cfa83a04e0e34bcb8a2b3c8e2212c61610142ba08d4000, 14, 0xe0606610e1606a14c38860810100052114358810810c0230a610b02308a1030330963c501e4c0d42590500c42284140890210862930270aa09d02709609d027180ac349532099d02b7c09c10c056124508c51808603308e1920330aa31903508a3c5e400670011bc05229802309633504a04e99002f0aa40128a05281aa6042194226066281286780f01484d14f0f0257c9812a67c09423be74095d3e04a11c602915e484ba98b14181a9404ac0198a04f01a84d0c23c500a04a8010234009433be062f9003140a9f20052801586d1222cc7a842009411204e1820210aa28a0405a154328f12480118205648139214981385500301384b15218202909ac01882000c482a06215491004698502718981384b112304a2ad34c41f3a04e10480254cc81a8511963130254c3012847112b8a02909b6900276c0952200576812875040a504a480d427da04b6ad0204a14ed029d8c019851156b60293c901aae04a18c578c14c9ad03509299326780b42487310e988021740c5803510699e031809920290a21cc52604e10d202d2169935a0621276264c90158490e224d30c7c10e0310aa281589314e30d324056f2d02709223512a0404012841147813da056785027000ac32a024d812843207813851152b900a300c421ae04a2045aa134c0b6035b48102406615433a05c0d6d0270ca3c491a6b409012062105064300ac28b2b409c228b522648d32005b6905a05211505a0536812867197b131604610438ec4c0853580469ae02308b6920210aa34460406200803108a2882606211530804228128672408128430c9018b204a1d4b98414201382000a460270d618202909a3cc006080842ab03008c298b1140811901040148a04e0860004e124358c11ea0191c046c81484042254589c50400199e06a09c02f380cc388a14d01385504481384900b01384b3ce01484d3c40118452c27931e7070188530d222cf3805613450a3c09c219e5008dc0290da79a3a04e104f0253c0a5c1c066144759e3cd0158410848f0350a618cf0804211cf36200d421865707831404e10c30b00662c5c1e0030139e04a18445b85008c002b0e242633440d9503308718f03140c81185310a3d485b4400b424cc3c09491e0409c22a87009660210ea34491e04200189e582012885809423881500b55031540ac920046a8189204e49702308b31503109a001592946aa4c020000acf0250ea7900213c09502e06615458ac400d4f28640d42986558a0159e580ac229e580ad628056114439090448129204094238a1809460a04a11c44901707814a004a81c1e05211433800060188530cc8198451465b421e0d30108550e200f1c0621540003008c2386b14201382052001588150b920230a33190310922b4f99e000cc8081409c102900401184b142ca61c066134389352ca7811e06a11413806ac0198713cd8118806679a3a04e12cf02524e0168005679f03508e78128c929e685a3e400c553204a14c41a040a8198510db28f035742013841240ac9123c801a8430ce00602709632430405213411e04e1820210aac0198b104781a887409c90204e12df5604e40118691c24800337010169c0661d4589c5),
  (0x147e95ac712212fbe7b7bc81c16de0689b281812b84591a95937e9824a2a3010767a437d9750a0e4b822b8e7059e24a0d0854822a000, 13, 0x1b3e582840276c0a5b02d6c0ac5aa8046f8602308a484a8c87c701ab66008db28046daf0230aa21465b6900ac269517d2121c04a144318893e6b163e046115f2c052146628066a0e0333c08438b6800cc9280521444593510b0502958f81184512331b1e04a12542a38094288731aada628140a440270c210168b56c4813b60521ac20c06211563658084228606ac18286c0ac2086712244db48056b1b4006610c34b6900cef36580a42087158da60356c301884558d81086600c42a893206da402b09ad9f484870128510c624c5484580c6003378b1f0230a2b1f023800d5f2c046c01ade04ad9603509234499bc80b240230921cdf2c6008c2a87198b140350a63143604212d808500ac208751a2da62858b1b02909731402b09a2c4698f56d2019b6604940290821d4488418284027080b411204e101486b1823c420c06211433006214e6365409c20cc04a9140330a2914023500ac34cc319012c80661c6654c809640330e2d922a056105b02554a019b65408c208916091502908a1019985490128606a1cc48bcbd0240270a6f2f02bc0d423d804224c58903797811c06cf0148410e6f1e027809c22de06a24c58de780c4e4006b601887338f2c280476170230a36190230a63547486bcb8138510da595e021397814a804aa190250a670108438f0e035096d8e0350862cc68cc38a01ad87808428893987010d2a0094e2806a14c489c50d8e029082a01289598a0e0213871402108e1d4598d198f2c023980b6c40a408c2a9c5140188550caa2c03109242cb9cc6c086c5838f0138410caa01ad806234ec3604aa141c042a01286712b31436042581a873122a1b362d40128530ea246652a009640330e320e02190095b2805212e4285010b0330aa19d7025146d941606a14db5006611454971),
  (0x1e9eec4f1d3827bb2d60e1eb033716b48d63a7af268885c141e9aeec721b54999ab28563a7a125a8cc42c9e78c5e5ce2148db8176000, 13, 0x261c1409c22cc980810845500a445bc38094e3c04a11d403164a120235c09c3089526609402b30f019c00621d5e1c540a5202d789230290aa19dd2c05299e03308e22ca296198f015206b42003108a20c59cca54012aa7809540350e22ccc2a7809660350e6a141c1409c22a8540813845500a44598980cc269212a2a140804aa019a8140a603309219443a80c00128430d6505e286c08429bc480cc2acc9890198430daf14021989019cc05a1d4e02318aa02023980954283008c23a85c08c228b3216b45e3c4c08422c04c901a8510e64940356ca01a84550f05023240813a80521ac528c178a122450084238751262c663aa4a0e03508a18c44ba500b540290d649b02550a041e06649a027500a4358a51823d662838a010aa380942189516634463c1009443c04a11c40b66cd8602108a1a5b365918148410cad9402909631caac898085436052a81ab65408c26c85008d40290d6444a9cc6c48128404ea1b02150a818855500b45990b993040a04e10432a805649b025500d542a06aa0b02308a2447998950d82035240a603308e001588518249b025980d542a06b3151604a10c368b351314185c094218731122acd8b6900adb361028138410caa015c85060b0250861c44992950d810230c001284b102d9b36540ccb0250c623540450601aae04a1cc418ab2a331403350701ab6500ac208914cf0902150701885312b3134804614c34bc500ac26a64c31e02108619db03518f011a63c08c22889512012b04c701a8450e22ce026798811bc5c08c2288d162f9402d0973143404214d3362409d30250d2d811a6380a532610084219c06a21c69cc4c0a555004a10c46a84c09d41c04e14d41c04611465ab190d931c05a14c38c84c0a425a66ca0198436ca01584d681140604214d41c04ea8169c04a24471909082030350a610e0293808902700301384910270128cb22331403350901ab6500ac208919931d4804614c34ba500b540290d6e9402d74f812be7409423a8740d6602d0d23c5f2805a12d40a74095d0270e33143a06214c3acc05aa1d0235030002508e18455ba98a019a850901a847540b5202516238c84b6980a64286c08520350e224db285029402508229b02d0aa2c469a805721b0a05a146436140b428b6580b4228a76ca019a8540d68025509012a404e1ac689034121050606a14c2240529011204e00602709220520251964456046c09c26ac9808d648046b180230a224c64b6580c411204eb01486180c0188531d6b020c06210d636046b14023092b190235809c3a8f3581019ac6408d60270d22b5b2c062b2430062155b0605a11c59ac05242d72b681201285310d816b6056c062806a10543006a11451911),
  (0x10227f2bf79efaf6476fbb19c3ae16707b62990ec6e633b1817febf85f8afa96eeb164afa440eb26b02bb91886e22020be850012e000, 13, 0x143a04a90e0270a7f93243809c29a874d0138450d690e02778e9a1e06211c32a8480c5c1c06211c49a43809de3c3c09d42406215449a6680acf03170701885314bf9e3c50d1d02574d0128471122ad41c06214d4284c094f03378a1d3404e1143488b1c2f202438094218737871e02d0a61a478a83c09d47e78a120310a6794027380d432fefdf9e1e052e013b83c09ce2404e14449cc8021403508ef010a40622cc42806af01488500d5e08047001286914ea04025780a543a6809d40290ca22c40a04e10c90cc5020109c06aa121c04a10c368d3780a488bc78981084580c0188537849b02508a0502108aa019895789019a8380d422a8c40d570250d23c4d1bc78e9f02708219540c0009c2286950c018a8600c4238932d73233a6c09d402b8c094408b18cf010a8540c42a89324f010a850205027240a492805212e603318a3848a926cf013845980d542a54a0108470ea24c88bc1009d402b7900e0310a61d5e3c4808c24bc040a5e02d3808dd2c052201386b1ca50413c06af093e04ef016861100a452c004f013c006a1954243809c2a8711e6f2003350a020a04e10432a8480d4298d15130c1604a10c3888d993090204e10432a8052a142406a14540251264adb3a700c420d6052f1c28640d428863126f013806a10eb02b80e2002770086b02b10ae1e03550c81a853780b458a814085402b980c5e28062c94100521043a8b3),
  (0xf26ea1d56ce3cdccc3cbccb5caeca7ca0c99c92c8bc84c7dc76c6fc68c4fc12bf9bbca3b9267b76a24fd41e417296007000, 12, 0x25c06218c0310a670202738481885510a1020206212446a05a20203108e215b3a04a08202908e22c30804a10302309ac0004052701a86512244de1e056e0e0310a730f2406214c33fe044818fe6df827efdfbf04fdfbf046d2019bc51001a8437c0ac11204ee1b03500e01a843000943006214c31c0621145aa878781285150301284b240b5b363808c22869103015b604a0943006210c202b11239d0084101820210aa1cc11204a48102508e1016a850301284b0809c44b050701a8450e664443604618208141019847043000270921ac628e122aa0203560101098600b421a8381010ae380b42189514a4ccb8c078f1b025092f1d2c0529813865116385e38480cc21b6c40d4259c50b81a84b0ca445e3a6809c22bc00f0148450d6f013c06a11d43605620502774981384f10a30491b6780d4f3c05212d440900842aa438094288a326701e2674f81484b7c29302b09219de0331ca405e3c5470128430e624403c000adb023780811bc04ef1f0310009c358c5787815b62409de025780d444bc1009e04804215522a04e70128711c66cc128066f0402709f01e28900bc2188740a453405211c4004c09c2786b780cc8296132af1b0293cf01a84b7808f035380cc3188508f01292780d5502378094498c77821e023380d5e24380942186f1a63b558fe),
  (0xaeeac3a62a1397c97596e96792a92391c8616bc69157c53f53843542e41540e40738225b20c19919213112a0a509e007000, 12, 0x143a05ed8188c680d4f022409ce0330e221460206a7012920409c25cc08d81a85150c0188533ca0139c740ac2a885fdfbf1e780cc10276c0d7f3c687940c04e12cf3804e12458a870095d1c6009c2987115b304283c0842a8733c101188701811b805a781089516639543805a2013b42409493404a11c4588180ac24b05020109c06a194499b178d01abc062f1b3a04ae9b02508e22de3c68094288404e20c11e053001a8c50094e0350e2f0108f37901e021480c439fe6d21828380d42287112611b0293cd81a8472408cf4c040a42abe056d8138a5283f8902063f813650c0188533ca0139c24081384b0ea29400606a0980333809438b65009421e78094289204094248a75030128c5009423840522acc084240c4303308701a8473cd814a804ef142406214ce02712bf82040cc0188531809c902b16a08234062a180310a678202738481585510bf8216066c02027c80cc206066c013871240ac7afe),
  (0x1e68ed6f0fb65393cb7ad3da80b3fe9f2cf7a7af31c927c57a1d6f8e796b5d97c6aaa51ba32101a77632791887061de02e811000e000, 13, 0x8a1f02180ac208677c094202d1a2f9e0210ca81885512649e0210c109120409c25a61409c62604e12c2033152414909556c4813bc04a101a8c540d542a080842a8651664c5e4c046f13080009c2186110b0134006a11532806b001286778c011b0800b4258912a6f02362420148470d6205e2604ea01ab006224c226780b5e2605a11c44844c0c4328180a530605a11c488b31d6481027080b440004e12450a8640d421a658100202d08ad83035086a030250961040a04e10198c0400148470d631470cc080b42025606011844808c302b0daa120c056f1402b08eb8118b578a015840c0ac239c0462b4b2a134e30144006a11544006a11de28046f015b4ac0a5602bacd0148471029e03308e1b4829613cf01a887809de0350d6f1e360009493604a11c478a94870138432266c603c50e9a02708aa014800462ac60bc50e120330aa701288378701984b1e3f8112057fbf0278a0f02909679e02b08e2c5c1e04e48e2404e14c388ad993011204a48102508ea0148b11962141e04215583c04214459882408c436046115428107819b4500a4258851423566306070138410e6246634a408da3204611444c6500b425921008542810b01392052481027500a435cc066394809352421b02708b301aa854a010aa38094218951664c5e40056b2628380c42986b113326080809c20cc05a21560804a21602508ea01aa8380d661804730b02308a23468973993090204e10432a8052a1428380d4288651264ad4041028102908f3019800562946088980d5436042a0129c06a24e64c4808c29cc3808c228ad51314185c094218731122ad08881008128470c11a2c240a4f0330ce49a027180a4358e52024d5b0805e101ab06070138410e6344234a408da3204611444be0c0b42592080d5b2804e101a881409c902924301482ac0a42388b1ca50490606ac141c06a114388808a8e0270861d44093300d9b387478168470c230158a51ab21830380842287112721b38680ac2386170d81ab038c0118450e62c40360622013840820102b0430158491022946a880448108436c181185560c0e02108a1c4898878f1d3404e11435bc78b1302708a1ac4490f7810934052115a0a04ad01586718238de123c0bdb025800d5e282c0d422b07809423a438094268f12c664e00418095e3c74d01384b0ca22460a8780d44243809c26a405624c6888680ac41205611eb3e04f30118693c0818b8240adf02978e8402d0ab18158871c2494f0606a79c02308ac0428046701a86512244cf36ac09d031096195c02d6c09c6a822409e602b3c4810270a219461886c0d6428056e01286360214023380d43289126608902b5079d03508e0812b6),
  (0x22e887de0887c65e28732dc46696598c638d8285d6d658559d356494d1bc429cfb63c34e6433d4c3a2c4ca221e4c67e14cc4300e1c2a804e4000, 14, 0x530159881a012853780c44abc480b5b0294c7816ba580a423bc04a2ac80e254a260210aa1ccc3cd130108550e621660a3809c20cc04b30c28052106602511b3012a04e106602998094559b198f03035981811841123326243008c2a87114081488500b4238005628499cc78c81acc0421c4232380b4288631cb3050216c0ae608180ac2086724a01abe540d42889398d94031640d4398856c4834c04215438cc98a8c0230aa1c4112500b4238005620489cc080adb4c066c8b023640a6602112a34482cc70e950237570118451222ce638056135d4c1408421ba74a01185574c01185116731d02280d421ba04eea80230a234c72ba5808e60290d73264c640cc21865981202406214c31cc04a29d202b29a286023140011845080c420606a9150230a2281023640d4328f34d3016cc7cf9302308af930237c094338d3380b485cc109814cc04a18490606ad8a03508a99a021380d4388f3103011880008c228406210303538a811851100811b206a19479ac58181a85358b1b023280d4398856c10128c5849b0270973011885600d46991158e1402308ad818b858da603108a18d030062c8128751e6d9c2a06214c35be6cb0108517cb01ab804ae160a04211433b6046f9c02309ad814be6c99203109218db4c046c9f0290aa21463650c0188437c0a44abe6cc8148430ca41d802d456dcd61204ee260350a2e014b63c09426ac70a81885558f811cc062e0e0310aa29489b8983010855584811b806ac260216009c388d3193012b60809428ac0c0d580316cb010cc102813920409c25cc04628468b206a494c9ac7c0a464c04ad818ac0c0d5803198c81a84516640db306409429b605223460406219803128c040a04e481027096204588c5226a0f32062154f4c05ba900233c09434ca500a4258e13ca011a83c0b4f2405a7012801809c208a31d6a1b02150094f34ac09d402d500ac40b2062788023640c43293531329b0253c0d5430066145e347409c25ec4008c249e04a305e404c09e5025940af5280561265462409c80250c220caaca3cf013845500cd94c04215468aa3cf013845d1301085551c01ac65409f402d807013a80561a740251c24c5e1e3c20108550ca78f08042155e02510f3016a8200b425a83c901a84b3809441a8200d542004612e33a04ea016a805620541e06a40109004621543206ad810a851a0118530d6a19035500ad902310a54564ca500c603c409810d206219c448b5787811a8640d428885684813a4062b812a80522ad42a056a2803508b28f3c04e11562604f28128756c0b5b02b203b252004240128636d481ab204a1c474ca50d8f0270821cdb28066114832062e93027044813849500b5402b200947093520c8188a1009c202d044813801809c2488b2009480840400148410809420270c1010843008d90290e6c820212c08c32911800a003508ef933a05611de0297848118534ce814ba180a425be4c0ac23bc05a394d0bc6c09de03578c011853162f2002800d422b006224de244c09530a04a11c41bc6c0c533a180a427be7c981484f0ce314859a1),
  (0x19d6c84dfd2e2b582a63cfea5ef19a878bce9d46d8e618a9e94e6a36517a7c93d69ae4d3a4d11ca7f4342972898e43016988a824e000, 13, 0x83c200b5c3604ad0108637c0ac69bc700d584c380d42287316241c60056e0128804301484b0c2402023200a436933c01811b804a3260255c0d4398d1055818b804ae1c1258d0198510c6214538c080c5c1c06214cf02d16ae2b0237009c636062c019875d80b00230a679e30066154388cb4ce014cc056b0f0350a209c0357008119c06a1c4599453c0b4638042e1c0405a124398470e093404a10c349c06a2cc688c98095e03170d011aa062f014b65c0d5e0210cae0e0310964cc64c04a1018e070095c6004a11e60404e4810250a220c330062c81284042254c9b86c08e60c06730128710810503304001484b10301584718218202160601185312211904380cc2687110a7d5e38380cc28bc4ce81384b70095b1e05a00158691c319d2c056f01686770095e363c0ade0250e6245c3c056125e3804f3017bc10e813bc04a29b0250962846ab871201084748701285316270de38380cc28be7409de02d70095c0005612460bc7009db1204ef01286920e01184d20e019b8380cc2880658302a06214c338831424ade606c0adc0296da8158477809460bc74c1e0297009c38c67070188550cb81c02538a9e02508e1c456983366f2603370d1d0270920015b804af1c0297821e02508e18c569417900302f04e01a845106f1b6a04ef0128694871e2a04611c3088b2266c7f3a68e81384970097f1e7809d33804a14ff284c901885364097f347409d43c3c09d20350e6245902574d012b8066f0e0330a2f1424056701286378e133804a11da3a04ee01286b182e0e3805a14c3894970f011bc500c5e38380c42a87368e8138413ce018b8480c4298852d6f1424056701286311af1c3c05611dc02d1129b03c0478012e0c0f0118450ce32e63cc0901884b0e6225e3c7ce81384178096602915649b025782810cc04a1d451a87009580337808448cc7918102108f1812e0540c42a8d399801584d24d9e02708a49e021980c439cc505012cc0421c662a062284027240a411204f301486b500b6602520254ceab804e015849c0d81884378095c4005330e0350a224df1204ee014e00470019bc70f013b806a1cc42b878f3002108e18e61c06a14c68bc1530128404f3011204e1066025980a455a82809429955993120350a73143206a14c328d1),
  (0x1826b76d5b2963408970c9ba26afd86f5b23975eaf44b9a298e6e5382358e7853629412b88f84261c40d5869028613c09a8470152000, 13, 0x1e36046101a8a1009c1001809c2486b0809460cc0c5012840421d581804731916046154328b3262f0002b1531a02108f301288378e0e0330861c5e4c06609c035380cc38823c0b4902770094438580bc23bc04a22c809a978a1c025380cc38bc3c0b5e02768e813b804ae01488b1c33303804ae3002508e24e602d7131c1c06214c3488b70e1402d08e4a608500b42387520d81984518731a021980966029116e2602160e01085312331a2a046d1902308a24e66005613494c06ab04027240ac94c056125402d71301a84520249c3604e116603350e012cc042a819895222b163804ea01a87304281492180a42388158e013cc0573261804614d902b11a3c66385809d4031640d4498a598e034c04215438cc9872602b0ab31c02909a2c45020520015861982260290ab31402909b3261806210c3590746730202b713010b298701984d0ea2c472b8700812847701011b85848149e05ad0202d08ed09027180a43590108094a999570781ab6700d580330c62c5f347d8018e05408c29bec00c702e04614c42915256d1c023c00b4349eb4a012b206a1c4f4a05758f3e06a11c349e04a10168e124101aba1009c902905581492180a42388b080b5c0406a114a0b67009c304042154938080b42a8656130e03508a1cca8b81808db3806a14dc386cdb002108e1d703604a701a8731c6445c0405a08f02d0920860290973020256c0cc936680cc2a8404a20471b6700d5803370d9906600cc2386312a284888a3ce01184d71301884640c42a8853cf1e340461043a8a04ae183c04a14c3890770d1d0274cb0138497009457bc78e01a851d4e040270aad812a40622cc819cb70f1c02909b31c035086f1e347409c20bc04a225c2406614475cc20095c383cd01a8410cee1f02109634dc6c98094e0350e6245b4c20095c0330d6e180330a2e1a1e05a15410c052cb060600c42986710632c90b40878102508ed017b470095c34c00ac29b60c0bc23806a11da0336810188868e019e004eba67006611c38b87131c035981013b83cc0118510e6f8f03109610f0257020f029082e1f0210962cdc307008429871),
  (0x210281ae02e7f35f4879eddae721dbba6cd59a2635567c574d4be4ea525e42e5046391cd9e2da4a9c24fc8cc1edc720167c4c00eac26003c4000, 14, 0x131e1408dc0350e67a51e04e0814ae06a20c589e94d812ca04e1acf2e04e2815828da0198550e298f031047813b806ad920295c094388d32132614046e033804a124358b31ab30f02b5d3170270821d458cc055812d60409423a6700ac26900427ab3806ac8158631125ce64c0c0cc2acc05b3260606612435ccacb81aae0561cc48cc9938a0230aa1cc12e06a1446280201819ae062284027000b411204e001486b18241903308a5d564e600cc2ad65008d6029980b5602514339602158b1b3a04e10435ac58a0118410d2c018ac7c301a84358c01aac58c8118550d22c482a13993920230a338e02308a2b505a04ae018b8600c429b820d81384dac0aeb0295008dc0251c2e262c04ae01686b703015b898b01684b0ca29e638600cc2aa8042c8128a3589812ccb409428b87cd1302d0a6e012881640c5c12042e012b206221d6380638019cc04b33002508e32d0aa899ce180310a6e1a1204e12eb28046126602d7009470cc700c5c4c5008da1204e12c40b87c08c60210cac003206a11c38973713015ce0461a562c0009c24a0b40975031600cd6362409c25d65008c24906c09eb0290dab01292136ab26325008590250da20d63204612d6027409c20ac04ae304c04eb0128731173016ccb409590350e2625f2c042f814be7008423be04b39e3404e106602d40c0198519d2180330a219644c046125f4e600cd502d50c01884164094618eb4aab140337c09483804adab02508e23d63804e31d1e04e104398c056a083604e10436d670b013841000ac603314b31f02b918015d6980ac238c04b30168d321359f025996812be0421cd94c042154788a1009ed0257c0a6602bc008d9566c09df0250c223642c7c0a5c3e06211df0257c0aca0604e10c80be1478138417c0ae63006a145f5a5c0d4288657d826027096fa602b7d801584710b301190990f94021600c59025106c0158cd5e60063206208902720101384d1420138005a00158891809490975001800210a200a0004214432803008c10405a1040006458118550e22140006400158550e201903109a324e9bc7d2933a052e81587510e40128d36cf09023149813855040a533a180a42386b2021012bc05ad831404a15580337808458bc4c095e26066f0128676cf81aba04e781288b78f052604e1043182080d450270caf1e3e06a981386178095f3a04ef0128c05223c95bc0c0d4a025600cdb3c05e10468be78095f02046f0128677c0c5f600638153ec00a7002b0da244598f5947ad03350095903512329e2604e986027096f2503508a325f04240cc239004a20cb092080d490405a2930274c301384b112f0203508a405b1204e181ab0066f2603328a81985510a10109314cf130254cf012847480b455a699001aec2808c2289378f1202b0a6f13025086f1e2405614d33c04a10c539513d2326025080c5e2604a99e02508e481025087302027082192031640943a973),
  (0x1facf78fa43c83d74d72e98330387ebcfd68295f3be9a5c8922f6ffa78db861abacc65d8ab914768de31594107ba33412183e0056000, 13, 0x98d042406a10da02568d013206a10c3288722730e02b09b31a4e680c42287398701584d6131a489c0942a871126d264c2008423b41008128410c6018b204a1d46992398701584d3c48003108678f3604210cf480467950230a278f28300c42186711a44cba9e0530188433c7970310861d4f4c640d42186924a79a4c06200148613c095a4c05358002908b58002969301484510e701693339731a021ac181a9c062784027640d4328d39931a02108b3260804211431404a156b1e056701a82380d4228b12a67800333c0a5a0a04679a2a04614c38c63c0c5a14046d2e0230a224c629c05a62e32c04ab2302508ed0f0a0467818875112d1a00700cc21867380b455b43c1040310824012927c0c520353c094f48640d4228671e658da1e1008423c63cc8198550ca780021000cc359293c7990250927941806210cf02510e701590d00202023104011845000b458800c0d4e2a0467013871100811b206a19489ba4c09533a04a11c002d240010310921ac90a04320a0250aaa810230a234e63aa408dd3204611449cc540ac26ba9930802108e494035540c502a06212dd020433013b206b38e031096314b99c398a81584d8cf014c604a8188434cf018c66408c29885540b485cc20095d02125301a927808c90270d299d0a04211c90351008c5292000a425ba05a6c492604218a0250aa0150350a234e63a042e930254ce8128478d4811b88c58118510ca2ac99cc540ac26cc24181a9298205027092184a03514a3ce62a0673153204e10d33a06a124508f17519d02575181284711719502b94101284940942388919a9a53a74981484b7808d3025142e0e0310a6455d04046e890270a2e8802308ae81021740949027000a455ba000c432a062c812875166009000840128510c622c90606aa81892102813841640d4428f3992900359c09550311262810d620101aca04e1cc449e047810845040019851981819ae0622ab02d69301184710241903308a08a02d5409c83206611400291967d4f020467816b89878198430d71a30204214cf0233c0b454803c4011b20661d4429e040a4f0205279b2406210c368b33c98199e8c78168490ea294f360527800290a69812cc00a380310aa1cc81e06611461ae05a62d83da4c094f32046134f1e040a4299eac0a422ae05a32d35a04a78169e5c0b6b0204a124458e73c08f00066146606066ba60210a241903308a35491d604e016aa04e79903308a2d400291d758f487009429ae062254f4a05330119e04a206b02b0428f1c04211cf700422813865e00ac74b0e00af80290dba1b3004a12c318a3c7840210aa19c1023040a414c50c0188530c600148ab3c401a8028b8188550e629642e062c81286d9958f021707018b8380c423895ace0e0310861ac99cc540ac269e8cc819843),
  (0x15f8af8d5faaef4f2a3fd1e28e346aa0dcc1a59328c942c8da21efc4706b741adecea5c6aa7140a7f436699689b23c41698788326000, 13, 0xfd39603190c0188538d1990330aa197f30480ce30252ca810270a6a980330aa2c520804ec016aa05318129e6009421fefdf8c2e8c0c633206a14c42cc20096302b8d18502108718149e4c09400270da3c634831181685164096302b16a34d20804e90188804a28e0315c09e303330623085c09d90330ea214c24300cc28c65c0cc22c60572270258c5a31405614c3089119b1a90236118108455c0ac5482000c6648066426027142013c63008c298891a24230311028138005a185903318a75413205a001486b040830358c501a84512208002b0820010004a10662e04a0980236409436829808d902d0d24440005408c26900809c24805c0c4228eb4a6e9c26480cc2886d4ce019a6740ade2a06610c48ba4c0c533c4c0b421b8480c4298b5ac0ac50005b59c0605614c302d11299c03308a0051406a14c318a000b413a04ae8102508e2252240408c2287326331e2606a9a30294ce814845116f133a056e2302b08a22453cc700ac269b34ce019a6700ade2a046f1702308a08158a91e33263a042116602978281082780c5e20540c42187514f3016828d381685574181684778a120310861a485c69d38a0230961d663c040ad90230ea246624056134a2b5398e810ba0c0d429ba200a5d1406a14c42ba740015849040b5d36052401286300901a85326331d3aa4c81284398e01584d16a34e63a0008c20ba980b5d209c0942aaa04b81a8450e210502508240dd3a5090188430eae812ba74c8118450ce901692b4e699c0334c99202909a9011a64c901484d04b81a84314a4c5c4674095d4604a11c448ab8d30103114e81682000a42588120081084522a0831404a15402406a14459801410118a2008c228005a2c400606a9122a04611c388a0408d90350ca44da40d409631c0661444688000b6b3404ad2b02508ed2b025acd012847112001192b0c501288695812d6680942388b0c501284d1d270e0204611438993),
  (0x186eb64d882a83462970c77a1fef90722b70190ec4a591a7a92827f63ca9ad8bae4321c487d81c20da057825808e04001c80c800e000, 13, 0x2600056401480067301029000ac50804e0814802010138490d600128f32822a61004a14c31404a0010a43008d92e056114498f52a2d2602d9901a2a046146734b808c28865480b47990b053054c04b31602909a20414c05212c7acc913812a4066b01089516331e2604ae130205214435a678095c26040a42886b14f31c02b09a64e6384c08428824c0d533004614642605212d326380d42888040ac208a78c9931c056145902312a29509cc3808dc0290db3014806a14c14c05331902b09aa8118b1991990350a619450804f301282056204130062c244e04a14d24c04b30138711ab32402309a09802d600a43582981818cc280c422895993261804615438cc6531702309a1d442cc04c8128430c25cc13205b3011cc9008c258a9ad59b56200a425ba05ad930233c79b02d6c0a43789318e554b080ac0ac22b6ac18a025086a81989516200f0313d581025087012031640943a8d3984012d60c0d4a0250e3581025000d402406a144598a20d813ac0521b5b1204e001486b0009480a6ac0adc2e0621353384ca818853003013860622019881647015845247593100624020274c094308ab700b474b67558159e6c0b4238936c0a6b0a740cc802f0c2d8138a3ac00168456d5831404a10d503312a2c5d26740ac22a6740add0250ce99c02b70701884911b308025709810851ac99b2605212c41205611c5a82000d422a620e014b604e981288115a98e0350a27cc5568008c25ae6409570270da2ab029ad0011900521aeb0a580a4208004a19203328b819845122435b360c0d402a06a14449b6102813b605a00158816d3018b206a1cc8280980815849ac1800210aa1c404c5460118550e208802b200b493605a101586718254eb4c06608a0355c581185312208003508241664c0c0d550310e7326081409c2082062c81a8b318b3260606a146b4c06b31530046154388b30808414c05aa813cc0c08c248ab053018cc64b811b20521c44a82980cc00290c249666004b1a41404a15439c605719d02d0118402108619d82405a14e3465c0d4298652a3fa346600cc2abe4c0c6340740c562406214c4afefdf9f6006b1819fe),
  (0x78ef0fdbbb3f60e2388303ddcb636aac8d8aabf56296d267b6f51b9b6c616c1175ae45bab5967ac84f298093800, 11, 0x3f12040c7f025918902b0aa98102b08e1854c05608802b092001280240812849000ac43921041920310a6c81288d4c481aac800aeb03159301aa604ff962604bf931206b1813fe8c98903508a0a61004a0031404a10c39cc040ae502d4d581a8454cb01280040ac2a8870008002b48b81285312a2a4e8fe589813a4066996027096c812fe589813a65809c25a4066c812fe044818fefdf807e011810310c081685312a0890270428902d9809400271020814820c9018b204a18c49820c0cc0109809424801408c00290ce30485cc2009661098094268004e089025240812847000a45593114001886480c59025000844a8d3),
  (0x11ae882bcf1db6d00619af91772bb25b1ac5158aabe55ba7f13c68e0463a2b90be6ba26693187aa3861bf89183ee1ba0d986b000e000, 13, 0x2b0406358803108b5830350428139406a19550311a732b0a040aeb029200b44120524815b605a21c80933215850006a10439885ac085027ac0cc32d61808400270c61ab021295815845540cc5a99178f1302108ae131c06a14439a698e133006214dc2405a12c40211aac8e02b08a48e6268cd1c02d0a69812881707019851715810b804a98e0310a629e6262010138410c622d0aa2914985347409d602d4c094448a11a6e0e0330a29831c05a10c35ac8c0d40027acd01384b68e814c606359d560498128510009c4ac674095346ac0ac2886758d01acc06381d03508bfa30298b013849c13013c6740c42488b58c81280480cc2388d0448138a580a484028094298631409d0250409c34807530128470d6401680480d4299514c481a822409c12c06249203309b80158a580ce66004b01c6a05a114398a3140a60256d20159005b59d02b08b59d0296cdab029096401688518e584daac0009520350e68c564c04a2a66004a281087312229b3a04ae9b02508f00a0250a690188e922b3260a580cc22ac000c660250cf00118f5200a495cc801811a4062c81289315a9932c05331c033c0e019845106981023040a403a4c0942386b4c701a8532229ab029589813de05a1cc426998012ac0c0d411406a114498c34d19d02575181284711629b0214c094002700701a8531865c5c260429931c06a14c38a67098109c0621cff7e6cd016c604a0013cc044811851c009445ac4c09d60318060188554d0013b206a194898290f812e4b80942888d000030230a61ac84fe),
  (0x15b0a71d25284339c94cc659ee6e3a677b0d16cea2e432a17904281a3dc9ec8f327923bc9dc8ed671c31594a074e36a14e8938272000, 13, 0x4cd2503108698138a0529850a040c42986710b31c1c06214c3aa6594819c6640cc2289538a818e206b72303380f81985110a9a603504981025082e0e2404e1443a8d3982030350a73262a04614e61c640b42986b1a33004c4c0ac10230e2c81a8b318ac26060461366241009442404a11d802d0ce012cc6c085502798094488c92e662e6260c0d660604610448cc98c01185198901184b4d30e3205a1443acc0562a4236056284027980ac348a13e73130290408e60004215401464701685398c81184116a344b2a67008d31e6c09c26a604a98f3a04e105302511698e0350a2981027408c23a6056b0168a119284c10a06a9819b89980129c06a1cc48824c98f3604e12530251262ac538052135b0a05ae8138004a20cc0ac7d5813a6052b012ca0662ad32c052e121c04e14c388a314981ab66ce8118474c09440a67070198550e2e133804612c34a68c0aeb26052115b2605a1014a604a20eb260522812a614401a8450c631d64c04ae0e0310aa24d3024c781984b24d81584715229c02909a293033142013827409c2488118628003308a9960606a08a03508a20e62604e901aae380bc228b32a3f961e740ac29a604bf961e0669812b28090198470e3f8f2604bf9a2604a9bf3a68095c0334c70198514ce1202b3809431a67079302508ed1d0274c094358c17071c02d0a61c4a48a4c08532668e8138410d69814a604a9852c05210436933709810a6380d42989114001982ac08db3a04e14c5000661146080200a42584000cc50004a29602f092204668a5818a0250861d452e04614c68be580a403a04e14d63eac09c802b58095d2c05a14c64ac000cc36a04ab81987114698503304d8148551409564c04a4032406214c8320661145a8a05581384b14094802d0558158004a0013889242282023140019c00c0b4a0255c0cc48ac040d5d02714b01484d00401484b14001580066194a0a0f),
  (0x1b50cf9e60306b77ab71d78297341093ec9da4bb256927c69a146f5874eb3515869424289b40be25ea2a992a877226e0d986201be000, 13, 0x498502909609c03508698126200a5b0270d621e027700a4368e10009454c04e901ae0380d4e02d0ca344f99e3c99c1c06214c3488b4ce01584d713011a64cd1d027096185326380d4258714808d3264c701a84b0e270118a536731c0404210dc02d1129a526940b6502994f011a6052981288b1c2e0e0310a655521c04e0814b85cf0138004a18446b07008c25824c401484b700b5334200aeb3c06611d300066114608e3049815b85c0cc2189104d019ba04e9812a6200a425b805a0930294cd0802b7809c00251022cc71a670b8198430e2d2b025acd012847680a6b2a05619c025540c4348ad9959d0804f5815861ac4813849ac4020270821b49990ac9800350821cc42d60d58108557009c03508f5815885aca81a853263f8112057fbf0258981385124901984d4cb013e04c09c2488b6409664c044812920409423891980b6024062c81287326a9053205a11664004612c548a980cc502580b6b3a06611c448a980cc228e114181a8a700d422ae4c084298d199001190052901688b4ce1e0a0809c21a604a2045abc980b5302578701a853162f082606211450404b30002d08e089025240812847000a45592178981386000c425865cc815a67809cc0230d22c466a6789818847640d4429d3980015900408424801420138205218400250020108004a1b4000200a4202700094408ab3669a61004a14c30004250002108a71902900b81484b3058128431a6554d8ccace84027ac0aeb0291033016cc24d8138410c75934c06a10432993ad19302708358128698085c4c042115503316a4c66384c701a8530e299b1204e125302568f013a6052981288b08b01484d2829ab0334c09c1025980d453806a98e0350a62445347409d30254c0a44584700a42686480cda3605a11eb3206a114619a14d31336056d816b64c0ad602d0d298128e14ce011a43809c2989132a11300141014851040018c8480c590250ea2cc81b639731027000943588960d814b25cd8138410c62b41044808c28b6480a5836052136638066c240336c0c6368066114508e32ea9854c05e0831404a154388a304981aa6380d4288a6c0b5b26056e01686948d813c6640d4228832426cdf2605731c0314cc01885312af963605a11da0234c09450a670d818843589812a66c0b423be98e163004e701287312228c65cc1008660c05213664c6c0842486b981811867009533006a14c448d1),
  (0x1a8ad41e91b47fa26cebe232f376f2adcd1ba6b33528e8c72a36317489bc041d66d8c5cfaa293329023d298d8a6636a0d0866819a000, 13, 0x3f1e480c5b02764097f1e4c0953363c09428b8380c429a64c79b0270829812b8380cc28b87070198514cd010a604ae0e0330a229c849d54ce1202d380943188b4c28118804e09302970081084311698f3604eb014a604a205c1c06614476d668095a5604a11da029ac9015c07009520310d22b454c20096b0331420138004a18461d66c086b025580a44680909019b204a1d448aaad00118490d64000331420138005641b02709a0883604e12c3490000cc229410520a0250aab8198a8c0a4002b0c23c53564c09d30358ce0e0310a61a465a64c99c0234c09433a60622cdc1c062125c02b25bf824806640a03308b28f0298c0d400278c09450c6589812c605a1d630298d3160250ab18148878c901ac6640d422893363f962604a99b02bac181185340b1f023800b439c6911920350a21cc54c04e10159004718148a1981190350a69960278c0a630358c0c450905040054605610802508624414806a9002406a11c3882000c590350ca44cd4809008d902b909018b204a1a46682600c5848d009580210e6280025000b401c6c0b4208a000b4228a704c016b00521acb89f5140a6023040943582000ac24820c5012800421d44882000d40243008c2a87100019160461443a885142013820520a4029096d81680040ad90230ca485298a6c981984398e0e0330a2d9b1e046e81586700095b3a4c09423ac05a98158a92826d56263c084219e05a996027580cdd02b11299c023acf812b006a70168931a2985560567810cc8c0ac22cc7070188530ea40d3347409c25a604b301484700a4268aac0bc1025980c6638380cc288a0cd81984b3ce815847280946093534732b566c08c9027147813cc0561a460d615301a8410cb301697305581386980842a8a9d58158550cb3150350a64c660a980ac01e2408c288670c90188551e73261e0622a602b08e0811b206a34c728a993050804e14e602d6c0ac508d5981920330aa1c663205b30330066144202110632454c0520811cc000a42acc647011b205330108951625145022409c24a65879b0270a61a445a604ae016a614d013887809c26881142013a620f0138410de2ac00252c69813805f330025380d4398a31a29930420095c0330c6293027040a403c046981286b4c701a85322228e027040a584004612d638e0b015bc04e184068046114698ed),
  (0x14eaa29ccb250727c916c77a1fef6c7a0b74990ec145d0ad0159a994490a4691ba8103869948b764ca2198e2850e09a04981a00c2000, 13, 0x1356062e131e042701887312b59c02d7008c34a6ac0ae6104c0d420b89c084288a3ac98e0350a211c029ac0adb1e240ac238004a20c70953ace131c06214ce02b1069ad2604e14d92604211454a6998019a605e98002508e9ab0297098e0330a21b5326080d530250c69930004611433d64c00118417070188551675815a63c0b53025ad58f3604e12c39d604ae0168c94d5818cc4c0bdc0310ea9822a06a70128713c08902709201303108a284999c3089813a6062413021ad801a82700d422893089812a60809423a6380d429a65c0cd70270da4c415604b58102508eb8168005232c800066284027000ac802d044813900561a480006611490d60c0d413806a11570334d58148005618488d6ace0f02d0821a5c26056a8168714ca818b84c0b501e047581586914298e023715815a6380c421889718016a64c701a8510c758e02d09699338ac701a8530e2514035100cc308e34ce0f033082e0e02d0a2e1c1c05a14433d624084259494cc8f02109b59c02370701384d11299c26380cc28d60569ab56940d4298805a226b2671a019851104814841640946a8e34cc8f0216409c36ce4c095c031acc81a853100030350a218481d66448108430d699c0334c78118406a1131e04615432d605358e0350a64c6b364c0b531006a11441a605359c1c06215439804c0d53566c08eb1e046114488a9100013a62408128430e2e0e0310aa3ce62620981a843ac0a440b85558e03508a1c449a6ac0ce62605a9813b8540c429a6640cc228f5ac0ac026000b415604b58102508e10802508632488880c0d55031000818b206a19469824d3011860621d5c1404611415604b58102508e00302309232eb0006a284027080b4100052481386b182015180461543882000d4032380b42a87114a84ff2c6c0d53025fc996027800c4f3604e14dc025),
  (0x24508e9e292890e1e2813dfee7e7de78773dc966f25aea670d7e85d454f850f52bc4774fcc37c4da23354be4262c80a16c43d60e1c22a05bc000, 14, 0x716816be700b424da056e1c3006214d40216409451be7cd818b850e01284f0c22a543e640a42284700c54383c08425b0062c8128b31c6555928b40ac20da6408c22b8640c5410046106d32046115c0406ab140350a23142870781084f0c625543006a14479b8180adc567c09d90350de225c3e500cc23da700c590330ea30cc2b2516818da056186d3205a11545a04b808029640b431be500b5f02558a01784b7ca142c04a11c398428a01385150b08021096c018b204a2cc8a98370a1f1204ee0128405622450a81809421c06a14449ac58f89027080ad4033102b012ccb40959035080ac4894998a033006614542405a12d90251aa38c92c7009c209204aa015840524940350a2a0602508a81a851126a142804084248659810128c056a0188c504011841600c590251664d41000523030405a14c33860008581804614c48806408202d082c860004e12c34960463d482d61429a02308e18665605758540056d013b47809c268a11a60012d6acb080337809eb0251022ad602d1d35830352809422406a9012873ac08478aef794990250860ab025ac08128475c0b400291962a6027995813849ac001384bc04010845ac0812e00c08f002b28094002116a3c45003c084239000f0108470db59a1204e104002d11380802900101084711758002108ab855605210438a73155a50310aa2a502994d0108606aa818d6640d4228c32275850a6808c23861ac12b02b0835812d6ac29a02708218d602d9828138451d332b1004219203365601684512a30c78a4f6959a0256958128470420138006618471d6480ae06a04a901886915b5ab14056135a00640cc2686569581280640ac26887141018aa066008031640cc328c314d012b41409423820009400270c2d2b025acd01284711619203164094369c915301182ac096b0204a11c00291560831404a00108751235800351420202d08e089027000a4358c10090c0230aa1c410006a01916046154388a5426d1338056e0e03109223450a4c09c21a67008c25a63cd813ac05298128817070198511da99c02b4ce019d615881a843ac096b5600b81a8430ca21c88b8380c4269894c98f3604e13430a604ae014b84c7016b80521cdc26380b429b805221c88cc700c4814062116b3006319903508a24c50804e3030350a200a03508a304e1d67090169c04a08902708228c6590000cc50804e0015906c09c268220d81384b0d240003308a504148000842ac67000108550cab9302104b81a849126545d020469a43804a14c3aba4c09533a04a11c01c052134008000942386126321c02d740010c805a195d000432016c8700b4228a74ce812ba4c094238890400603308a10c0335c094388c35169814c046081286b0400158490418002128001084512a2c410006a284027040ac148056125b02d0009470803808002b092c816982c094218d51e284da26700adc1c06212446a64d5819801420138550c228d31e7809d60294c09440b8380cdc1c06611c4892dace05021480b4e0251062ac03806a9841e05a104e2a04614459d6704810843700b444a6000b530251000168417019c02509b581025600d4398d11830002308ec030230a20ab025ac08128472408455949),
  (0x272097e64d28b9617682edfb8745dbcc6d1da7a66258bc5e0d614524d35a47f50c43bece2e35ccbf22c948841e4c53a11fc3fa09e418804e4000, 14, 0x58a033006614547005a12d9025186b1f1204ea019a805620542e0661456285c0cc2886529339f2c4c09d40357c0a562804ea1e0230aa234899217c327029086195f2864c0138530ea24753e04ab130254cb0128479c0a4a0316d2018ac5009c20a87c0a427ea5040118410ca4acfabe9c0c580357ca143a0461243a8819969f02f0a2c81a8852e6a0202350094a03158e012b8580942394062a0158c950a05023082b1c027500d434b85809c1023180d442b00625cda2c6809561c056135a2c04ab0e02b09a21c8ab4080b4248c68181a85300d0a0350a6195a341009c102508c0e0250a61d46184380cc269313c79b02108679d2a06210c39b43c08ca02d0d678404056104f2a05614c539e3c18158535008cf300467930c04e104e033116344a49e04781a8433c50118493d3171c05a1543189124d0139c05a7990330922ace28c101011a81809c2689110a030230aa7150230a22cd40004620802318a01384d122201023640d4399257cf014be7cf018d264094298839c0b465bc9cf01021600c439a8640d4228c37cf011204e10431ce05a2a5d0c7c4020277409439889156e883604e2812861106e9e023b40ad903512251802200b420b004ac090405a105802510e44c51405a301586958fab0270933811a85010168470e6a0603308ab142c04a14c35ac7ce017ccb409429b206a28c68be7ca1f02509619dc4e04ea019a818e0158530cae263006a14ed3206a1145896308e014be6c08421b8600cc288cd7cc81ab8080b4602b0c2e16031500d5c4e046105f5604e13c62806ae27023600d4388b350a0603570b81185112629514ac640d5f3605a10564e7c0ac21a8066b164e04611d43006615458ac5050188c5c0c42988314a72562c2408d40310ceb1f023500c432ce58a1803164094318939c0b6728480c429ce640c570230caa0148eb36b39403170494035600c5f00062c81a8651863ce702d9ca018a8600c5c2804e135c300621146990b9d39402b09339c0219cb010ce05219c52d6500d542a06a14544e500ad80230e2225f280633950316408c3a8a5513950230a339702308a2b529a8040854025180ad40405aa0148c04a24e71004ac81a8c042245a40540c5a0256959703108a19c61ce5c0c672e06211c469e047810845043019a804a1c482c140a5b02b0c21980310a641903308a1030335c0c5a12580a42586120c81984520e85403e04af8002508e7814ba9c0b6400180c422d264094298a31d6781023040a4f3e05279f0293c0b4398b53c08149e040a4299e6c90188430da39cf3806679f0293c70f02d0a61d4e0231a2414f0204278139e50c0188430e678828640d42986310a01f0277c0013845112b8169eb3d38f02505281284b11278f4e04b28102509622453ce5c0c672e06211c469e3cd8158413c1980310961ccf04042a180313c0b4398a33c79b2406210c3488042a8602909639c81406678f0204611c34b805a7942e06a10c389e712860290c0b401c06a11c588d31d681652c0627a43804a14d703112a7a502b580a670233c09450ac0009414e06a14e72e06b38802508224561e3c20108550ce0811820520800290412703150c018853106b0148c7216788035505170310aa1cc52c85c0c590250da314025201819ae06228602d04001484b1048602909619c7090640cc2299564a2d02b08369902d08ae1403350b010d67c09c2488558f81184b50b1902908a10a03150b08021096c018b204a2cc71955),
  (0x20cc7e95f567c1de3a70ed99a62158005f556f6585d5fe57dd4f44f7d2ee47f511e4414fde3bb4e323594c2c26bc89a1eec56211c435c0334000, 14, 0x4b0002909ab161005213c35ac6c2816ba04eb1f02d08a28461ac8120169404ab81988316319602958e813853d40b56026c0a42aac04ba816ac20a019a4062b0802d05581384b50d940330861a560252025d564070095703359a9703308a10324066155602510e3b4a882580ad60317c08d60a05a14c03a580ad602d58281684516a31c10005ae813ac04ab0802f0963252084241ab0210aa1c48025809ca56042154488a5acb01a8a1009c20822409c259258a01a8430c0ac44900809eb0290dab090c04612520351220ab031640d440a04e48159205220403206a10c22e062b81386d30aecd62c7090169c04a1c441ac68e813a605ab012b805600118c1707019b8380cc238912d2b0814062c819ba74b015849200b4408f5b4e920310a6b272c0676812b206225563a06ba9602759a8002308e1c4549005a40564e58c81886140cc20895146b1d100562816ac04a204a2e06614474ac740d562c20181884358b120350a2b1d02b58a013a85809c2a8891824cf8065808c2486d581011ac056b1203128181984111a1963a200ac502d0c224d7480424015ae04a244949059a81a85159a8159005ba9602b092b0002560d8902718094308951865cd64e58a010b20621d441ac7cd9d0270a61856025280b4802b28b819851252416025808c2482580a542c04a10c459005a4456402809520310ea24d61206ab0840280942986358d090275809435b42409d602b5008d6025152b14025480d439ae05a6c562c6ce8138415809444ac200a4258c05ab0303558501a8455cb0108511a6b273806769c03308a20d63804ea01aac04ab0e0350a6345c2c5009c10290c73ad025700cd42c04a70198711aaa16025096108025503012a81440168450cea14120409c20865500a45595158a01ab0062b1402b640d4328d358103033500b431801809c50804e14c40ac04001685520101384b152b0300042181387508c1202b0aa1cc788058401985158081094062c840c05a28102908e204598c0009d70330840138491566d5028404e014805212c226052135438052301286322a4cdc4c042f8e03598701a84512634544c06209403550c01a851126a020317c2050270820815b206a2cc728204f8188537d3019845992018ce600c429849c0c5f3206214c42915080854020421982a05a14c388064b8168550ca40df0298c81884d0ea12602d08731f4804211e40237d301384519662755a0576814b6500ced0250dba86021b4a010d60576950270a2c8128d3206d9b081409c20b605a215b28062a152e04a1443ab654c8128430da44db2805aa01486b241030310aa3020204214483604ea08021086089027000b434b0062454b9801809c3023540b480204610138691d600110066144814062c819875240813b61808c80270da28460004eb819842009c248ab40ab092805212d44c500cc80c066115903116a30d432062c81286d),
  (0x20607edde4873f5aa463fd8565c2d4a04a3d19e3f54ee434fcc182c9ca121fbc6fe16844f80d4c34c0bac2e40a9c2a009d426e08c41e203c4000, 14, 0x712816ca052a015ca780ac80250c6e141c06a14439827008c03e04ee012b8046e0802f09232c160200a425b805ab13025700d5703168f1803108ec9f02d08a284919b3589812b806ae170330a2981035680cc90270033003308e401488b7009443c04af0402508ee0148ad38210906ac0842a87120e01027715810855122296b3806ae8402708248159270a01a8430c0ac44900809eb0290dac1502b0a2e01027000c59087409db1004e13490c04612460aa056454b2b3378e012b8062b1302570e1a1204e105c02511381e0290963d5e1c06ab815ae04e245c387808c23b85008c20b84808c259c04a43559bc70096d2604ae01a873783016b804af0e0350a62c5e280828138450c2f1403120a090204e105402912229475bc7009d4035600c5c3c04ea018b206a214898c701019851701140005214c318a1009c402d040a440801818198472010138491561800216060118531228d5c1405a008031640d439881409c402d1808c10291423000275c0cc21004e124559e504e0139204a1033804a146602112b59c0357420138416c481384b24e14035086181588909301484d60a815851700813cc062c9a3a04e30118405a205502b1aa49579ac70b0e0350a61c56362409c24b804a11302909ad1e027580a56025116504202700a429ac7070198550e22933406a11da3a04eb01486b7009470acac0cdf025580d5638380cc2a87108e01488600c403206a114418c135ae1603158e0e0330a21d5636056d9602b092a180316409431b64c0a4269210809c0350a2b161c06a14439ac6c0a5602b14c81286600cc238831c2b012c066e0e0330aa245b3805221803100c81a845106304b6ac5880158514cb0202b0a2b01388550e013ac040c422b8380c42aa605ab1c2c04e1143495358b1b0350a209c035480c5c28046e013ac04ab1928600c42386312a404b9a8980c442806aa1c1204611d803512234d40406231c0204614540275070188551a64142040ce0128516131903508ad8108931d6a020270cc1202d0a61c4100062c8e02d0aa21491840ce012cc0421c5c0a0422013cc05a1815b006272632140842a86710a54ce4b858b0e0350a21cd60205279d027580a5602511679b0274c0a5602511a50412c4c0a426ac70b0f3604e13c39ac04a2a465ac58e0168477012d025380d4398913d21d03308e50128812c699c02358d94023082b012b85809c24ac380d428913580890275809434ac4c79b0275809439889156b1638052b0f03500301a84510630476ac80181782700d42284b4094e0350e638c88fe58e9a3a04e12439a6580cc22fe3cc013a6640cc22fe807819b804bf9a40740cc23b804ae9a025700cd61c066145638480ace0250c6b1c1e5809423b47409d60250d6305c1c700b429871292e1602358d1d027082b014ac04a2adc384c08561c06a14c458b148e01484d),
  (0x228e83edfc278bddaa744dc586c7d8485c8561e4e8531c498515e41b4f8e3abce1831ccbee2a8ca6628a498023a481c1c1c52c10ec26002a4000, 14, 0x136004699a0214c097046ac09e602b0c380e26056901187112781c1c06214d302b5c08c529b54138135204612703204611456a6c008e6600661353347409c20a604b812031c09962406210c3988bc0e0e0310a6b8118852aa72421004b026023c00b66480521040001408c2286b2220050804e0814861000943243008d71604611448805c90138430c2454d9cc80d1502368b8118451222ce640056135a4c912040204a11ce0351222cc61cc900ac26cc902840270832150230a32242e04614432cc900ac26953913244c0560800250862045ac8980c644c90a818ae04a18c46cc90c190250a218e402d156554c9c8800d601e05a14cf4a052d0109e800d4f56480d42487116640169279130149e900d580310e628cf340427ab40480c42a8691264016c03c0b423c8000c4832066c81687514671645605358002908b5a402501581284910e181692b3d2015c8980ac802590c0188090b8188550ca2cc81c890b81884d3c0010c8000c42988b1d278f1e3808c228713cc811847909814d6d80a422d69009762604a124439405a4acf4c0c0cc21c805a78f4c046104f3004678139e4808c248b322240f1e0c08c238733d20119e7008c2a8893c0170350861c4b2d6901816d6900b422d6900b640605a114439154c0013804c09c2288935758f40480c4298758080119e04a186b02b612015c03c094f4004a11c51c04fc012861e00ae402d25320f02121004027900ae40005612660231824012915900172e90084238751222cc0100008430335c284027082b812ae05ab811204e1057025000a45595136b2127004bc016c801c0128490d63553460578137005b181586112a3452460560011a406202403148a811849912260239009640311122ac99a6e18019a494a81984bc12013a60561a460915489126005213438a49808d26005213443a490a813a65520138410ca9800210923ce600c00d429e04c181a8530cb80302309a44505cc48085262a009430330d332a02909a34664c4808c29cc4808425a4493010847548030230ab3262405213643206a10c52a40c0a5002d0d65cce8ccc46012c80661c66629409640330e2aa62a042155548042a813c8480864025900ac498f1006018a4000b551805a12552404a181a8711e61810004a0013800522040060860198430c58118604e194668f10411c0310aad9b383ce8158410ce30128a358701a851226d9302d580adb3805e10c548404481386980842aac9d30108550ca3c4904540c426ac5090188551800b0350a21946192580d451e04a78502508e204302b980b562a06a144a4a73513161e04e4811a406a24c58a8080c461e0622813a80408c25b206a34c8284582840251028128476c0ac508405a3cc2045008c23cc0c0cc258404301a8430cb3016929081a60210aac1202d0a60191c046c814cc04225452951580811ac7009c29a65932d0250a21cc47ac04b0f03309649b02b08e2a5c025700b5c0a6809c43c04e13440b8480cc28b2380ac2292346ab1c2c380c429ac68e813ac04a1ad6029700b460935),
  (0x110c828bcf1d26d3667cb3c98dac425ccac515f6abe55baa3150aa5a4eaa4b112a86a3d79b40bbe5242348e286be2800eb85480c2000, 13, 0x818011804903002d040ac15605612400278009470915262020031c09018855580819c806ae813c004a0002404614c02e05211455c0c00bc26981ac1018d6c00c422d6050013d605619432a06215469d6140815d6052209029240ac338c1ac101a85101220027200d438885ad001086540c6b2e4809c2186116a3cdf4c052b012aa0671963e06b3014ac04aea02e4809c28875126fa602b740c66400660170335808438be58097002b940c5803315301f2e06a146024046e815be7409c248a1d8a815ec750019a40621d606c15c01a851fd21d02b9809e00c9809570350e30202404e145d02b102b304004215603a04303002d000ad20335c0945a8f17d02624066b81287112a992023740adf029103b131e04611533a180a425c07d001a8450c69a60352009533004614c58868028108c0561a4302319801484d9980802308ac000216009c398d1800815c004a0814c0044813c004a18441ac980970031809018853580b46a80800ce02e06a14564068481384b8009640004e124688e1c101b3a04e1260025580ac50c0c00b4002b00901a8531630130274d3080250a21d6440380d428a604e81384b00094102914244f656380d428a64d0014006a124318938099b033ac09c30c004b308025380cc3a91181001027093b201204210c35ecc09019ae04a1c44aec80081884380097660480cd70250e225404c2009428c0980013822409490204a11c458c10c0010a45c094288952e73136006af13025380d4388b3),
  (0x12aa912c7a237b138850bec1dc6e82707b5999c2c5c606acb923a82c3829928a2250a25d928888243a1fe8fd874e34614e850007a000, 13, 0x1260533190330ab01a2605212da023102db6029d809d3025113360330ab01b4c057013031640d4398a36c9815849982010cc6c08660290d69a602b653010855126c15264809c2286b98198303808c23a41009db2a04e126602515640498955049814cc640cc2aa468981484b696015a606619d31c06211480b6497930230961a533204614ef62062c9703108a9936c06215430c06c98e0350a61c60364c0ac24a4a0094e02d0c630412606298102508fb2802598c81885312a981023980b12006741903308a20c588d5998a80254cc81a8531233120804e106602598d810cc053301288b4d3015b26530138410ea2ce64c9008c22a60521a60a052da602909620138606602603308a4049acc9931803364094318959930e0330aa1ae6263930158550e622434c4870128530c730148ad4622844006611e40298079d0274c0a530251022ad3266c9019ae04a18c4a8b14d201584200960033480c44a8274081a8474c0b600254c9850804e901a8735c094518cb2c301b3a4c0cc23a604a98148a14c99b02d38901385312a2c53042009600330eb024025480d438a6044813c004a1a5302b4c2812c0380c554004a11c498c32c3f9d34052a813a0380cc229c4809cf20480c429a07070188530cbf962a06298e03308bf9a3a480cc23a0380cc22ba6809530318098e0350a21cd3263cd1d02709618444a604b0130213890138511269934040701885368e81384180e0e0310a619530292570050804e10431c0810120230a219e02e04611466a75010018e0480c42a82ac08db3a04e14f002d800940408cb812a404e18c448ab2c321b5605212e0025),
  (0x21387f25eea7afddbc7405b38688d8fc5c3d5c451e53884c552a2479d1084134f0239f4c002da497c1fa46b0166c43e0e0c2a407a4188040c000, 14, 0x141020204211434840800108450d6105033640c420a6c0a660405212c4984280a4269004690188a640ac229613aa203023644020270825014b204a2b59022409c00c04e12440b204a32c50604270188a0c50128514891902909a18c031086299160461543286080b410005212c4099300181980380ac412040942188084012843380cc4a8e926301b2604a9842004a10c358a14d001a9e800cdd02b6c09440a66c0bd30330d249e02604f2017cc4d0013b605e1b44aa64c90e0250861d449971915813c004b31b0a0535815923c0a423cc04a3047ad68008432a06331202308225469cc8078129e80094238605a2ae60614181a8450e73262405614c22a06609703508a20c789698132648046114348614da6029096226029980cc338004a3848acc989019855993120350a619e64c600cc03206a114418a90d3121c04a14c31cc0522b508c04c0cc21004b00198754d20129c06a1c60022409d30250d29815bc14d013a406a1cd31c06a11461961809816c04c09d62406214ce02514701a3a04e9812a6052205326380d429a64c701a8530ce346002d3169b00234c9a502d940a652605212d33c05290e02d0a620e51c046114ba99190c016a4b948138804a1ac44e00478133c0467012c8200b424b0056305360380c42ac8c00b5302b69581abc05698e03508a28c80a6c070188554cd019c8c00b42a9204e9812a678a8199c04a18c4594168d2b025acd01284711758302bc0a818e0540c42388919a99d0211009eb02bac4813849ac101a851009a4027200d438885ac981086540c6b1c5409c2186116a3cf03c4c09420a6780015a604a701989516201e0314d8018845c001e0606a12c38a60018e0310961d442822409490204a11c40993789812a67809423809809c20e078095e6004a11c46a6780c533c04af1302508e24c65a0900c019945c0c4228839902602d810011204e1060025116901a8d122701002398d9d0270833012e04090188538d5813841c100e0310a61948a989c102902309381902308a2b664cc03010ac480c429887c0b8188451c7001692b4c0050804e08148610009459ccc009664805210431c06214c6a80080120270a219702908a28c65865c1815b0640942189115b5a6035142013b62409c25d604a4a602b6c09e6025112486b26042195031987150270861845a8f34d013347409d30250d2284027086d1e0274c0a5302511650600405a7120270a6244fac04cd1d0274c095302911e2ad30a6809c00250c359302f90096003512640d340980d5324380942a8731463464266c0adb2604a98158691429a03605a90e0250a625458c06c981584980d2003308218128834cd811c04c08d21c04a154498d14d301ac02498158204a701a8914cd12035b0094318812669b603594b812aa9409423891813011c8480c534004a90e0250aa20469cc9820128606a18138939930302b09a49203504b81a84510730e4c05a14c34951),
  (0x18dac18e0aaf03756b7ada0aa273ec998c991ff2f2c726af416069b84879fe8f5678036b9af8d4a5b42bb93c87de3d61ba8b78296000, 13, 0x2d32066b1d0a05a155e2c04e12d64a052401a865202e9d0c740ad4025780c6d0c042ea302708ac81a8b324769f03524095e3a0536920350a609703108b69e2806211544e052f120330a220c53c7c08424bc50b013840030138490c6284658ab40d453e052b1402709620480231ca2960004a0810869640d459bc1408c8025140cc50205200502909628a02d0809c502512640453c2009429b206a28108b13cb018a0500b4838066115703116ae963c0467812869102b1e20380c4299e640cc228b5580a671e0473813ce6408c228ad147813ac05278f06066125402312a7803806a14c329e3c901a8530429a0290aa7812881147ab02109278129e480d4298c7480b4e89e00b0202308e184f1004611401e05380a02508690188b32d6b000253c19c0250a6b81889574e932c04e12c34bc04678128c150f0f0253c78e0290a61acf3c04a78f1c05214c358a750781484d32278f342409c2086b3cb0324062154358933c10109ec00d520310e628cf24062134f280469018805809c258a93c40119e3c08a03508619c49b805a7880233c9016a404e1cc589e700120350a21cc45a05144030335c0c4502000a4258424301484b0ce304832066114baac64326027082c812bc4930108556009c459035921d02758d81a853102b0129405a101584640d42894960d82035092e860297c0adf00056e814867640cc72ba00b012ac000942388b581023a7c09df3a04e12c428a1640cc7a909289018b204e1b5b4a04ac133206611c34b63c001484558e819ac04e1120330aaf860004ef81486b640cc52ba180d553204ae9d261809dd0250d6254202d08e9b0217409438ba6c0018847640d4499037cd81592500ac23827409de02b600ccf12062b819b604e21563e7409d402b0d2b019ac50e9f0270aaa01588914af160250809d42406214c51be740c464a7809c24ba062b980270a611602d640cdd2c06631e0a052144358405a3042609c09429ac0009573a04215448bc5800158533cb0158473cb015ac000ac238850808ca4e09c095604480a4a02b0e6244668a781010847c08422889781010ac08301084308001084714a3ac52c00095b0210d2c923204a1043a8f3),
  (0x173cb91da7ad2f690afcd61a80b14084bc049bbad1067bb3c19aec88640b1e97c6af24169b40a7a4ca2228ba04a218406d830807a000, 13, 0x201018a6740a420355809c828066c0189c04e22ff7e4cb1302b7009df0405690138691a241903308b20e6204671702308a24642805212ed0874d0138490cb6b02805ae0128735c0c5d2604f6812da056f1d027b4096d02b112da628052144602720094519a14aa29f0a04e1156265008c228c100011847740ac408a05219c14046e016b8052214599b57c30128c04efa41204a2090204a12c338b31822814887c0add0257421f02b08a19c20804a10c602d143015b63c09421889480cceab117431e0314c181ab804ac01889318e9a02708a18491bc044813a8052185e02578a01ab00621cc50a0808c23bc7c08424bc18006027092184458ab40d440212008c42881409c60c24d0138410ca2243382808dc02b0ca25560a056901a8c04290e0234809d32406a124529314e63020314c181ab804ac018893743011ba680a5d3405611c428c1044815fe24081aac04a019855249819845fdf962604e996027096481482480d428e0640cc22822409490204a11d402979801285150a0e0350a22042805610168751123cd60c04228148a780b5e02b0808448a60808420310008c40a04e10158691ca116031083015845140a423e04a301886370a0a02508619c02509619c0259c0a436a40624d580408c8118550ca2814b42409463404a11c459216a63050606a14c53005a302023600cc35b004e34460a04e30168c0564011801409c6120409c2086b640d46996578b2724066c016b204a25440a04e10a0250aa20491ce58b1f0210aac018ac75201384158901885514b3816ac1809c25993352e963c046b0802308a22403206a14d63c0633983a04214439bc01a0198430d229e46ac09c20869780160404611c3088b1442b4604e10434ac0009c80230d639452c0408400250d2c81a8b3b40860359409434ba00b0138557968128491572963206a14dd005809c25ba7808c24ca74f8139005618c42921b4016027096e9b03578901984b191813ae05619474ba7c0b5e32067688023580c5636080d424865182b9e3a062c019867),
  (0x17a8bc7dddadbf582a5acfea7331f484bbdc1d46de862ab06162aa484a2a3d91ba86a4049f30f4271c30c90205e624a09a808000e000, 13, 0x4c2812be9809c13a04ef8002b40f8202d0a619c5aba580d422ce58b163605e1143888178901aac04e8138517c1016855580ade025593816bc05640003514094318c93427cc13a04ef0159e04af1f4a04f2816ca7c09c258b53cb01a845226d163a06a11cf0257d1816bc480d423ac140a570310ca3cde0c056f018ac04ab0002508ef0f0255808413a04ef014bc5809d60290d6b1f0005200a02909ab165a05213c202711640499ba0409d6033140ac42ac6408c28ab55800128a20b0108530e2405033640c45001430198471409445901409426c87409c8025280cc802b152604faba0c0b5d3a480a42687175a816ba74901484d0e2295b6806610dd3e04ef814be06650168ab74f816be05769b0a50301384b0d240128a1740813b206a1cc91907cc81a8531429602d7c0a5f02b04e813843200947a90114f9d021280cc3a8a7c0a5f02b7c29f0297c0ac32a406a2cc88be7c1015be04a1c5f3206a14c602000d422861246f9903309ab1d0a04e115d02b58b1d0a04e11434ba062e940335009d828052b1202508ef2d025480cc368f1286b1d5a04ae9e02909728168b128c01885358e940230a6e8128810131d02b780b438ba940ac229460e9202708a1c449ba000b4924180a42a863142b020354c0aed0404e116d3c06b6a502b580c6636052f160310aa2156347409c2aac780a425ca04ad9e3a06211d80331929b02708ab013a04e155e2c04e12e500b40d4288651529648056d814d658e81884b0ce304802522ab250315830188004ac81a8831a62802c04ab0002508e23460004ae820230a222413a04ae8102508e296031092b05029080c43192b142813a1808c2387100094548224095d0204a11c45b2140842a99314b0002504084348a00b012ac0009423840462ac5033640c451405a00158a04a204caba500b5d3e04af9d02508ee8e02d092345f2805a12dd284c90198516409446da90e012853749019ae04a1c5f36046a06027092e8128a12d62840277c0a5f0c080c433006214df1e0525180310a600108a524652c33804ac01886d201018fe),
  (0x1e9ee34e7fb0d7720b5fd73a9073c89c5cd3a4731b4897be29c12d60691b399712b82590a8c12368603db98489d646618488182de000, 13, 0x40a0662010805a12430880c20108550820109c06a1cc68881409c438062124a02d3890138a5c0c42489324af08025101818a4066005100809c2986910221c031480cc32955316b1628280c42186510f0303158094348870819c0250a2b270230922ad62c1808424ac6d30148410d699d023580d660c05610453ac90281a8430cab0e0350a284d604100a560250c338e0330a233703804ae3002508e20158c000942184100842888c00d5c025100844023c0e012b8c0094239c06a70159204094e0350c64c4e988102010006210c328870818a0250a228108848c81284348da6029082901288b481040290821b4a99d568e960310aae9a2606215432ac380cdc2c05ab1d3404a10d63c3c09421873196b1c0214c701a8531226253264c701584d0e699326380ac2687310ee133c480c4299e380c4228a34cd1d02708298129c0662acb4b874d012a6780d4f0250e6b0e0330a238d61c066b01486d58d1d0270929812b47409d60294c0953380429962668e8138414c094458a91a2e133c04698f02308a235c1c06a144e02b226a130275809531e380c429a0600c4238b558a13027480d5002d12698f1c06214c329e38e013855780ad01c062135e061009c20ba580c5c2406214c4a8e370f1c0210a6e0e027380b438bc6808de26380cc21871156594f265809c209e04a78e0330a2e0f0233c0b4349e3cd1d0270821a4f1e380a4298713c78f1c05214c38885487012843356e1c3a6809562604a145e1c06214c6a8e378701884d7899602709a7812a65809de02d3c095c383ce0108517870188533c9960273c0a4f02510278e0330a23b4ca9e3cd1d0270821a4f0253c70198511d67040a0c084299c38901384b0e2e9602900f08025580cd90310c48199404a1847a90364ca6021640943388d58c864c04e10590255c281084b186b243a04e7819909809c25ac04a304a2e06614494ac8cb0a02b09a1c632c58501584d0e221d646056c816869584164605b1814c605719d027086b0128e1640cc9a8a151810210931a30204210e300046114558a8c0a6302d8c0ac5460531816c605612302508631ca8a551519d0004610438b206a2cc514046ca60216409436ac040840025640d44480001050c04214c31889002819845640c485a85809cf025acfa602709a79d03508a2cd62c5808188490c6e812ba580a563c7409560330d222d90317cb0158058501784d0d2e9f02308e28129013eae800c04a30002508e22dd02958f1d10056115d033640c490a04a1047a903640b5d2c04eda35a0576816cc04e254598a3c0a42282740ad602758e8178496cb1e029096b01982580ac01405ab0102f09622460ac0409c50330cac992404e10438a15),
  (0x263693ae3b28b9619a7ddde987805c386c458dc5ff56a055e54e24fc525e46450a03e2cee23a04d6c3354b1e27dc888194c5860ef42de052c000, 14, 0xf60500b003508a19cf28480d429871989019ae04a184a1a83cd090270827812a8480c4298d5500a48588100811845500d4428066a0202350094428056124e0331aa445448056a012a4380b42188052305e260628083806611606a04a13570319480802508698148812aa993200521353200628101c052144398c24901a8530c698f0314080e0290a21cc802640d42986320a82d40806af083e7409c2087111769002314986027096101188119278802108a2940354cf013c80c0d421bc3c09c268c50ca01484b1168159c06a7014a810084e0350ca3c51988940a652805212e5208c481384b20094408a378a141c06a1443189310810120409c80290ca2045aa85c98108550e221402350701884d784233a04e104389e2008422a8512010a804a701a8911665a54200808421a850a0e0230a21a449a820a0e0310a618c4296b1010302d200800290821ac80250cb818853104012902430148412009445865c0c42990742ab062806610d62006612d62c7408c2588400ace0330ea345020380cc2886d5831f031086b140230c0cce2c04e1445a9e580cd01c06212446a63c0c432c6c08ce0350e224c65a453cd062006615531270d8158550e6214719e3ca9a1c06a114318931623261e9808c208653c1850210aa1ccf061930138450c27891e0520812a406a20d202b1a654431e480cc2886d10281588140ac00250c628303510084398808201085538901588140ac1025480d4418d326290e02538901284754c014b05409430330e22b5324056913584008c28c0b00c429d80c0b6c0314c7818b206618c629753129af025bc981284710a019a44810e03308619c48a49008d22e640cc2187514a5aef2804aa030250a620109c5c70198450e242522849610023b0096c2e04a11ec029196a0169115160188532ea21448100a420a804a255204046a015ae04aa040213871202108e1d4599313d78149e06378f2006a78f32046154328a93c181484b3d60119e6808c22de06a2c4d9a448a01184548181a8534892402308ab840210aa2c440606621702510581a85312218306380b4288650818c0310a61812860400b0330aa194439031018199c0c0b42888b68b012ac6809423b405219c02558701985111ae962806208902708220d63c744810853202819845146b0302358701a85358299035086194789a9593010ac04a2014a870094e0330e23b5628280952109809c20a404a24c61ac04e8138805a426027096b0128c150e012ae0661c4a4ac70b0138510448138410808dc2c7009c28920409c2090046314028380c590250ea24c42870094269c06200158a914a014a8100a42588700a561404612c4288500a56040c0c42186b14a015b81008c2488524ea1c02509a0050351008402d09330138005628128c13808109c04a7013a40562c4d98850201085550115033086a012e06a10c32a8380cc269c0564c440404601602709620308042154388858001384b28201085114a2052c0561452035101013820030138490d62844020460040210a2901a8a53a6b130259881c025380c531c056134598d598f180237870118451262a5e0858ea402708af960250aa2a56001809c50250c622ca0ac1009c33804a125606280942186b58701a853262f0e02b380a436a0100a5010700cc2286b407019c8500a4212180a425867142e0e03314481027180013849116284729d1),
  (0x22c486760887ea5eb87525cd670b5b0667359366115646559d41c4ea52dc49a50a03c7ce4035ccc3a2a54938211c5b813ac4300a7411c0214000, 14, 0x9d3833e0533816875180ac50ce1048148806a29a029100d4338c11ca20603364b0108551229a5029800ced2604b0340335c094e02d12b01302d940ae312d80ac2386980094709b1813a04e06300e0310a6254f4e06338198692173a00339c0a6002b11bc362604b001ac65409e0025e00b4408f3390018f04db013c004a1cc458c99c7812c00622235604e126002501001484b0800189004a18c9088010010218009438889647200270821d489b205a9a50299c4012b0640ac29883640b604e05301302508648159e7c9812ce05618d903316b38f025800c60042009421be000ac602780094448e11102d0314c0810845112c81a8d3640b6708046781288066201080661240080521040250a622c21405213490889c7812853640d44021162f13031950019ae0632a70234c0a600251023d53269c0a426a89d00e0290a70130250873a01c05214d34004a10c539512d7002023780ae0087ce81384b0c302626180ac23861112446008b40ace035380a4488b380401080630013b206a24c51c0380c426a63d0019c0380cc288951566944100c0cd70310820168804e089027003013849116384832066114ca8c3c0d4f0c056d090276c0ccf0253c0ad602d192404f4c1809c64c04e134402514230cf323c0842a8714c309043c09421b206625454b205b00f02d6c78128439c9860273c094358893c4814c006a70188934d00f1c800b42987112a9990230930204018084228698100f3e0429815865113020406c0842286912649e0041800138450c220c4400808c259c06738f0251898129c06a1cc549311010f0204211434843c00108450d73840233c0944033640c44041009c26cc1009425b6280b44025080ac8023152504fa8a0c08d9100809c2094052c8128ad64089027003013849102c8128cb1018a0250a27030230418002b09218590404260b02508623499801009c6025182010860661d4e0310cc01884d1818198c24081284318108025086c0198951e24ac4404c0943033044812920409423880522848a884c30128c4c0942388b4d0012c04c0942388d0840128436098e03508a70148933e2e840c056a012ba0809c83a05211448c82409494804a14431c062154699a30c986025189812847380cc588cd4c98302b09af930250869930605613533e04a10c53a60c701884d7c0ac44a60c2100310aa18d312042993263c08c2887510e31533405698203108699d02b08a99312056144339294d20118a4c50118554c281384b14b0130211408c30251122931204094218694891302108e1d478a534d8011ba74981484b74f013b00667932e06a14ce02d10a38ca8a6c0f011e004b8303c046114338cb987b01c06212c398894c98f02046981886510e78f342409c2086b3c1010843c090188533d80f2405614439ae046294daa60d80a02d08a90188831523040c05212c002514181a853100844261809462604a11c469c052901588080d440a05611450804e0812a406a24c819f1502010a808a81984350097035086194e0291e2eab02950e9e0273c09541c06214c5a8c3),
  (0x21da83a5ff87875c9c6bddaa85e25662569d4c84f5d3ac4b7d21243650303b4ce4e37b4db03464baa2c04938208c78c1c1c4540ef436e0574000, 14, 0x5101408430334811203308eb812ae044813801809c248815c0946595136a2830330c18002308a1ad206480a4258604581a8450860198604a19c61931141011a61809c258a0c20108550e22862604e12ca08042144528a103015851380d440405a2814820030138490d63045020460040210a2701a8a53e67893404a781a8633c2814cc1809c40250c6284f36980a460273c094408ab141850210aa2a70a04215432a4600ac29911142810006210c502710b38f0258138128510818a0250a218c40211470119c6d301484138094e02715670202138095202911a5cd3a8a380d5208046701486b809813ba4c09d902d74a2602d0a61846aa680e81a847640b442b48c085d4005a115d4005ad2302108a21c85a880481084b500c5502d14649402b280b5d2805bb0002109621556c0008540250d621e74018085d02d0e61980330a2784033640c43292351278002b0079a1204e104f02b3c094a02d1aa3a4f109809c40250c220cf00056c8f0210aa2460268d0230310a61d634006612465c6807018849800ac46c08130139004a18e30293d0011c681c01185500b81a845380b468913811814c00400128410c700a0290a70000480094e0330ea20e31c05a12478c6800aec0298d90c023c809438c6813011c0e008c22e405a2a603205614489a4487013b29808590250da2a550064a9902508e1d4498005232c4000408530004211444880010118004a1ac4033640c44001808c259c04a5260804a11c368e136a9890294d3930333c09590312420128411aa38d902d4c1811a65008d30273c9011a66008c258911e699902308a99a1204e78129005650168a1813812ae0661c494be4c09e026600cc2186b4d00e03109a1a4f3206701b0233c095f029102f8f2a640942a8733d00f025082f814a67d0182e04a14431895167006040625180310a620e0007c09c21887c081384b640d4498e57cc81984d7cf9b0237c09438be0409d90350e63a4f268070188550e701a0238009cf02594981484b18301a1204a49a02508f0090204e104318eb8030402b0009431c00808e00250e22200c04602002708a24590351a66a530c04a31302508ec8198ad103130250408434884c30128c4c09423840462ac4033640c441405a00158804a204caa65809562604a11e402b589813a8380c4268896901203109ab1e0233c09601c06214c55ac4cb0002308219560c04698128671021602708b001a89358b0e0330aab02027600cc31ac1409d61c06615561c06613462b42409d63604612561c06a14c93404eb131004611c34a6380d4298e55848102708a18505b915900199e58c0119e4c701a843540ac428d31e2b0f025800ccf300661456263c00118410cab060234c09433c080fa00350861960027166b042c74d8138450d620560c046b0202708a22442c05ab013ce3c09425ac0840128430d270199354a23040606a14c61c06ac016b005610c03308634440c04e30168c0564011880009c6120409c2086b640d469965),
  (0xde37babdbc4582938a5800, 11, 0x285020461154035502140290808c428052114e0331aa3c4548140a440250d6205d605c0c5c36046e812be0562046ac87c21b03514781a84570901a8535030138204a1849195170f811b8480b4288897c3011be7410118470e2e940237c09c32b8480c42994b1800602714094303512691802d184810250863021004a10d803312a3a4988a042e9620046124f02570a0e0350a21cd4204070188533c80e0310a61946ab8500ac24a03c08d00254080f02308a19c668a3ca060004a11c3088b3cd2b0273c101184b10278802308a3a540a0427920351520f025092184588f3)]

def cert_boundsFor (i tok : Nat) :=
  hintedBounds cert_bound_chunks (hintWordAt cert_hint_pages i) tok
def cert_ref := symDagRef cert_mask cert_goal 2599 3 cert_syms cert_trace cert_links
def cert_check : Nat → Bool := fun i => forceW (hintWordAt cert_hint_pages i) (fun code =>
  checkNodeViaF cert_mask cert_goal (hintedBounds cert_bound_chunks code) cert_trace cert_ref i)
set_option maxHeartbeats 0 in
theorem cert_roots : dagCheckRootsF cert_mask cert_goal cert_bounds
    (cert_ref 0) cert_stock 12 = true := by decide +kernel
abbrev MainBlockChecked (lo : Nat) : Prop :=
  treeBlockF lo (min (lo + 16) 2599) cert_check = true

set_option maxHeartbeats 0 in
theorem row0 : MainBlockChecked 0 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row16 : MainBlockChecked 16 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row32 : MainBlockChecked 32 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row48 : MainBlockChecked 48 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row64 : MainBlockChecked 64 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row80 : MainBlockChecked 80 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row96 : MainBlockChecked 96 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row112 : MainBlockChecked 112 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row128 : MainBlockChecked 128 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row144 : MainBlockChecked 144 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row160 : MainBlockChecked 160 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row176 : MainBlockChecked 176 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row192 : MainBlockChecked 192 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row208 : MainBlockChecked 208 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row224 : MainBlockChecked 224 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row240 : MainBlockChecked 240 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row256 : MainBlockChecked 256 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row272 : MainBlockChecked 272 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row288 : MainBlockChecked 288 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row304 : MainBlockChecked 304 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row320 : MainBlockChecked 320 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row336 : MainBlockChecked 336 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row352 : MainBlockChecked 352 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row368 : MainBlockChecked 368 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row384 : MainBlockChecked 384 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row400 : MainBlockChecked 400 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row416 : MainBlockChecked 416 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row432 : MainBlockChecked 432 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row448 : MainBlockChecked 448 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row464 : MainBlockChecked 464 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row480 : MainBlockChecked 480 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row496 : MainBlockChecked 496 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row512 : MainBlockChecked 512 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row528 : MainBlockChecked 528 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row544 : MainBlockChecked 544 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row560 : MainBlockChecked 560 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row576 : MainBlockChecked 576 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row592 : MainBlockChecked 592 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row608 : MainBlockChecked 608 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row624 : MainBlockChecked 624 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row640 : MainBlockChecked 640 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row656 : MainBlockChecked 656 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row672 : MainBlockChecked 672 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row688 : MainBlockChecked 688 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row704 : MainBlockChecked 704 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row720 : MainBlockChecked 720 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row736 : MainBlockChecked 736 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row752 : MainBlockChecked 752 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row768 : MainBlockChecked 768 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row784 : MainBlockChecked 784 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row800 : MainBlockChecked 800 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row816 : MainBlockChecked 816 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row832 : MainBlockChecked 832 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row848 : MainBlockChecked 848 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row864 : MainBlockChecked 864 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row880 : MainBlockChecked 880 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row896 : MainBlockChecked 896 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row912 : MainBlockChecked 912 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row928 : MainBlockChecked 928 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row944 : MainBlockChecked 944 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row960 : MainBlockChecked 960 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row976 : MainBlockChecked 976 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row992 : MainBlockChecked 992 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1008 : MainBlockChecked 1008 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1024 : MainBlockChecked 1024 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1040 : MainBlockChecked 1040 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1056 : MainBlockChecked 1056 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1072 : MainBlockChecked 1072 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1088 : MainBlockChecked 1088 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1104 : MainBlockChecked 1104 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1120 : MainBlockChecked 1120 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1136 : MainBlockChecked 1136 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1152 : MainBlockChecked 1152 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1168 : MainBlockChecked 1168 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1184 : MainBlockChecked 1184 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1200 : MainBlockChecked 1200 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1216 : MainBlockChecked 1216 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1232 : MainBlockChecked 1232 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1248 : MainBlockChecked 1248 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1264 : MainBlockChecked 1264 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1280 : MainBlockChecked 1280 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1296 : MainBlockChecked 1296 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1312 : MainBlockChecked 1312 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1328 : MainBlockChecked 1328 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1344 : MainBlockChecked 1344 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1360 : MainBlockChecked 1360 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1376 : MainBlockChecked 1376 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1392 : MainBlockChecked 1392 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1408 : MainBlockChecked 1408 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1424 : MainBlockChecked 1424 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1440 : MainBlockChecked 1440 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1456 : MainBlockChecked 1456 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1472 : MainBlockChecked 1472 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1488 : MainBlockChecked 1488 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1504 : MainBlockChecked 1504 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1520 : MainBlockChecked 1520 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1536 : MainBlockChecked 1536 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1552 : MainBlockChecked 1552 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1568 : MainBlockChecked 1568 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1584 : MainBlockChecked 1584 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1600 : MainBlockChecked 1600 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1616 : MainBlockChecked 1616 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1632 : MainBlockChecked 1632 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1648 : MainBlockChecked 1648 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1664 : MainBlockChecked 1664 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1680 : MainBlockChecked 1680 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1696 : MainBlockChecked 1696 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1712 : MainBlockChecked 1712 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1728 : MainBlockChecked 1728 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1744 : MainBlockChecked 1744 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1760 : MainBlockChecked 1760 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1776 : MainBlockChecked 1776 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1792 : MainBlockChecked 1792 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1808 : MainBlockChecked 1808 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1824 : MainBlockChecked 1824 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1840 : MainBlockChecked 1840 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1856 : MainBlockChecked 1856 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1872 : MainBlockChecked 1872 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1888 : MainBlockChecked 1888 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1904 : MainBlockChecked 1904 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1920 : MainBlockChecked 1920 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1936 : MainBlockChecked 1936 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1952 : MainBlockChecked 1952 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1968 : MainBlockChecked 1968 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1984 : MainBlockChecked 1984 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2000 : MainBlockChecked 2000 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2016 : MainBlockChecked 2016 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2032 : MainBlockChecked 2032 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2048 : MainBlockChecked 2048 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2064 : MainBlockChecked 2064 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2080 : MainBlockChecked 2080 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2096 : MainBlockChecked 2096 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2112 : MainBlockChecked 2112 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2128 : MainBlockChecked 2128 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2144 : MainBlockChecked 2144 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2160 : MainBlockChecked 2160 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2176 : MainBlockChecked 2176 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2192 : MainBlockChecked 2192 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2208 : MainBlockChecked 2208 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2224 : MainBlockChecked 2224 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2240 : MainBlockChecked 2240 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2256 : MainBlockChecked 2256 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2272 : MainBlockChecked 2272 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2288 : MainBlockChecked 2288 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2304 : MainBlockChecked 2304 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2320 : MainBlockChecked 2320 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2336 : MainBlockChecked 2336 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2352 : MainBlockChecked 2352 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2368 : MainBlockChecked 2368 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2384 : MainBlockChecked 2384 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2400 : MainBlockChecked 2400 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2416 : MainBlockChecked 2416 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2432 : MainBlockChecked 2432 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2448 : MainBlockChecked 2448 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2464 : MainBlockChecked 2464 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2480 : MainBlockChecked 2480 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2496 : MainBlockChecked 2496 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2512 : MainBlockChecked 2512 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2528 : MainBlockChecked 2528 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2544 : MainBlockChecked 2544 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2560 : MainBlockChecked 2560 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2576 : MainBlockChecked 2576 := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2592 : MainBlockChecked 2592 := by decide +kernel
def RangeChecks (check : Nat → Bool) (finish : Nat) :
    List Nat → Nat → Prop
  | [], start => treeBlockF start finish check = true
  | mid :: rest, start =>
    treeBlockF start mid check = true ∧ RangeChecks check finish rest mid

theorem rangeChecks_cover {check : Nat → Bool} {finish : Nat} (cuts : List Nat) {start : Nat}
    (h : RangeChecks check finish cuts start) :
    ∀ i, start ≤ i → i < finish → check i = true := by
  induction cuts generalizing start with
  | nil => exact blockSpec h
  | cons mid rest ih =>
    exact joinBlockSpecs (blockSpec h.1) (ih h.2)

theorem cert_nodes : ∀ i, 0 ≤ i → i < 2599 → cert_check i = true :=
  rangeChecks_cover [16, 32, 48, 64, 80, 96, 112, 128, 144,
    160, 176, 192, 208, 224, 240, 256, 272, 288,
    304, 320, 336, 352, 368, 384, 400, 416, 432,
    448, 464, 480, 496, 512, 528, 544, 560, 576,
    592, 608, 624, 640, 656, 672, 688, 704, 720,
    736, 752, 768, 784, 800, 816, 832, 848, 864,
    880, 896, 912, 928, 944, 960, 976, 992, 1008,
    1024, 1040, 1056, 1072, 1088, 1104, 1120, 1136, 1152,
    1168, 1184, 1200, 1216, 1232, 1248, 1264, 1280, 1296,
    1312, 1328, 1344, 1360, 1376, 1392, 1408, 1424, 1440,
    1456, 1472, 1488, 1504, 1520, 1536, 1552, 1568, 1584,
    1600, 1616, 1632, 1648, 1664, 1680, 1696, 1712, 1728,
    1744, 1760, 1776, 1792, 1808, 1824, 1840, 1856, 1872,
    1888, 1904, 1920, 1936, 1952, 1968, 1984, 2000, 2016,
    2032, 2048, 2064, 2080, 2096, 2112, 2128, 2144, 2160,
    2176, 2192, 2208, 2224, 2240, 2256, 2272, 2288, 2304,
    2320, 2336, 2352, 2368, 2384, 2400, 2416, 2432, 2448,
    2464, 2480, 2496, 2512, 2528, 2544, 2560, 2576, 2592]
    ⟨row0, row16, row32, row48, row64, row80, row96, row112, row128,
    row144, row160, row176, row192, row208, row224, row240, row256, row272,
    row288, row304, row320, row336, row352, row368, row384, row400, row416,
    row432, row448, row464, row480, row496, row512, row528, row544, row560,
    row576, row592, row608, row624, row640, row656, row672, row688, row704,
    row720, row736, row752, row768, row784, row800, row816, row832, row848,
    row864, row880, row896, row912, row928, row944, row960, row976, row992,
    row1008, row1024, row1040, row1056, row1072, row1088, row1104, row1120, row1136,
    row1152, row1168, row1184, row1200, row1216, row1232, row1248, row1264, row1280,
    row1296, row1312, row1328, row1344, row1360, row1376, row1392, row1408, row1424,
    row1440, row1456, row1472, row1488, row1504, row1520, row1536, row1552, row1568,
    row1584, row1600, row1616, row1632, row1648, row1664, row1680, row1696, row1712,
    row1728, row1744, row1760, row1776, row1792, row1808, row1824, row1840, row1856,
    row1872, row1888, row1904, row1920, row1936, row1952, row1968, row1984, row2000,
    row2016, row2032, row2048, row2064, row2080, row2096, row2112, row2128, row2144,
    row2160, row2176, row2192, row2208, row2224, row2240, row2256, row2272, row2288,
    row2304, row2320, row2336, row2352, row2368, row2384, row2400, row2416, row2432,
    row2448, row2464, row2480, row2496, row2512, row2528, row2544, row2560, row2576,
    row2592⟩

theorem cert_lower (hknown : KnownBin cert_bounds) : LowerBin cert_mask cert_stock cert_goal 13 :=
  lowerDagRefF (boundsFor := cert_boundsFor) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hknown cert_sub cert_goals
    (fun _ _ _ hb => hintedBounds_mem hb)
    (symDagRef_sound (by decide +kernel) cert_syms cert_trace cert_links)
    cert_roots
    (by intro i hlo hhi
        have h := cert_nodes i hlo hhi
        simp only [cert_check, forceW_eq] at h
        change checkNodeViaF cert_mask cert_goal
          (hintedBounds cert_bound_chunks (hintWordAt cert_hint_pages i)) cert_trace cert_ref i = true
        exact h)

theorem knownNil : KnownBin [] := by
  intro b hb
  exact (List.not_mem_nil hb).elim

theorem knownCons {b : Nat × List Nat × Nat × Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hb : LowerBin b.1 b.2.1 b.2.2.2 b.2.2.1) (hs : KnownBin bounds) : KnownBin (b :: bounds) := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | hm
  · exact hb
  · exact hs a hm

def r0_mask : Nat := 0xcccc0000cccc
def r0_stock : List Nat := [0xcccc, 0xcc000000cc, 0xc0c00000c0c, 0x444400004444]
def r0_goal : Nat := 0x4440000444c
def r0_bounds : List (Nat × List Nat × Nat × Nat) := []
theorem r0_sub : ∀ b ∈ r0_bounds, r0_mask &&& b.1 = b.1 := by
  have hall : r0_bounds.all (fun b => Nat.beq (Nat.land r0_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r0_goals : ∀ b ∈ r0_bounds, canon b.1 r0_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r0_bounds.all (fun b => Nat.beq (canonF b.1 r0_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r0_forest : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def r0_links : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
def r0_trace := dagTraceF r0_mask r0_stock 5 r0_forest
def r0_check : Nat → Bool := dagCheckNodeF r0_mask r0_goal r0_bounds 64 r0_trace r0_links
set_option maxHeartbeats 0 in
theorem r0_roots : dagCheckRootsF r0_mask r0_goal r0_bounds
    (dagRefF 64 r0_trace r0_links 0) r0_stock 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_b0 : BlockChecked r0_check 0 12 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_b12 : BlockChecked r0_check 12 24 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_b24 : BlockChecked r0_check 24 36 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_b36 : BlockChecked r0_check 36 48 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_b48 : BlockChecked r0_check 48 60 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_b60 : BlockChecked r0_check 60 64 := by decide +kernel
theorem r0_nodes : ∀ i, 0 ≤ i → i < 64 → r0_check i = true :=
  joinBlockSpecs
    (joinBlockSpecs
      (blockSpec r0_b0)
      (joinBlockSpecs
        (blockSpec r0_b12)
        (blockSpec r0_b24)))
    (joinBlockSpecs
      (blockSpec r0_b36)
      (joinBlockSpecs
        (blockSpec r0_b48)
        (blockSpec r0_b60)))
theorem r0_known : KnownBin r0_bounds :=
  knownNil
theorem r0_lower : LowerBin r0_mask r0_stock r0_goal 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r0_known r0_sub r0_goals r0_roots r0_nodes

def r1_mask : Nat := 0xf0f00000f0f0
def r1_stock : List Nat := [0xf0f0, 0xf0000000f0, 0x303000003030, 0x505000005050]
def r1_goal : Nat := 0x105000005070
def r1_rows : Fin 64 → Fin 64 := decodeRows 0xbee000b6c0009e60009640000000000000000000000000003ce00034c0001c6000144000
set_option maxHeartbeats 0 in
theorem r1_lower : LowerBin r1_mask r1_stock r1_goal 6 :=
  relabelLower r1_rows r0_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r2_mask : Nat := 0xff00ff00
def r2_stock : List Nat := [0xff00, 0xf000f00, 0x33003300, 0x55005500]
def r2_goal : Nat := 0x1005700
def r2_bounds : List (Nat × List Nat × Nat × Nat) := []
theorem r2_sub : ∀ b ∈ r2_bounds, r2_mask &&& b.1 = b.1 := by
  have hall : r2_bounds.all (fun b => Nat.beq (Nat.land r2_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r2_goals : ∀ b ∈ r2_bounds, canon b.1 r2_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r2_bounds.all (fun b => Nat.beq (canonF b.1 r2_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r2_forest : Nat → Nat × Nat := unpackForestF 0x32eb2c32932232132000f 3 9
def r2_links : Nat → Nat → Option Nat := unpackLinksF 0xe78c70c30341 0xb2cb2cd2e92972252132000f 6 3 9 3 4
def r2_trace := dagTraceF r2_mask r2_stock 4 r2_forest
def r2_check : Nat → Bool := dagCheckNodeF r2_mask r2_goal r2_bounds 7 r2_trace r2_links
set_option maxHeartbeats 0 in
theorem r2_roots : dagCheckRootsF r2_mask r2_goal r2_bounds
    (dagRefF 7 r2_trace r2_links 0) r2_stock 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r2_b0 : BlockChecked r2_check 0 7 := by decide +kernel
theorem r2_nodes : ∀ i, 0 ≤ i → i < 7 → r2_check i = true :=
  blockSpec r2_b0
theorem r2_known : KnownBin r2_bounds :=
  knownNil
theorem r2_lower : LowerBin r2_mask r2_stock r2_goal 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r2_known r2_sub r2_goals r2_roots r2_nodes

def r3_mask : Nat := 0xaaaa0000aaaa
def r3_stock : List Nat := [0xaaaa, 0xaa000000aa, 0xa0a00000a0a, 0x222200002222]
def r3_goal : Nat := 0x2020000022a
def r3_rows : Fin 64 → Fin 64 := decodeRows 0xbed9e53cd1c5000000000000ae98e12c90c1000000000000
set_option maxHeartbeats 0 in
theorem r3_lower : LowerBin r3_mask r3_stock r3_goal 5 :=
  relabelLower r3_rows r2_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r4_mask : Nat := 0xffff
def r4_stock : List Nat := [0xff, 0xf0f, 0x3333, 0x5555]
def r4_goal : Nat := 0x577f
def r4_bounds : List (Nat × List Nat × Nat × Nat) := []
theorem r4_sub : ∀ b ∈ r4_bounds, r4_mask &&& b.1 = b.1 := by
  have hall : r4_bounds.all (fun b => Nat.beq (Nat.land r4_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r4_goals : ∀ b ∈ r4_bounds, canon b.1 r4_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r4_bounds.all (fun b => Nat.beq (canonF b.1 r4_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r4_forest : Nat → Nat × Nat := unpackForestF 0xc7463629d6490a6c43a492209086c00f 3 10
def r4_links : Nat → Nat → Option Nat := unpackLinksF 0x1a2d58b12a44890e8701 0x192430919242090d24209263a88d9d3a54d903a10d800f 7 3 10 4 4
def r4_trace := dagTraceF r4_mask r4_stock 4 r4_forest
def r4_check : Nat → Bool := dagCheckNodeF r4_mask r4_goal r4_bounds 10 r4_trace r4_links
set_option maxHeartbeats 0 in
theorem r4_roots : dagCheckRootsF r4_mask r4_goal r4_bounds
    (dagRefF 10 r4_trace r4_links 0) r4_stock 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r4_b0 : BlockChecked r4_check 0 10 := by decide +kernel
theorem r4_nodes : ∀ i, 0 ≤ i → i < 10 → r4_check i = true :=
  blockSpec r4_b0
theorem r4_known : KnownBin r4_bounds :=
  knownNil
theorem r4_lower : LowerBin r4_mask r4_stock r4_goal 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r4_known r4_sub r4_goals r4_roots r4_nodes

def r5_mask : Nat := 0xff000000ff
def r5_stock : List Nat := [0xff, 0xf0000000f, 0x3300000033, 0x5500000055]
def r5_goal : Nat := 0x570000007f
def r5_rows : Fin 64 → Fin 64 := decodeRows 0x2082082082082082082082082082082082082082082082082082082082082082082082089e69648e28601c61440c2040
set_option maxHeartbeats 0 in
theorem r5_lower : LowerBin r5_mask r5_stock r5_goal 5 :=
  relabelLower r5_rows r4_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r6_mask : Nat := 0xcccccccc
def r6_stock : List Nat := [0xcccc, 0xcc00cc, 0xc0c0c0c, 0x44444444]
def r6_goal : Nat := 0x44444c
def r6_bounds : List (Nat × List Nat × Nat × Nat) := []
theorem r6_sub : ∀ b ∈ r6_bounds, r6_mask &&& b.1 = b.1 := by
  have hall : r6_bounds.all (fun b => Nat.beq (Nat.land r6_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r6_goals : ∀ b ∈ r6_bounds, canon b.1 r6_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r6_bounds.all (fun b => Nat.beq (canonF b.1 r6_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r6_forest : Nat → Nat × Nat := unpackForestF 0x63a84c203018d981814a452130b0429108400f 4 10
def r6_links : Nat → Nat → Option Nat := unpackLinksF 0xb162c4a910604072e0701 0x253080c181830b2a3a78d95294484829108400f 7 3 10 4 4
def r6_trace := dagTraceF r6_mask r6_stock 4 r6_forest
def r6_check : Nat → Bool := dagCheckNodeF r6_mask r6_goal r6_bounds 11 r6_trace r6_links
set_option maxHeartbeats 0 in
theorem r6_roots : dagCheckRootsF r6_mask r6_goal r6_bounds
    (dagRefF 11 r6_trace r6_links 0) r6_stock 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r6_b0 : BlockChecked r6_check 0 11 := by decide +kernel
theorem r6_nodes : ∀ i, 0 ≤ i → i < 11 → r6_check i = true :=
  blockSpec r6_b0
theorem r6_known : KnownBin r6_bounds :=
  knownNil
theorem r6_lower : LowerBin r6_mask r6_stock r6_goal 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r6_known r6_sub r6_goals r6_roots r6_nodes

def r7_mask : Nat := 0xff000000ff00
def r7_stock : List Nat := [0xff00, 0xf0000000f00, 0x330000003300, 0x550000005500]
def r7_goal : Nat := 0x170000005700
def r7_rows : Fin 64 → Fin 64 := decodeRows 0x209000a2900028b000aab00030d000b2d00038f000baf000
set_option maxHeartbeats 0 in
theorem r7_lower : LowerBin r7_mask r7_stock r7_goal 5 :=
  relabelLower r7_rows r6_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r8_mask : Nat := 0xffff00000000
def r8_stock : List Nat := [0xff00000000, 0xf0f00000000, 0x333300000000, 0x555500000000]
def r8_goal : Nat := 0x175700000000
def r8_rows : Fin 64 → Fin 64 := decodeRows 0x821000a290008a3000aab000925000b2d0009a7000baf000
set_option maxHeartbeats 0 in
theorem r8_lower : LowerBin r8_mask r8_stock r8_goal 5 :=
  relabelLower r8_rows r6_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r9_mask : Nat := 0xffff0000ffff
def r9_stock : List Nat := [0xffff, 0xff000000ff, 0xf0f00000f0f, 0x333300003333, 0x555500005555]
def r9_goal : Nat := 0x17570000577f
def r9_bounds : List (Nat × List Nat × Nat × Nat) := [(0xcccc0000cccc, [0xcccc, 0xcc000000cc, 0xc0c00000c0c, 0x444400004444], 6, 0x4440000444c), (0xf0f00000f0f0, [0xf0f0, 0xf0000000f0, 0x303000003030, 0x505000005050], 6, 0x105000005070), (0xaaaa0000aaaa, [0xaaaa, 0xaa000000aa, 0xa0a00000a0a, 0x222200002222], 5, 0x2020000022a), (0xff000000ff, [0xff, 0xf0000000f, 0x3300000033, 0x5500000055], 5, 0x570000007f), (0xff000000ff00, [0xff00, 0xf0000000f00, 0x330000003300, 0x550000005500], 5, 0x170000005700), (0xffff, [0xff, 0xf0f, 0x3333, 0x5555], 5, 0x577f), (0xffff00000000, [0xff00000000, 0xf0f00000000, 0x333300000000, 0x555500000000], 5, 0x175700000000)]
theorem r9_sub : ∀ b ∈ r9_bounds, r9_mask &&& b.1 = b.1 := by
  have hall : r9_bounds.all (fun b => Nat.beq (Nat.land r9_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r9_goals : ∀ b ∈ r9_bounds, canon b.1 r9_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r9_bounds.all (fun b => Nat.beq (canonF b.1 r9_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r9_forest : Nat → Nat × Nat := unpackForestRelative (unpackPagedWidths [
    (17, 0x10ad0655822940946191d088e832b4084a04160216b502e0854c9af821b306ae085cb9a3849141089595e1da50c958228808440caf02530128d193604221293c12a03a4704260a8dc1028113a049b024a982486a5d31269691424a0094420130c4f4108021350c210410010340814282b10d6816b8335615a508d1834ac12460423020d81026001f),
    (18, 0x2d30123a02148ca5604d600a542c57c094c2856c0b602455c19540453009341c54c094c1852c135002970494706d28125602118285a06d68125602158084ac609c085432d7c086c2ed5c085c2ad1c1236028d0925202918823a02170092a1a5581a5d02570092a121583b5a0cd582b4a08d181a56045280856020da401b029608b5f029807b57029406b47024d85a5a),
    (19, 0x22960251ef4238085c1068e06d2809a300a460c06c0c8ec151b8212f032560449c0491828340146e060b0051b80824ab08602150722f8136c010d83315c042a0ba5f010482a96c043609a57034a804910041207a53010481a92c09ae809500a2ac02d74202b0345a058ac08d580c9c80850010ac0211a341581358014a84f17c05b012c570148c46d680e2f0125a014ac3ed2815a682345),
    (19, 0x10b80a1780d2e0115c012a002148722b00b5c04ac806d70081c00834168a60ad2411a081a5e0248c02910412b01148012881a13c04a40295c04068060b0042600824060960297010238084c012a80210f751b80b5d0548a071600a2a00a540146fac13c21ab8085c0668e0a96c0da501346014ac020db342580b450e4ba0297031238146c018c0128dc08a380927062b80491c051b81950),
    (20, 0xb459324f0cb5f0c35d01c6c0106c008600a35700c5e0934d00a6c0834700a5e073450685f0116c008540505b0246c01b6c0116c0096002857011500085c00964008538624700a5416c5f00d6c15c5b00b5614c5a01a6c0106c0086012c570445e03a5e)] 6) 11
def r9_links : Nat → Nat → Option Nat := unpackLinksPaged (unpackPaged [
    0x28805084a00932726404b8897012c1248843ac860906320c03e1c7b08ec51d4239886e28da11b0236006c00d421a8034086230c4018042f845d10b8116842d005908b20158627204e009a1128625004a009021200240047088e011c023803f4064d0c80190031086200c40188031006200a500d3c01c8001,
    0x42028401013a02040027e8cfd01f813f007d84fb01f603ec07c0cf801ee13dc07b04f221e403c807900ef19de03bc07780ec19bce37806e84dd01b4336806c08d801b0034ca6980cf219e033826494c90192032026118c20184030806100c20184030805d9caf615e02b445604a91952029865300a221440,
    0x5e80b5416a02c865900b2016402bc65780af015e02bc05780af01554aaa05502aa01530a8ec51c0a30546028c0504aa081400a8004fc29f813d127a04f409e813a1a7404dc69b81360a6634cc0980d30026004c00980130025e14a4c8e351c0238046088c01151a2a0448688851102220428e84850902120,
    0x7fc4ff81ff03fe07ec8f9a1f303e417c80f901f203d487a80f501ea03d407a80f295e40bc807846f005dd1bba07740ee05db0bac57580e98dd303a417442daf1b5036056c00d801b0035846910d109a20340267c2cf819f033e066c8c6b98d031246240c30d86030c06088c1018202fe35fc0bf817a2af40,
    0x4da498d5300e5a34b4096812c86523ca4093c727824b24960910f2186420c8408fc71f823f047e08f831c1a38047008d851a0a16f42c0848908860d241a082c505820b0416080d101820114020] 15 6)
  (unpackPaged [
    0x1901b0100640b01500a0340f80503c1241801700c0540221100803414c490518261440585cb451709144f93613c4985a04413651028044148510500441368e04c14c158d28542561385784a1460981580684609015046044088110421500801103a0380e05203e04c0e80503813a0d84d81a046112d3c40b4711093c402470f08dc3493a0d04a818046090050291240a0090200140a89402814408810024a3d0828d42413d0804d41e0420701001a82a06806830b5d042d542eb4d0b2d143025d0409542e24d0b09142793609c4982683609809818014048d701435a040d580e34a030d180a2560209180714601811866c5f18b15c6635f188d5c5e34716497849a461248d85815e122518481360c84901605601211804036932d3e18b4793093e182476e88ddad14f66c52d7b14755c50d1b93b31e4dd1b12b31c49dac04f66812d7a04755810d1a83b31a0dd1a02b31809c9101f24006c6a01700804c0001f,
    0x3d8d60f4254138040f014c3b0d80e8154398530e41343805304c010370d40dbb483689704a010358d28d4256348118ce35a330958ca05645117d10457430d690434a3e0958f215f3b856cea15738854cde14b36051cd005a32012848012310150c006c278190980342f01709a0542e2918b6a442e08d8b62341bc090b22462b0558a405625a118ae05c2b24e8ac12a16817094836250098a615c2a2d749eb552a09749e2552924e8a412a280d689e356270d289a3462609589614a250158c2c5f2fb15cc235f2f8d5cba3472d0948b0a4a2c08e8aa156288158928462480d88e258110040420201f89a08a2601000407a2582189403c0101fa528829461f84e8821360e0080360101d49687e15a1f05587a14a1e05187405a0d00807112c1c00b07004a1d29287423a1c85686e02c23317c88c57230d7c88357210d1c8025a1da9287623a1b45686c05a0c8040460141104902e0641a0150552341504d040124,
    0x62049d84b4761091d822374c20e93002a65ad7592b47658975922476308dd8615c6005417e14b5f051d4193b3ae4dd4112b3ac49d2e83a4b80a8aa01a5e0171720545c2111700345780b15a0245d0d29723465c09193d129394494b901e5b08ed6a2374fe4ece99375a04bd6612b59049d621232dc0795e2375688dd763474e692ce3a474e48ece32372d44b96e8465821116e0365800d15c02c56009154054540db0cc9445381b1260644901114a054518090ad12c5081b13e2544f09113a02448e911220544d8091200364c8d75301504780d92c35d498d54ca8364801412845a499159243564884e51e0562cc0795245f53115d4825f51096d402574e094d3424b37e91d2e156322518b112e4a81591c046460d610a34840899116254420da1123604009510824a438918ce04a3f8d510a45e3f0d590825a418958db945358168560123f88e0fe34c408d35003453f08e8fa052350128cc03a15004852010,
    0x7e4141fab5c7e8971f815c7d85420245e7b117600b5e800979fd15e7d4549fc05e7d0149f035c7b9591e2c647b0d71e22647ac4e1e91347a80e1e8034790d25e2341780979de246770911d2048760521d61447401603a014748521c00447280503a038728131d015c73a111ce0347300b1c8024712d71c425c6f8101c004c6f85521445f84116e0c45a81115df245679914ddab56768959af15f69c56d8d1575dc54dd514f71c52dc31476f450dae05f69816d8c0575d814dd404f71812dc20476f010cbb01f2e806c8401717804db835d6c8d55b02363d44945c0126d1161b24546c2d51b02546dad15b62456b88dd4993b3ce4dd4912b3cc49c580123504d19e0346a0171a00541c84d1a234a680d199e25634a119aac576a8d5da634769096d7f25751692cefa475148ecef237342518d01361b04999c8466700d99034d660d15942564ca0e99425c628571841506411b18e4606205b18216062a91d8a147,
    0x20e25585a8d51793545a0d63cb55938d155393b4564dd5283b4520dcc301f30806c8c01719804e00b648dad51e02348ead5a00b46838d160aa355464e5508397ead724646c802d723a26c9145b2431609101b2420608f9179031254080960e5648ead723a26c7788d236b4e8d8979dc2344064d5011254020d5000258c01a21e0548c05b22e0546780d2200508a91b22836c6509b22616c8905821c0508805421e05c870590fa134928d7e4835d900d5df23558f0d36383478d0d15da2368cc57e2d15b88c55e1b1536ac52d931475364ed119373e44963205f8b016e2205786814daa04b64811d4c83b4420dcf80252fc07cbe01b22005c620138491a20e45485ad52162547c0d521256c809591e4c647909920e356808d56024587b91420ab6c8289b20916c81c5820806c818181fb1507e8141fe05c] 22 7) 5 11 6
def r9_trace := dagTraceF r9_mask r9_stock 8 r9_forest
set_option maxHeartbeats 0 in
def r9_sym0 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r9_sym1 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeaeab6ca689e68e29648607de75c6da6585d65544d24503ce2ca34c2481c60c2144040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeaeab6ca689e68e29648607de75c6da6585d65544d24503ce2ca34c2481c60c2144040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r9_sym2 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa683ce34c2ca2487de75c6da6585d65544d24509e69648e28601c61440c2040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa683ce34c2ca2487de75c6da6585d65544d24509e69648e28601c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r9_sym3 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeaeab6ca683ce2ca34c2487de75c6da6585d65544d24509e68e29648601c60c2144040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeaeab6ca683ce2ca34c2487de75c6da6585d65544d24509e68e29648601c60c2144040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r9_syms : List (TableSymmetry r9_mask r9_goal) := [
  ⟨(⟨r9_sym0, by decide +kernel⟩, rowCanon r9_sym0 r9_mask), fun _ => rfl⟩,
  ⟨(⟨r9_sym1, by decide +kernel⟩, rowCanon r9_sym1 r9_mask), fun _ => rfl⟩,
  ⟨(⟨r9_sym2, by decide +kernel⟩, rowCanon r9_sym2 r9_mask), fun _ => rfl⟩,
  ⟨(⟨r9_sym3, by decide +kernel⟩, rowCanon r9_sym3 r9_mask), fun _ => rfl⟩]
def r9_profile : Nat → Nat := unpackPagedWidths [
    (7, 0xc007e4040091f1f842803f18f620a1c1030000080043e085020800640000078f8000080083010208080021cfe000190002a01037ff83),
    (7, 0x2e0013f06709bc180473f82700047b001017e00000737e136083427c8038f007e0003e000003f8010048840042fff01f020a01e403f),
    (7, 0xf1e3f81ce060e1fe030c2218006703df0effe03220058c06405601782050977276c07efc03f804010c00017ff80099d36100fd00040fc020),
    (7, 0x1000000083d8000000810e081030ebd7a103840008204041c2070800387f807e01c01ceff11cc3e000003fff81fe071010b840015f830b7),
    (7, 0xfffc3fb0200081001c087081f30003800800083080000737f0214007f1ec0810214081)] 6
def r9_boundsFor (i _ : Nat) := chooseBounds r9_bounds (r9_profile i)
def r9_ref := symDagRef r9_mask r9_goal 296 2 r9_syms r9_trace r9_links
def r9_check : Nat → Bool := fun i => checkNodeViaF r9_mask r9_goal (r9_boundsFor i) r9_trace r9_ref i
set_option maxHeartbeats 0 in
theorem r9_roots : dagCheckRootsF r9_mask r9_goal r9_bounds
    (r9_ref 0) r9_stock 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b0 : BlockChecked r9_check 0 12 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b12 : BlockChecked r9_check 12 24 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b24 : BlockChecked r9_check 24 36 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b36 : BlockChecked r9_check 36 48 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b48 : BlockChecked r9_check 48 60 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b60 : BlockChecked r9_check 60 72 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b72 : BlockChecked r9_check 72 84 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b84 : BlockChecked r9_check 84 96 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b96 : BlockChecked r9_check 96 108 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b108 : BlockChecked r9_check 108 120 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b120 : BlockChecked r9_check 120 132 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b132 : BlockChecked r9_check 132 144 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b144 : BlockChecked r9_check 144 156 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b156 : BlockChecked r9_check 156 168 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b168 : BlockChecked r9_check 168 180 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b180 : BlockChecked r9_check 180 192 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b192 : BlockChecked r9_check 192 204 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b204 : BlockChecked r9_check 204 216 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b216 : BlockChecked r9_check 216 228 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b228 : BlockChecked r9_check 228 240 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b240 : BlockChecked r9_check 240 252 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b252 : BlockChecked r9_check 252 264 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b264 : BlockChecked r9_check 264 276 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b276 : BlockChecked r9_check 276 288 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b288 : BlockChecked r9_check 288 296 := by decide +kernel
theorem r9_nodes : ∀ i, 0 ≤ i → i < 296 → r9_check i = true :=
  joinBlockSpecs
    (joinBlockSpecs
      (joinBlockSpecs
        (joinBlockSpecs
          (blockSpec r9_b0)
          (joinBlockSpecs
            (blockSpec r9_b12)
            (blockSpec r9_b24)))
        (joinBlockSpecs
          (blockSpec r9_b36)
          (joinBlockSpecs
            (blockSpec r9_b48)
            (blockSpec r9_b60))))
      (joinBlockSpecs
        (joinBlockSpecs
          (blockSpec r9_b72)
          (joinBlockSpecs
            (blockSpec r9_b84)
            (blockSpec r9_b96)))
        (joinBlockSpecs
          (blockSpec r9_b108)
          (joinBlockSpecs
            (blockSpec r9_b120)
            (blockSpec r9_b132)))))
    (joinBlockSpecs
      (joinBlockSpecs
        (joinBlockSpecs
          (blockSpec r9_b144)
          (joinBlockSpecs
            (blockSpec r9_b156)
            (blockSpec r9_b168)))
        (joinBlockSpecs
          (blockSpec r9_b180)
          (joinBlockSpecs
            (blockSpec r9_b192)
            (blockSpec r9_b204))))
      (joinBlockSpecs
        (joinBlockSpecs
          (blockSpec r9_b216)
          (joinBlockSpecs
            (blockSpec r9_b228)
            (blockSpec r9_b240)))
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec r9_b252)
            (blockSpec r9_b264))
          (joinBlockSpecs
            (blockSpec r9_b276)
            (blockSpec r9_b288)))))
theorem r9_known : KnownBin r9_bounds :=
  knownCons r0_lower (
  knownCons r1_lower (
  knownCons r3_lower (
  knownCons r5_lower (
  knownCons r7_lower (
  knownCons r4_lower (
  knownCons r8_lower (
  knownNil)))))))
theorem r9_lower : LowerBin r9_mask r9_stock r9_goal 9 :=
  lowerDagRefF (boundsFor := r9_boundsFor) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) r9_known r9_sub r9_goals
    (fun i _ _ hb => chooseBounds_mem (r9_profile i) hb)
    (symDagRef_sound (by decide +kernel) r9_syms r9_trace r9_links)
    r9_roots r9_nodes

def r10_mask : Nat := 0xf0f0f0f0f0f0f0f0
def r10_stock : List Nat := [0xf0f0f0f0, 0xf0f00000f0f0, 0xf000f000f000f0, 0x3030303030303030, 0x5050505050505050]
def r10_goal : Nat := 0x10105000505070
def r10_rows : Fin 64 → Fin 64 := decodeRows 0x10530d51571d18738f59779f000000000000000000000000925b2dd35f3d9a7bafdb7fbf
set_option maxHeartbeats 0 in
theorem r10_lower : LowerBin r10_mask r10_stock r10_goal 9 :=
  relabelLower r10_rows r9_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r11_mask : Nat := 0xcccccccccccccccc
def r11_stock : List Nat := [0xcccccccc, 0xcccc0000cccc, 0xcc00cc00cc00cc, 0xc0c0c0c0c0c0c0c, 0x4444444444444444]
def r11_goal : Nat := 0x404440044444c
def r11_rows : Fin 64 → Fin 64 := decodeRows 0x8328b49369b18738f59779f0000000000000000000000008a3aabcb3ebb9a7bafdb7fbf
set_option maxHeartbeats 0 in
theorem r11_lower : LowerBin r11_mask r11_stock r11_goal 9 :=
  relabelLower r11_rows r9_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r12_mask : Nat := 0xff00ff00ff00ff
def r12_stock : List Nat := [0xff00ff, 0xff000000ff, 0xf000f000f000f, 0x33003300330033, 0x55005500550055]
def r12_goal : Nat := 0x1700570057007f
def r12_rows : Fin 64 → Fin 64 := decodeRows 0x208208208208208208208208df6d74cf2c709e69648e28602082082082082082082082085d65544d24501c61440c2040
set_option maxHeartbeats 0 in
theorem r12_lower : LowerBin r12_mask r12_stock r12_goal 9 :=
  relabelLower r12_rows r9_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r13_mask : Nat := 0xf0f0f0f
def r13_stock : List Nat := [0xf0f, 0xf000f, 0x3030303, 0x5050505]
def r13_goal : Nat := 0x107070f
def r13_bounds : List (Nat × List Nat × Nat × Nat) := []
theorem r13_sub : ∀ b ∈ r13_bounds, r13_mask &&& b.1 = b.1 := by
  have hall : r13_bounds.all (fun b => Nat.beq (Nat.land r13_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r13_goals : ∀ b ∈ r13_bounds, canon b.1 r13_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r13_bounds.all (fun b => Nat.beq (canonF b.1 r13_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r13_forest : Nat → Nat × Nat := unpackForestRelative (unpackPagedWidths [
    (16, 0x193a152d103e0c360826041ed81b3a3e363a0b4807402a36094c05441e32183a043408300424083604199c17042c9125081e041d8524803e0924044c743d703c1524104c041408440434583a04145036152404140c4c041404443835081504142c340c4c0844041c1c32181e1124041408340414041d0413000f)] 6) 10
def r13_links : Nat → Nat → Option Nat := unpackLinksPaged (unpackPaged [
    0x2d836a1b40da02cc35c59aa4d026813409a04c0a6012c290347863c11a28a1c312104d796b0340da00d005c62e01684b405622b01504a8054029854829c44e026852c49604a0a5012428664302180f8a7c03e01f00e4a7203711b80d826c03220ce4070001] 13 6)
  (unpackPaged [
    0xd423ed023ac4236b8232b554aa5546b513aa5136a012e1c12db444aa4446b403aa4036a102e1d02da101ea001995012940118801038444380349802c8043d7043a5843650435344348002d7002a5802650025340249001e8c01d4c43414024801247c04c484446003468034140246801414014701246c04c6404460034580144c03c440344c01444014501244804c400442603c1102c1001c1101d1001a3901638015340142c04c280442603c2502c2401c1443414024140141812410444100340c0140912d0812a9512694125881248444e7844d7444c5c44a544463c44530444204428403e7803d7403c5c03a540363c03530034200321d02e0902d1c01e0801ddb63fdaa3b9ea3706a33db13fd9d3b9dd3705d33da52fd992b9d92705923dac3fd8c3b9cc3704c33da02fd882b9c82704823d901fd801b9c017040130000f,
    0x240149802424028180101812426c4c604442603c60034f054ab4d46f013ab4936ed12eec12da012508122e844ed5c4ae44465cc42e803ed583ae40365c832e0026a0025dc01e0801dcc348c8340b1924b0824ada34c014cbc14460924ac8346181470010b00341402414120148201581061930ac920ac030a80240c02c1801cd464ed064ac4646b8642] 20 7) 5 10 6
def r13_trace := dagTraceF r13_mask r13_stock 6 r13_forest
set_option maxHeartbeats 0 in
def r13_sym0 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym1 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d96985d65544d14903ce34c2c92881c61440c1080
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d96985d65544d14903ce34c2c92881c61440c1080
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym2 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da4d25d65546584503ce34c2ca0c21c6144248040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da4d25d65546584503ce34c2ca0c21c6144248040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym3 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d94d15d65546984903ce34c2c90c11c6144288080
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d36925d65546516103ce34c2c32821c6144241200
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym4 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65542ca2483ce34c4d24501c61440c2040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65542ca2483ce34c4d24501c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym5 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d96985d65542c92883ce34c4d14901c61440c1080
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d96985d65542c92883ce34c4d14901c61440c1080
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym6 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da2ca5d65546582483ce34c4d20c21c6144450040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da4d25d65542ca0c23ce34c6584501c6144248040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym7 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d92c95d65546982883ce34c4d10c11c6144490080
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d36925d65542c32823ce34c6516101c6144241200
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym8 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da4d25d65542ca0c23ce34c6584501c6144248040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da2ca5d65546582483ce34c4d20c21c6144450040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym9 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da2ca5d65544d20c23ce34c6582481c6144450040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da2ca5d65544d20c23ce34c6582481c6144450040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym10 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d32c35d65546922823ce34c6512411c6144610200
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d32c35d65546922823ce34c6512411c6144610200
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym11 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d94d15d65542c90c13ce34c6984901c6144288080
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6cb68a5d65546496083ce34c4c34821c6144441400
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym12 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d92c95d65544d10c13ce34c6982881c6144490080
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6cb68a5d65544c34823ce34c6496081c6144441400
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym13 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d32c35d65546512413ce34c6922821c6144610200
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6cb4c35d655468a4823ce34c6494411c6144608400
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_syms : List (TableSymmetry r13_mask r13_goal) := [
  ⟨(⟨r13_sym0, by decide +kernel⟩, rowCanon r13_sym0 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym1, by decide +kernel⟩, rowCanon r13_sym1 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym2, by decide +kernel⟩, rowCanon r13_sym2 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym3, by decide +kernel⟩, rowCanon r13_sym3 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym4, by decide +kernel⟩, rowCanon r13_sym4 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym5, by decide +kernel⟩, rowCanon r13_sym5 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym6, by decide +kernel⟩, rowCanon r13_sym6 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym7, by decide +kernel⟩, rowCanon r13_sym7 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym8, by decide +kernel⟩, rowCanon r13_sym8 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym9, by decide +kernel⟩, rowCanon r13_sym9 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym10, by decide +kernel⟩, rowCanon r13_sym10 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym11, by decide +kernel⟩, rowCanon r13_sym11 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym12, by decide +kernel⟩, rowCanon r13_sym12 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym13, by decide +kernel⟩, rowCanon r13_sym13 r13_mask), fun _ => rfl⟩]
def r13_profile : Nat → Nat := unpackPagedWidths [
    (1, 0x0)] 6
def r13_boundsFor (i _ : Nat) := chooseBounds r13_bounds (r13_profile i)
def r13_ref := symDagRef r13_mask r13_goal 61 4 r13_syms r13_trace r13_links
def r13_check : Nat → Bool := fun i => checkNodeViaF r13_mask r13_goal (r13_boundsFor i) r13_trace r13_ref i
set_option maxHeartbeats 0 in
theorem r13_roots : dagCheckRootsF r13_mask r13_goal r13_bounds
    (r13_ref 0) r13_stock 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b0 : BlockChecked r13_check 0 12 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b12 : BlockChecked r13_check 12 24 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b24 : BlockChecked r13_check 24 36 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b36 : BlockChecked r13_check 36 48 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b48 : BlockChecked r13_check 48 60 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b60 : BlockChecked r13_check 60 61 := by decide +kernel
theorem r13_nodes : ∀ i, 0 ≤ i → i < 61 → r13_check i = true :=
  joinBlockSpecs
    (joinBlockSpecs
      (blockSpec r13_b0)
      (joinBlockSpecs
        (blockSpec r13_b12)
        (blockSpec r13_b24)))
    (joinBlockSpecs
      (blockSpec r13_b36)
      (joinBlockSpecs
        (blockSpec r13_b48)
        (blockSpec r13_b60)))
theorem r13_known : KnownBin r13_bounds :=
  knownNil
theorem r13_lower : LowerBin r13_mask r13_stock r13_goal 7 :=
  lowerDagRefF (boundsFor := r13_boundsFor) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) r13_known r13_sub r13_goals
    (fun i _ _ hb => chooseBounds_mem (r13_profile i) hb)
    (symDagRef_sound (by decide +kernel) r13_syms r13_trace r13_links)
    r13_roots r13_nodes

def r14_mask : Nat := 0x5555555500000000
def r14_stock : List Nat := [0x555500000000, 0x55005500000000, 0x505050500000000, 0x1111111100000000]
def r14_goal : Nat := 0x115155500000000
def r14_rows : Fin 64 → Fin 64 := decodeRows 0xfbceb8000000db4cb0000000bacaa80000009a48a0
set_option maxHeartbeats 0 in
theorem r14_lower : LowerBin r14_mask r14_stock r14_goal 7 :=
  relabelLower r14_rows r13_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r15_mask : Nat := 0x5555555555555555
def r15_stock : List Nat := [0x55555555, 0x555500005555, 0x55005500550055, 0x505050505050505, 0x1111111111111111]
def r15_goal : Nat := 0x115155501555555
def r15_bounds : List (Nat × List Nat × Nat × Nat) := [(0x5555555500000000, [0x555500000000, 0x55005500000000, 0x505050500000000, 0x1111111100000000], 7, 0x115155500000000)]
theorem r15_sub : ∀ b ∈ r15_bounds, r15_mask &&& b.1 = b.1 := by
  have hall : r15_bounds.all (fun b => Nat.beq (Nat.land r15_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r15_goals : ∀ b ∈ r15_bounds, canon b.1 r15_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r15_bounds.all (fun b => Nat.beq (canonF b.1 r15_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r15_forest : Nat → Nat × Nat := fun _ => (0, 0)
def r15_links : Nat → Nat → Option Nat := fun _ _ => none
def r15_trace := dagTraceF r15_mask r15_stock 7 r15_forest
def r15_check : Nat → Bool := dagCheckNodeF r15_mask r15_goal r15_bounds 0 r15_trace r15_links
set_option maxHeartbeats 0 in
theorem r15_roots : dagCheckRootsF r15_mask r15_goal r15_bounds
    (dagRefF 0 r15_trace r15_links 0) r15_stock 7 = true := by decide +kernel
theorem r15_nodes : ∀ i, 0 ≤ i → i < 0 → r15_check i = true :=
  fun i _ hi => absurd hi (Nat.not_lt_zero i)
theorem r15_known : KnownBin r15_bounds :=
  knownCons r14_lower (
  knownNil)
theorem r15_lower : LowerBin r15_mask r15_stock r15_goal 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r15_known r15_sub r15_goals r15_roots r15_nodes

def r16_mask : Nat := 0xaaaaaaaaaaaaaaaa
def r16_stock : List Nat := [0xaaaaaaaa, 0xaaaa0000aaaa, 0xaa00aa00aa00aa, 0xa0a0a0a0a0a0a0a, 0x2222222222222222]
def r16_goal : Nat := 0x202020002022a
def r16_rows : Fin 64 → Fin 64 := decodeRows 0x100901101900300b01301b00500d01501d00700f01701f02102903103902302b03303b02502d03503d02702f03703f
set_option maxHeartbeats 0 in
theorem r16_lower : LowerBin r16_mask r16_stock r16_goal 8 :=
  relabelLower r16_rows r15_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r17_mask : Nat := 0xf0f0f0f0f0f0f0f
def r17_stock : List Nat := [0xf0f0f0f, 0xf0f00000f0f, 0xf000f000f000f, 0x303030303030303, 0x505050505050505]
def r17_goal : Nat := 0x10707070107070f
def r17_bounds : List (Nat × List Nat × Nat × Nat) := [(0xf0f0f0f, [0xf0f, 0xf000f, 0x3030303, 0x5050505], 7, 0x107070f)]
theorem r17_sub : ∀ b ∈ r17_bounds, r17_mask &&& b.1 = b.1 := by
  have hall : r17_bounds.all (fun b => Nat.beq (Nat.land r17_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r17_goals : ∀ b ∈ r17_bounds, canon b.1 r17_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r17_bounds.all (fun b => Nat.beq (canonF b.1 r17_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r17_forest : Nat → Nat × Nat := fun _ => (0, 0)
def r17_links : Nat → Nat → Option Nat := fun _ _ => none
def r17_trace := dagTraceF r17_mask r17_stock 7 r17_forest
def r17_check : Nat → Bool := dagCheckNodeF r17_mask r17_goal r17_bounds 0 r17_trace r17_links
set_option maxHeartbeats 0 in
theorem r17_roots : dagCheckRootsF r17_mask r17_goal r17_bounds
    (dagRefF 0 r17_trace r17_links 0) r17_stock 7 = true := by decide +kernel
theorem r17_nodes : ∀ i, 0 ≤ i → i < 0 → r17_check i = true :=
  fun i _ hi => absurd hi (Nat.not_lt_zero i)
theorem r17_known : KnownBin r17_bounds :=
  knownCons r13_lower (
  knownNil)
theorem r17_lower : LowerBin r17_mask r17_stock r17_goal 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r17_known r17_sub r17_goals r17_roots r17_nodes

def r18_mask : Nat := 0x33333333
def r18_stock : List Nat := [0x3333, 0x330033, 0x3030303, 0x11111111]
def r18_goal : Nat := 0x1131333
def r18_rows : Fin 64 → Fin 64 := decodeRows 0x8208208208208208208208208208208208208208208208208208275c65808208255445008208234c248082082144040
set_option maxHeartbeats 0 in
theorem r18_lower : LowerBin r18_mask r18_stock r18_goal 7 :=
  relabelLower r18_rows r13_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r19_mask : Nat := 0x4444444411111111
def r19_stock : List Nat := [0x11111111, 0x444400001111, 0x44004400110011, 0x404040401010101]
def r19_goal : Nat := 0x4044401111111
def r19_rows : Fin 64 → Fin 64 := decodeRows 0x41041041041041041041041041041041041041041041041041041fbadb2041041baa9a2041041718510041041308100
set_option maxHeartbeats 0 in
theorem r19_lower : LowerBin r19_mask r19_stock r19_goal 7 :=
  relabelLower r19_rows r13_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r20_mask : Nat := 0xc0c0c0c030303030
def r20_stock : List Nat := [0x30303030, 0xc0c000003030, 0xc000c000300030, 0x4040404010101010]
def r20_goal : Nat := 0x4000101030
def r20_rows : Fin 64 → Fin 64 := decodeRows 0x10530d00000051571d0000009a7baf000000db7fbf
set_option maxHeartbeats 0 in
theorem r20_lower : LowerBin r20_mask r20_stock r20_goal 7 :=
  relabelLower r20_rows r13_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r21_mask : Nat := 0xcc00cc0033003300
def r21_stock : List Nat := [0x33003300, 0xcc0000003300, 0xc000c0003000300, 0x4400440011001100]
def r21_goal : Nat := 0x40001001300
def r21_rows : Fin 64 → Fin 64 := decodeRows 0x20930d00000061971d000000aabbaf000000ebbfbf
set_option maxHeartbeats 0 in
theorem r21_lower : LowerBin r21_mask r21_stock r21_goal 7 :=
  relabelLower r21_rows r13_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r22_mask : Nat := 0xcccc000033330000
def r22_stock : List Nat := [0x33330000, 0xcc000000330000, 0xc0c000003030000, 0x4444000011110000]
def r22_goal : Nat := 0x4000001130000
def r22_rows : Fin 64 → Fin 64 := decodeRows 0x41151500000061971d000000cb3db7000000ebbfbf
set_option maxHeartbeats 0 in
theorem r22_lower : LowerBin r22_mask r22_stock r22_goal 7 :=
  relabelLower r22_rows r13_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r23_mask : Nat := 0xcccccccc00000000
def r23_stock : List Nat := [0xcccc00000000, 0xcc00cc00000000, 0xc0c0c0c00000000, 0x4444444400000000]
def r23_goal : Nat := 0x4044400000000
def r23_rows : Fin 64 → Fin 64 := decodeRows 0x8a39a7aabbafcb3db7ebbfbf
set_option maxHeartbeats 0 in
theorem r23_lower : LowerBin r23_mask r23_stock r23_goal 5 :=
  relabelLower r23_rows r4_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r24_mask : Nat := 0xcccc00003333
def r24_stock : List Nat := [0x3333, 0xcc00000033, 0xc0c00000303, 0x444400001111]
def r24_goal : Nat := 0x44400001333
def r24_rows : Fin 64 → Fin 64 := decodeRows 0x8208208208208208208208208208208208208208208208200110520930d0820820820828a39a7aabbaf082082082082
set_option maxHeartbeats 0 in
theorem r24_lower : LowerBin r24_mask r24_stock r24_goal 5 :=
  relabelLower r24_rows r2_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r25_mask : Nat := 0xcc00cc00330033
def r25_stock : List Nat := [0x330033, 0xcc00000033, 0xc000c00030003, 0x44004400110011]
def r25_goal : Nat := 0x4004400130033
def r25_rows : Fin 64 → Fin 64 := decodeRows 0x820820820820820820820820820820820820820820820820011054115150820820820828a39a7cb3db7082082082082
set_option maxHeartbeats 0 in
theorem r25_lower : LowerBin r25_mask r25_stock r25_goal 5 :=
  relabelLower r25_rows r2_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r26_mask : Nat := 0xc0c0c0c03030303
def r26_stock : List Nat := [0x3030303, 0xc0c00000303, 0xc000c00030003, 0x404040401010101]
def r26_goal : Nat := 0x4040401030303
def r26_rows : Fin 64 → Fin 64 := decodeRows 0x820820820820820820820820820820820820820820820820012094116190820820820828a3aabcb3ebb082082082082
set_option maxHeartbeats 0 in
theorem r26_lower : LowerBin r26_mask r26_stock r26_goal 5 :=
  relabelLower r26_rows r2_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r27_mask : Nat := 0x8888888822222222
def r27_stock : List Nat := [0x22222222, 0x888800002222, 0x88008800220022, 0x808080802020202]
def r27_goal : Nat := 0x20222
def r27_rows : Fin 64 → Fin 64 := decodeRows 0x6316726b36f47357767b77f
set_option maxHeartbeats 0 in
theorem r27_lower : LowerBin r27_mask r27_stock r27_goal 5 :=
  relabelLower r27_rows r4_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r28_mask : Nat := 0xcccccccc33333333
def r28_stock : List Nat := [0x33333333, 0xcccc00003333, 0xcc00cc00330033, 0xc0c0c0c03030303, 0x4444444411111111]
def r28_goal : Nat := 0x4044401131333
def r28_bounds : List (Nat × List Nat × Nat × Nat) := [(0x33333333, [0x3333, 0x330033, 0x3030303, 0x11111111], 7, 0x1131333), (0x4444444411111111, [0x11111111, 0x444400001111, 0x44004400110011, 0x404040401010101], 7, 0x4044401111111), (0xc0c0c0c030303030, [0x30303030, 0xc0c000003030, 0xc000c000300030, 0x4040404010101010], 7, 0x4000101030), (0xcc00cc0033003300, [0x33003300, 0xcc0000003300, 0xc000c0003000300, 0x4400440011001100], 7, 0x40001001300), (0xcccc000033330000, [0x33330000, 0xcc000000330000, 0xc0c000003030000, 0x4444000011110000], 7, 0x4000001130000), (0xcccccccc00000000, [0xcccc00000000, 0xcc00cc00000000, 0xc0c0c0c00000000, 0x4444444400000000], 5, 0x4044400000000), (0xcccc00003333, [0x3333, 0xcc00000033, 0xc0c00000303, 0x444400001111], 5, 0x44400001333), (0xcc00cc00330033, [0x330033, 0xcc00000033, 0xc000c00030003, 0x44004400110011], 5, 0x4004400130033), (0xc0c0c0c03030303, [0x3030303, 0xc0c00000303, 0xc000c00030003, 0x404040401010101], 5, 0x4040401030303), (0x8888888822222222, [0x22222222, 0x888800002222, 0x88008800220022, 0x808080802020202], 5, 0x20222)]
theorem r28_sub : ∀ b ∈ r28_bounds, r28_mask &&& b.1 = b.1 := by
  have hall : r28_bounds.all (fun b => Nat.beq (Nat.land r28_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r28_goals : ∀ b ∈ r28_bounds, canon b.1 r28_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r28_bounds.all (fun b => Nat.beq (canonF b.1 r28_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r28_forest : Nat → Nat × Nat := unpackForestRelative (unpackPagedWidths [
    (17, 0x322b02910a4ac0c6020a10e138609a093404a30613010a80842311b8ed2828b0084c11a30691812680846101382940168e08269c218415410a91b5f04220d58854bc205e0c2e8417010a4db470426028dd84bc0b55582f83160146e985e042e02d1d00a40854062f9a0e810a83c6e1a310b16810b81c56083702158406e0b58062f820d81036001f),
    (18, 0x82918d2c5b4a021004b46024d03946091881c5a041b80856040cc08318649c08341d168085c)] 6) 11
def r28_links : Nat → Nat → Option Nat := unpackLinksPaged (unpackPaged [
    0x7a377377076176076076075173273071262f6206206206025f15f05e156856055154148c4804803f93f03e13e03e03e03d13c131b3102f22e12e02862802712612602512412402312212202112102102102012002001a61a01911810bd01a001,
    0xa509d89c19c09939819629519509509508e78d17fe7f07e17e07d1] 12 6)
  (unpackPaged [
    0x8800c610034800171c184c7020f1c002c7c0911b885c6e00f1e04607004d1b92466e0519a8054600131dac61821169f84567a4d59e82567605089205a528159d004e720135b004c5e0115a00425c40d5700256211618004c5a00d168134642d6978b56640d29783465c2959702465821596004654094148347666d1d98a476608dc8a04a56811d420462240e9590375040d88802a56009d400261ef1741bc551801746305a4cc159300554a01507884a062119180443605784805c1ef5b9105623409b90825e2a01b890062400178f805d3c0170400553a0148dac58360130d0237183174c0c55180d74c03550e2118380362c1160a8237260170903472001507845f1a01504805c1811b858462141168404560e01b830056080d601845f48317d2035f380d1cc825e2e017ca005e2201487084a0a211c108461c00e8280370400d80c34f02c93e19a3702a53e1893786049d380430280ec0902b02006c0001f,
    0x10c56e90b18a82a6e3b09890a059900106800293a8086080539ab141f80539a0101f00439604d1e805378058248462901169d81628e01b9a00623a816a3005645117ce445f1cad7a2ab5388ad4a7834b9c0d2a6034694491a5014666014ce204b1c00e628033] 22 7) 4 11 5
def r28_trace := dagTraceF r28_mask r28_stock 9 r28_forest
set_option maxHeartbeats 0 in
def r28_sym0 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym1 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cdf6e78efad74cf2c70beeb6c9e6a68aea9648e28607de75c6da5545d66584d24503ce34c2ca1441c62480c2040
  invFun := decodeRows 0xffef7cdf6e78efad74cf2c70beeb6c9e6a68aea9648e28607de75c6da5545d66584d24503ce34c2ca1441c62480c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym2 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78beed74aeac70df6b6ccf2a689e69648e28607de75c6da6585d634c4d22483ce5542ca4501c61440c2040
  invFun := decodeRows 0xffef7cefae78beed74aeac70df6b6ccf2a689e69648e28607de75c6da6585d634c4d22483ce5542ca4501c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym3 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cbeee78efad74aeac70df6b6c9e6a68cf29648e28607de75c6da34c5d66584d22483ce5542ca1441c64500c2040
  invFun := decodeRows 0xffef7cdf6e78beed749e6c70efab6ccf2a68aea9648e28607de75c6da5545d634c4d21443ce6582ca4501c62480c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym4 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cdf6e78beed749e6c70efab6ccf2a68aea9648e28607de75c6da5545d634c4d21443ce6582ca4501c62480c2040
  invFun := decodeRows 0xffef7cbeee78efad74aeac70df6b6c9e6a68cf29648e28607de75c6da34c5d66584d22483ce5542ca1441c64500c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym5 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xfddf7ced9e78dd5d74cd1c70bcdb6cac9a689c59648c18607def9c6dae985d6d944d2c903ceb8c2caa881c69840c2880
  invFun := decodeRows 0xfddf7ced9e78dd5d74cd1c70bcdb6cac9a689c59648c18607def9c6dae985d6d944d2c903ceb8c2caa881c69840c2880
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym6 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xfddf7ced9e78bcdd74ac9c70dd5b6ccd1a689c59648c18607def9c6dae985d6b8c4d2a883ced942cac901c69840c2880
  invFun := decodeRows 0xfddf7ced9e78bcdd74ac9c70dd5b6ccd1a689c59648c18607def9c6dae985d6b8c4d2a883ced942cac901c69840c2880
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym7 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xfddf7cbcde78ed9d74ac9c70dd5b6c9c5a68cd19648c18607def9c6dab8c5d6e984d2a883ced942ca9841c6c900c2880
  invFun := decodeRows 0xfddf7cdd5e78bcdd749c5c70ed9b6ccd1a68ac99648c18607def9c6dad945d6b8c4d29843cee982cac901c6a880c2880
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym8 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xfddf7cdd5e78bcdd749c5c70ed9b6ccd1a68ac99648c18607def9c6dad945d6b8c4d29843cee982cac901c6a880c2880
  invFun := decodeRows 0xfddf7cbcde78ed9d74ac9c70dd5b6c9c5a68cd19648c18607def9c6dab8c5d6e984d2a883ced942ca9841c6c900c2880
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_syms : List (TableSymmetry r28_mask r28_goal) := [
  ⟨(⟨r28_sym0, by decide +kernel⟩, rowCanon r28_sym0 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym1, by decide +kernel⟩, rowCanon r28_sym1 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym2, by decide +kernel⟩, rowCanon r28_sym2 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym3, by decide +kernel⟩, rowCanon r28_sym3 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym4, by decide +kernel⟩, rowCanon r28_sym4 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym5, by decide +kernel⟩, rowCanon r28_sym5 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym6, by decide +kernel⟩, rowCanon r28_sym6 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym7, by decide +kernel⟩, rowCanon r28_sym7 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym8, by decide +kernel⟩, rowCanon r28_sym8 r28_mask), fun _ => rfl⟩]
def r28_profile : Nat → Nat := unpackPagedWidths [
    (10, 0xffccd7340b3ac3810c000111f0201cbfc990040001e39064d90fc6c371ff0fc8047cbf00673354242461f010ff000651fcca1fc00b5bbf001fc6fc004933f000008ed0c00011a298c1fc00603bf0fc1f),
    (10, 0xed37f7f0fe7f37c5f8ad2582d0d3ff3f17c407f401)] 6
def r28_boundsFor (i _ : Nat) := chooseBounds r28_bounds (r28_profile i)
def r28_ref := symDagRef r28_mask r28_goal 81 4 r28_syms r28_trace r28_links
def r28_check : Nat → Bool := fun i => checkNodeViaF r28_mask r28_goal (r28_boundsFor i) r28_trace r28_ref i
set_option maxHeartbeats 0 in
theorem r28_roots : dagCheckRootsF r28_mask r28_goal r28_bounds
    (r28_ref 0) r28_stock 9 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b0 : BlockChecked r28_check 0 12 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b12 : BlockChecked r28_check 12 24 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b24 : BlockChecked r28_check 24 36 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b36 : BlockChecked r28_check 36 48 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b48 : BlockChecked r28_check 48 60 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b60 : BlockChecked r28_check 60 72 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b72 : BlockChecked r28_check 72 81 := by decide +kernel
theorem r28_nodes : ∀ i, 0 ≤ i → i < 81 → r28_check i = true :=
  joinBlockSpecs
    (joinBlockSpecs
      (blockSpec r28_b0)
      (joinBlockSpecs
        (blockSpec r28_b12)
        (blockSpec r28_b24)))
    (joinBlockSpecs
      (joinBlockSpecs
        (blockSpec r28_b36)
        (blockSpec r28_b48))
      (joinBlockSpecs
        (blockSpec r28_b60)
        (blockSpec r28_b72)))
theorem r28_known : KnownBin r28_bounds :=
  knownCons r18_lower (
  knownCons r19_lower (
  knownCons r20_lower (
  knownCons r21_lower (
  knownCons r22_lower (
  knownCons r23_lower (
  knownCons r24_lower (
  knownCons r25_lower (
  knownCons r26_lower (
  knownCons r27_lower (
  knownNil))))))))))
theorem r28_lower : LowerBin r28_mask r28_stock r28_goal 10 :=
  lowerDagRefF (boundsFor := r28_boundsFor) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) r28_known r28_sub r28_goals
    (fun i _ _ hb => chooseBounds_mem (r28_profile i) hb)
    (symDagRef_sound (by decide +kernel) r28_syms r28_trace r28_links)
    r28_roots r28_nodes

def r29_mask : Nat := 0xffff00000000ffff
def r29_stock : List Nat := [0xffff, 0xff0000000000ff, 0xf0f000000000f0f, 0x3333000000003333, 0x5555000000005555]
def r29_goal : Nat := 0x11700000000577f
def r29_rows : Fin 64 → Fin 64 := decodeRows 0x141008341010541018741020941028b41030d41038f410410c31410cb3410d35410db7410e39410ebb410f3d410fbf
set_option maxHeartbeats 0 in
theorem r29_lower : LowerBin r29_mask r29_stock r29_goal 10 :=
  relabelLower r29_rows r28_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r30_mask : Nat := 0xff00ff00ff00ff00
def r30_stock : List Nat := [0xff00ff00, 0xff000000ff00, 0xf000f000f000f00, 0x3300330033003300, 0x5500550055005500]
def r30_goal : Nat := 0x100170001005700
def r30_rows : Fin 64 → Fin 64 := decodeRows 0x20961900000028b69b00000030d71d00000038f79f000000a29e39000000aabebb000000b2df3d000000baffbf
set_option maxHeartbeats 0 in
theorem r30_lower : LowerBin r30_mask r30_stock r30_goal 8 :=
  relabelLower r30_rows r17_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r31_mask : Nat := 0x3333333333333333
def r31_stock : List Nat := [0x33333333, 0x333300003333, 0x33003300330033, 0x303030303030303, 0x1111111111111111]
def r31_goal : Nat := 0x113131301131333
def r31_rows : Fin 64 → Fin 64 := decodeRows 0x82082f7ce78082082d74c70082082b6ca6808208296486008208275c65808208255445008208234c248082082144040
set_option maxHeartbeats 0 in
theorem r31_lower : LowerBin r31_mask r31_stock r31_goal 8 :=
  relabelLower r31_rows r17_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r32_mask : Nat := 0xffff0000ffff0000
def r32_stock : List Nat := [0xffff0000, 0xff000000ff0000, 0xf0f00000f0f0000, 0x3333000033330000, 0x5555000055550000]
def r32_goal : Nat := 0x117000001570000
def r32_rows : Fin 64 → Fin 64 := decodeRows 0x41161900000049369b00000051571d00000059779f000000c31e39000000cb3ebb000000d35f3d000000db7fbf
set_option maxHeartbeats 0 in
theorem r32_lower : LowerBin r32_mask r32_stock r32_goal 8 :=
  relabelLower r32_rows r17_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r33_mask : Nat := 0xaaaaaaaa
def r33_stock : List Nat := [0xaaaa, 0xaa00aa, 0xa0a0a0a, 0x22222222]
def r33_goal : Nat := 0x2022a
def r33_rows : Fin 64 → Fin 64 := decodeRows 0x4314700000024b34f00000045355700000065b75f
set_option maxHeartbeats 0 in
theorem r33_lower : LowerBin r33_mask r33_stock r33_goal 7 :=
  relabelLower r33_rows r13_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r34_mask : Nat := 0xff00ff
def r34_stock : List Nat := [0xff, 0xf000f, 0x330033, 0x550055]
def r34_goal : Nat := 0x57007f
def r34_rows : Fin 64 → Fin 64 := decodeRows 0x2082082082082082082082082082082082082082082082082082082082082082082082085d65544d24501c61440c2040
set_option maxHeartbeats 0 in
theorem r34_lower : LowerBin r34_mask r34_stock r34_goal 5 :=
  relabelLower r34_rows r4_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r35_mask : Nat := 0xffffffff
def r35_stock : List Nat := [0xffff, 0xff00ff, 0xf0f0f0f, 0x33333333, 0x55555555]
def r35_goal : Nat := 0x157577f
def r35_bounds : List (Nat × List Nat × Nat × Nat) := [(0xaaaaaaaa, [0xaaaa, 0xaa00aa, 0xa0a0a0a, 0x22222222], 7, 0x2022a), (0x33333333, [0x3333, 0x330033, 0x3030303, 0x11111111], 7, 0x1131333), (0xf0f0f0f, [0xf0f, 0xf000f, 0x3030303, 0x5050505], 7, 0x107070f), (0xff00ff, [0xff, 0xf000f, 0x330033, 0x550055], 5, 0x57007f), (0xff00ff00, [0xff00, 0xf000f00, 0x33003300, 0x55005500], 5, 0x1005700), (0xffff, [0xff, 0xf0f, 0x3333, 0x5555], 5, 0x577f)]
theorem r35_sub : ∀ b ∈ r35_bounds, r35_mask &&& b.1 = b.1 := by
  have hall : r35_bounds.all (fun b => Nat.beq (Nat.land r35_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r35_goals : ∀ b ∈ r35_bounds, canon b.1 r35_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r35_bounds.all (fun b => Nat.beq (canonF b.1 r35_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r35_forest : Nat → Nat × Nat := unpackForestF 0x10fa1b42f4910981f 2 9
def r35_links : Nat → Nat → Option Nat := unpackLinksF 0x38e31c29301 0x410524a1f81b61721301f 6 3 9 3 4
def r35_trace := dagTraceF r35_mask r35_stock 8 r35_forest
def r35_check : Nat → Bool := dagCheckNodeF r35_mask r35_goal r35_bounds 6 r35_trace r35_links
set_option maxHeartbeats 0 in
theorem r35_roots : dagCheckRootsF r35_mask r35_goal r35_bounds
    (dagRefF 6 r35_trace r35_links 0) r35_stock 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r35_b0 : BlockChecked r35_check 0 6 := by decide +kernel
theorem r35_nodes : ∀ i, 0 ≤ i → i < 6 → r35_check i = true :=
  blockSpec r35_b0
theorem r35_known : KnownBin r35_bounds :=
  knownCons r33_lower (
  knownCons r18_lower (
  knownCons r13_lower (
  knownCons r34_lower (
  knownCons r2_lower (
  knownCons r4_lower (
  knownNil))))))
theorem r35_lower : LowerBin r35_mask r35_stock r35_goal 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r35_known r35_sub r35_goals r35_roots r35_nodes

def r36_mask : Nat := 0xffffffff00000000
def r36_stock : List Nat := [0xffff00000000, 0xff00ff00000000, 0xf0f0f0f00000000, 0x3333333300000000, 0x5555555500000000]
def r36_goal : Nat := 0x117175700000000
def r36_rows : Fin 64 → Fin 64 := decodeRows 0x821a29c31e398a3aabcb3ebb925b2dd35f3d9a7bafdb7fbf
set_option maxHeartbeats 0 in
theorem r36_lower : LowerBin r36_mask r36_stock r36_goal 9 :=
  relabelLower r36_rows r35_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r37_mask : Nat := 0x55005500aa00aa
def r37_stock : List Nat := [0xaa00aa, 0x55000000aa, 0x50005000a000a, 0x11001100220022]
def r37_goal : Nat := 0x1500550002002a
def r37_rows : Fin 64 → Fin 64 := decodeRows 0x5d54d10000001c50c1000000db4cb00000009a48a0
set_option maxHeartbeats 0 in
theorem r37_lower : LowerBin r37_mask r37_stock r37_goal 7 :=
  relabelLower r37_rows r13_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r38_mask : Nat := 0x50505050a0a0a0a
def r38_stock : List Nat := [0xa0a0a0a, 0x50500000a0a, 0x50005000a000a, 0x101010102020202]
def r38_goal : Nat := 0x10505050002020a
def r38_rows : Fin 64 → Fin 64 := decodeRows 0x6d94d10000002c90c1000000eb8cb0000000aa88a0
set_option maxHeartbeats 0 in
theorem r38_lower : LowerBin r38_mask r38_stock r38_goal 7 :=
  relabelLower r38_rows r13_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r39_mask : Nat := 0x1111111122222222
def r39_stock : List Nat := [0x22222222, 0x111100002222, 0x11001100220022, 0x101010102020202]
def r39_goal : Nat := 0x111111100020222
def r39_rows : Fin 64 → Fin 64 := decodeRows 0x759551000000349141000000f38d30000000b28920
set_option maxHeartbeats 0 in
theorem r39_lower : LowerBin r39_mask r39_stock r39_goal 7 :=
  relabelLower r39_rows r13_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r40_mask : Nat := 0x4444444488888888
def r40_stock : List Nat := [0x88888888, 0x444400008888, 0x44004400880088, 0x404040408080808]
def r40_goal : Nat := 0x4044400000008
def r40_rows : Fin 64 → Fin 64 := decodeRows 0x8a6aae000000cb6ebe0000000c72cf0000004d76df
set_option maxHeartbeats 0 in
theorem r40_lower : LowerBin r40_mask r40_stock r40_goal 7 :=
  relabelLower r40_rows r13_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r41_mask : Nat := 0x50505050a0a0a0a0
def r41_stock : List Nat := [0xa0a0a0a0, 0x50500000a0a0, 0x50005000a000a0, 0x1010101020202020]
def r41_goal : Nat := 0x10105000000020
def r41_rows : Fin 64 → Fin 64 := decodeRows 0x926b2e000000d36f3e00000014734f00000055775f
set_option maxHeartbeats 0 in
theorem r41_lower : LowerBin r41_mask r41_stock r41_goal 7 :=
  relabelLower r41_rows r13_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r42_mask : Nat := 0x55005500aa00aa00
def r42_stock : List Nat := [0xaa00aa00, 0x55000000aa00, 0x50005000a000a00, 0x1100110022002200]
def r42_goal : Nat := 0x100150000000200
def r42_rows : Fin 64 → Fin 64 := decodeRows 0xa2ab2e000000e3af3e00000024b34f00000065b75f
set_option maxHeartbeats 0 in
theorem r42_lower : LowerBin r42_mask r42_stock r42_goal 7 :=
  relabelLower r42_rows r13_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r43_mask : Nat := 0x55555555aaaaaaaa
def r43_stock : List Nat := [0xaaaaaaaa, 0x55550000aaaa, 0x55005500aa00aa, 0x50505050a0a0a0a, 0x1111111122222222]
def r43_goal : Nat := 0x11515550002022a
def r43_bounds : List (Nat × List Nat × Nat × Nat) := [(0x5555555500000000, [0x555500000000, 0x55005500000000, 0x505050500000000, 0x1111111100000000], 7, 0x115155500000000), (0xaaaaaaaa, [0xaaaa, 0xaa00aa, 0xa0a0a0a, 0x22222222], 7, 0x2022a), (0x55005500aa00aa, [0xaa00aa, 0x55000000aa, 0x50005000a000a, 0x11001100220022], 7, 0x1500550002002a), (0x50505050a0a0a0a, [0xa0a0a0a, 0x50500000a0a, 0x50005000a000a, 0x101010102020202], 7, 0x10505050002020a), (0x1111111122222222, [0x22222222, 0x111100002222, 0x11001100220022, 0x101010102020202], 7, 0x111111100020222), (0x4444444488888888, [0x88888888, 0x444400008888, 0x44004400880088, 0x404040408080808], 7, 0x4044400000008), (0x50505050a0a0a0a0, [0xa0a0a0a0, 0x50500000a0a0, 0x50005000a000a0, 0x1010101020202020], 7, 0x10105000000020), (0x55005500aa00aa00, [0xaa00aa00, 0x55000000aa00, 0x50005000a000a00, 0x1100110022002200], 7, 0x100150000000200)]
theorem r43_sub : ∀ b ∈ r43_bounds, r43_mask &&& b.1 = b.1 := by
  have hall : r43_bounds.all (fun b => Nat.beq (Nat.land r43_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r43_goals : ∀ b ∈ r43_bounds, canon b.1 r43_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r43_bounds.all (fun b => Nat.beq (canonF b.1 r43_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r43_forest : Nat → Nat × Nat := unpackForestF 0x1f 1 5
def r43_links : Nat → Nat → Option Nat := unpackLinksF 0x9 0x1f 2 1 5 1 2
def r43_trace := dagTraceF r43_mask r43_stock 9 r43_forest
def r43_check : Nat → Bool := dagCheckNodeF r43_mask r43_goal r43_bounds 1 r43_trace r43_links
set_option maxHeartbeats 0 in
theorem r43_roots : dagCheckRootsF r43_mask r43_goal r43_bounds
    (dagRefF 1 r43_trace r43_links 0) r43_stock 9 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r43_b0 : BlockChecked r43_check 0 1 := by decide +kernel
theorem r43_nodes : ∀ i, 0 ≤ i → i < 1 → r43_check i = true :=
  blockSpec r43_b0
theorem r43_known : KnownBin r43_bounds :=
  knownCons r14_lower (
  knownCons r33_lower (
  knownCons r37_lower (
  knownCons r38_lower (
  knownCons r39_lower (
  knownCons r40_lower (
  knownCons r41_lower (
  knownCons r42_lower (
  knownNil))))))))
theorem r43_lower : LowerBin r43_mask r43_stock r43_goal 10 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r43_known r43_sub r43_goals r43_roots r43_nodes

def r44_mask : Nat := 0x5500550055005500
def r44_stock : List Nat := [0x55005500, 0x550000005500, 0x500050005000500, 0x1100110011001100]
def r44_goal : Nat := 0x100150001005500
def r44_rows : Fin 64 → Fin 64 := decodeRows 0x218000a3800029a000aba00031c000b3c00039e000bbe000
set_option maxHeartbeats 0 in
theorem r44_lower : LowerBin r44_mask r44_stock r44_goal 5 :=
  relabelLower r44_rows r6_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r45_mask : Nat := 0xf0f0f0f00f0f0f0f
def r45_stock : List Nat := [0xf0f0f0f, 0xf0f000000f0f, 0xf000f0000f000f, 0x3030303003030303, 0x5050505005050505]
def r45_goal : Nat := 0x1010500107070f
def r45_rows : Fin 64 → Fin 64 := decodeRows 0xffe104f7c104df6104d74104bee104b6c1049e61049641041046da1046581044d21044501042ca1042481040c2104040
set_option maxHeartbeats 0 in
theorem r45_lower : LowerBin r45_mask r45_stock r45_goal 10 :=
  relabelLower r45_rows r28_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r46_mask : Nat := 0x5050505050505050
def r46_stock : List Nat := [0x50505050, 0x505000005050, 0x50005000500050, 0x1010101010101010]
def r46_goal : Nat := 0x10105000505050
def r46_rows : Fin 64 → Fin 64 := decodeRows 0x10c18e92c9ae00000000000051c59ed3cdbe000000000000
set_option maxHeartbeats 0 in
theorem r46_lower : LowerBin r46_mask r46_stock r46_goal 5 :=
  relabelLower r46_rows r2_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r47_mask : Nat := 0xa0a0a0a0a0a0a0a
def r47_stock : List Nat := [0xa0a0a0a, 0xa0a00000a0a, 0xa000a000a000a, 0x202020202020202]
def r47_goal : Nat := 0x202020002020a
def r47_rows : Fin 64 → Fin 64 := decodeRows 0xef90006d9000cf10004d1000ae90002c90008e10000c1000
set_option maxHeartbeats 0 in
theorem r47_lower : LowerBin r47_mask r47_stock r47_goal 5 :=
  relabelLower r47_rows r6_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r48_mask : Nat := 0xff00ff0000000000
def r48_stock : List Nat := [0xff0000000000, 0xf000f0000000000, 0x3300330000000000, 0x5500550000000000]
def r48_goal : Nat := 0x100170000000000
def r48_rows : Fin 64 → Fin 64 := decodeRows 0xa29aab000000b2dbaf000000e39ebb000000f3dfbf
set_option maxHeartbeats 0 in
theorem r48_lower : LowerBin r48_mask r48_stock r48_goal 7 :=
  relabelLower r48_rows r13_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r49_mask : Nat := 0xffff000000000000
def r49_stock : List Nat := [0xff000000000000, 0xf0f000000000000, 0x3333000000000000, 0x5555000000000000]
def r49_goal : Nat := 0x117000000000000
def r49_rows : Fin 64 → Fin 64 := decodeRows 0xc31cb3000000d35db7000000e39ebb000000f3dfbf
set_option maxHeartbeats 0 in
theorem r49_lower : LowerBin r49_mask r49_stock r49_goal 7 :=
  relabelLower r49_rows r13_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r50_mask : Nat := 0x4444444444444444
def r50_stock : List Nat := [0x44444444, 0x444400004444, 0x44004400440044, 0x404040404040404]
def r50_goal : Nat := 0x4044400444444
def r50_rows : Fin 64 → Fin 64 := decodeRows 0x8a18e8aa9ae00000000000049a59ecbadbe000000000000
set_option maxHeartbeats 0 in
theorem r50_lower : LowerBin r50_mask r50_stock r50_goal 5 :=
  relabelLower r50_rows r2_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r51_mask : Nat := 0xcc00cc00cc00cc
def r51_stock : List Nat := [0xcc00cc, 0xcc000000cc, 0xc000c000c000c, 0x44004400440044]
def r51_goal : Nat := 0x400440044004c
def r51_rows : Fin 64 → Fin 64 := decodeRows 0xdf6000cf20009e60008e20000000000000000000000000005d60004d20001c60000c2000
set_option maxHeartbeats 0 in
theorem r51_lower : LowerBin r51_mask r51_stock r51_goal 6 :=
  relabelLower r51_rows r0_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r52_mask : Nat := 0x5555000055550000
def r52_stock : List Nat := [0x55550000, 0x55000000550000, 0x505000005050000, 0x1111000011110000]
def r52_goal : Nat := 0x115000001550000
def r52_rows : Fin 64 → Fin 64 := decodeRows 0x418000c3800049a000cba00051c000d3c00059e000dbe000
set_option maxHeartbeats 0 in
theorem r52_lower : LowerBin r52_mask r52_stock r52_goal 5 :=
  relabelLower r52_rows r6_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r53_mask : Nat := 0x2222222222222222
def r53_stock : List Nat := [0x22222222, 0x222200002222, 0x22002200220022, 0x202020202020202]
def r53_goal : Nat := 0x2020200020222
def r53_rows : Fin 64 → Fin 64 := decodeRows 0xf79000759000d71000551000b69000349000961000141000
set_option maxHeartbeats 0 in
theorem r53_lower : LowerBin r53_mask r53_stock r53_goal 5 :=
  relabelLower r53_rows r6_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r54_mask : Nat := 0xaa00aa00aa00aa
def r54_stock : List Nat := [0xaa00aa, 0xaa000000aa, 0xa000a000a000a, 0x22002200220022]
def r54_goal : Nat := 0x200020002002a
def r54_rows : Fin 64 → Fin 64 := decodeRows 0xdf59e55d51c5000000000000cf18e14d10c1000000000000
set_option maxHeartbeats 0 in
theorem r54_lower : LowerBin r54_mask r54_stock r54_goal 5 :=
  relabelLower r54_rows r2_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r55_mask : Nat := 0xc0c0c0c0c0c0c0c
def r55_stock : List Nat := [0xc0c0c0c, 0xc0c00000c0c, 0xc000c000c000c, 0x404040404040404]
def r55_goal : Nat := 0x404040004040c
def r55_rows : Fin 64 → Fin 64 := decodeRows 0xefa0006da000cf20004d2000aea0002ca0008e20000c2000
set_option maxHeartbeats 0 in
theorem r55_lower : LowerBin r55_mask r55_stock r55_goal 5 :=
  relabelLower r55_rows r6_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r56_mask : Nat := 0xff00ff0000ff00ff
def r56_stock : List Nat := [0xff00ff, 0xff00000000ff, 0xf000f00000f000f, 0x3300330000330033, 0x5500550000550055]
def r56_goal : Nat := 0x10017000057007f
def r56_rows : Fin 64 → Fin 64 := decodeRows 0x1208083208105208187208411208493208515208597208208a29208aab208b2d208baf208e39208ebb208f3d208fbf
set_option maxHeartbeats 0 in
theorem r56_lower : LowerBin r56_mask r56_stock r56_goal 10 :=
  relabelLower r56_rows r28_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r57_mask : Nat := 0xc0c0c0c0c0c0c0c0
def r57_stock : List Nat := [0xc0c0c0c0, 0xc0c00000c0c0, 0xc000c000c000c0, 0x4040404040404040]
def r57_goal : Nat := 0x4000404040
def r57_rows : Fin 64 → Fin 64 := decodeRows 0x18738f59779f9a7bafdb7fbf
set_option maxHeartbeats 0 in
theorem r57_lower : LowerBin r57_mask r57_stock r57_goal 5 :=
  relabelLower r57_rows r4_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r58_mask : Nat := 0x3333000033330000
def r58_stock : List Nat := [0x33330000, 0x33000000330000, 0x303000003030000, 0x1111000011110000]
def r58_goal : Nat := 0x113000001130000
def r58_bounds : List (Nat × List Nat × Nat × Nat) := []
theorem r58_sub : ∀ b ∈ r58_bounds, r58_mask &&& b.1 = b.1 := by
  have hall : r58_bounds.all (fun b => Nat.beq (Nat.land r58_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r58_goals : ∀ b ∈ r58_bounds, canon b.1 r58_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r58_bounds.all (fun b => Nat.beq (canonF b.1 r58_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r58_forest : Nat → Nat × Nat := unpackForestF 0x1ee 1 4
def r58_links : Nat → Nat → Option Nat := unpackLinksF 0x882 0x3ee 4 2 4 1 3
def r58_trace := dagTraceF r58_mask r58_stock 3 r58_forest
def r58_check : Nat → Bool := dagCheckNodeF r58_mask r58_goal r58_bounds 2 r58_trace r58_links
set_option maxHeartbeats 0 in
theorem r58_roots : dagCheckRootsF r58_mask r58_goal r58_bounds
    (dagRefF 2 r58_trace r58_links 0) r58_stock 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r58_b0 : BlockChecked r58_check 0 2 := by decide +kernel
theorem r58_nodes : ∀ i, 0 ≤ i → i < 2 → r58_check i = true :=
  blockSpec r58_b0
theorem r58_known : KnownBin r58_bounds :=
  knownNil
theorem r58_lower : LowerBin r58_mask r58_stock r58_goal 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r58_known r58_sub r58_goals r58_roots r58_nodes

def r59_mask : Nat := 0x3300330033003300
def r59_stock : List Nat := [0x33003300, 0x330000003300, 0x300030003000300, 0x1100110011001100]
def r59_goal : Nat := 0x100130001001300
def r59_rows : Fin 64 → Fin 64 := decodeRows 0xf7c000e78000b6c000a6800000000000000000000000000075c00065800034c000248000000000000000000000000
set_option maxHeartbeats 0 in
theorem r59_lower : LowerBin r59_mask r59_stock r59_goal 4 :=
  relabelLower r59_rows r58_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r60_mask : Nat := 0xf000f000f000f0
def r60_stock : List Nat := [0xf000f0, 0xf0000000f0, 0x30003000300030, 0x50005000500050]
def r60_goal : Nat := 0x10005000500070
def r60_rows : Fin 64 → Fin 64 := decodeRows 0xdf6000d740009e60009640000000000000000000000000005d60005540001c6000144000
set_option maxHeartbeats 0 in
theorem r60_lower : LowerBin r60_mask r60_stock r60_goal 6 :=
  relabelLower r60_rows r0_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r61_mask : Nat := 0xff000000ff0000
def r61_stock : List Nat := [0xff0000, 0xf0000000f0000, 0x33000000330000, 0x55000000550000]
def r61_goal : Nat := 0x17000000570000
def r61_rows : Fin 64 → Fin 64 := decodeRows 0x411000c31000493000cb3000515000d35000597000db7000
set_option maxHeartbeats 0 in
theorem r61_lower : LowerBin r61_mask r61_stock r61_goal 5 :=
  relabelLower r61_rows r6_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r62_mask : Nat := 0xf0f0f0f000000000
def r62_stock : List Nat := [0xf0f000000000, 0xf000f000000000, 0x3030303000000000, 0x5050505000000000]
def r62_goal : Nat := 0x10105000000000
def r62_rows : Fin 64 → Fin 64 := decodeRows 0x9259a7b2dbafd35db7f3dfbf
set_option maxHeartbeats 0 in
theorem r62_lower : LowerBin r62_mask r62_stock r62_goal 5 :=
  relabelLower r62_rows r4_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r63_mask : Nat := 0x3030303030303030
def r63_stock : List Nat := [0x30303030, 0x303000003030, 0x30003000300030, 0x1010101010101010]
def r63_goal : Nat := 0x10101000101030
def r63_rows : Fin 64 → Fin 64 := decodeRows 0xf7c00075c000d74000554000b6c00034c000964000144000
set_option maxHeartbeats 0 in
theorem r63_lower : LowerBin r63_mask r63_stock r63_goal 5 :=
  relabelLower r63_rows r6_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r64_mask : Nat := 0x3333333300000000
def r64_stock : List Nat := [0x333300000000, 0x33003300000000, 0x303030300000000, 0x1111111100000000]
def r64_goal : Nat := 0x113131300000000
def r64_rows : Fin 64 → Fin 64 := decodeRows 0x821a29c31e39000000000000925b2dd35f3d000000000000
set_option maxHeartbeats 0 in
theorem r64_lower : LowerBin r64_mask r64_stock r64_goal 5 :=
  relabelLower r64_rows r2_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r65_mask : Nat := 0xf000f000f000f00
def r65_stock : List Nat := [0xf000f00, 0xf0000000f00, 0x300030003000300, 0x500050005000500]
def r65_goal : Nat := 0x100070001000700
def r65_rows : Fin 64 → Fin 64 := decodeRows 0xefa000e78000aea000a680000000000000000000000000006da0006580002ca000248000000000000000000000000
set_option maxHeartbeats 0 in
theorem r65_lower : LowerBin r65_mask r65_stock r65_goal 4 :=
  relabelLower r65_rows r58_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r66_mask : Nat := 0xf0f0f0f00000000
def r66_stock : List Nat := [0xf0f00000000, 0xf000f00000000, 0x303030300000000, 0x505050500000000]
def r66_goal : Nat := 0x107070700000000
def r66_rows : Fin 64 → Fin 64 := decodeRows 0x821a29c31e390000000000008a3aabcb3ebb000000000000
set_option maxHeartbeats 0 in
theorem r66_lower : LowerBin r66_mask r66_stock r66_goal 5 :=
  relabelLower r66_rows r2_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r67_mask : Nat := 0xf0f0f0f0
def r67_stock : List Nat := [0xf0f0, 0xf000f0, 0x30303030, 0x50505050]
def r67_goal : Nat := 0x505070
def r67_rows : Fin 64 → Fin 64 := decodeRows 0x7de00075c0005d60005540003ce00034c0001c6000144000
set_option maxHeartbeats 0 in
theorem r67_lower : LowerBin r67_mask r67_stock r67_goal 5 :=
  relabelLower r67_rows r6_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r68_mask : Nat := 0xffff0000
def r68_stock : List Nat := [0xff0000, 0xf0f0000, 0x33330000, 0x55550000]
def r68_goal : Nat := 0x1570000
def r68_rows : Fin 64 → Fin 64 := decodeRows 0x7de75c6da6580000000000005d65544d2450000000000000
set_option maxHeartbeats 0 in
theorem r68_lower : LowerBin r68_mask r68_stock r68_goal 5 :=
  relabelLower r68_rows r2_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r69_mask : Nat := 0xf0f00000f0f0000
def r69_stock : List Nat := [0xf0f0000, 0xf0000000f0000, 0x303000003030000, 0x505000005050000]
def r69_goal : Nat := 0x107000001070000
def r69_rows : Fin 64 → Fin 64 := decodeRows 0xefa000e78000cf2000c700000000000000000000000000006da0006580004d2000450000000000000000000000000
set_option maxHeartbeats 0 in
theorem r69_lower : LowerBin r69_mask r69_stock r69_goal 4 :=
  relabelLower r69_rows r58_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def r70_mask : Nat := 0xff00ff00000000
def r70_stock : List Nat := [0xff00000000, 0xf000f00000000, 0x33003300000000, 0x55005500000000]
def r70_goal : Nat := 0x17005700000000
def r70_rows : Fin 64 → Fin 64 := decodeRows 0x821000c310008a3000cb3000925000d350009a7000db7000
set_option maxHeartbeats 0 in
theorem r70_lower : LowerBin r70_mask r70_stock r70_goal 5 :=
  relabelLower r70_rows r6_lower (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem cert_known : KnownBin cert_bounds :=
  knownCons r10_lower (
  knownCons r11_lower (
  knownCons r12_lower (
  knownCons r9_lower (
  knownCons r15_lower (
  knownCons r16_lower (
  knownCons r17_lower (
  knownCons r29_lower (
  knownCons r30_lower (
  knownCons r31_lower (
  knownCons r32_lower (
  knownCons r36_lower (
  knownCons r35_lower (
  knownCons r43_lower (
  knownCons r14_lower (
  knownCons r44_lower (
  knownCons r5_lower (
  knownCons r45_lower (
  knownCons r33_lower (
  knownCons r46_lower (
  knownCons r1_lower (
  knownCons r18_lower (
  knownCons r47_lower (
  knownCons r48_lower (
  knownCons r13_lower (
  knownCons r49_lower (
  knownCons r50_lower (
  knownCons r51_lower (
  knownCons r52_lower (
  knownCons r53_lower (
  knownCons r54_lower (
  knownCons r55_lower (
  knownCons r3_lower (
  knownCons r56_lower (
  knownCons r28_lower (
  knownCons r57_lower (
  knownCons r0_lower (
  knownCons r59_lower (
  knownCons r60_lower (
  knownCons r61_lower (
  knownCons r62_lower (
  knownCons r4_lower (
  knownCons r8_lower (
  knownCons r63_lower (
  knownCons r64_lower (
  knownCons r65_lower (
  knownCons r23_lower (
  knownCons r66_lower (
  knownCons r7_lower (
  knownCons r34_lower (
  knownCons r6_lower (
  knownCons r67_lower (
  knownCons r68_lower (
  knownCons r58_lower (
  knownCons r69_lower (
  knownCons r70_lower (
  knownCons r2_lower (
  knownNil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem binaryLower : LowerBin cert_mask cert_stock cert_goal 13 :=
  cert_lower cert_known


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev X := Fin 6 → Bool
abbrev F := X → Bool

def target : F := fun x => Nat.testBit 18368186892755183744
  (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def witness : Circuit :=
  ⟨[
    ⟨.and, [3, 4]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.and, [5, 7]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.and, [2, 10]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.or, [6, 13]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [2, 11]⟩,
    ⟨.and, [14, 16]⟩,
    ⟨.or, [1, 17]⟩,
    ⟨.and, [15, 18]⟩], 19⟩

theorem witness_mono : Monotone2 witness := by simp [Monotone2, witness]

theorem witness_size : witness.size = 14 := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem witness_eval : ∀ x : X, witness.eval (List.ofFn x) = target x := by
  decide +kernel

theorem binaryLowerRoot : LowerBin fullMask rootStock (canon fullMask 18368186892755183744) 13 := by
  intro vs hbuild hhit
  have hstock : ∀ w ∈ rootStock, w ∈ cert_stock := by
    have hall : rootStock.all (fun i => cert_stock.contains i) = true := by decide +kernel
    intro w hw
    exact List.contains_iff_mem.mp (List.all_eq_true.mp hall w hw)
  have hbuild' := builds_weaken hstock hbuild
  have hhit' : Avail (vs ++ cert_stock) (canon fullMask 18368186892755183744) :=
    avail_weaken (fun w hw => by
      rcases List.mem_append.mp hw with hv | hs
      · exact List.mem_append_left _ hv
      · exact List.mem_append_right _ (hstock w hs)) hhit
  exact binaryLower vs hbuild' hhit'

end PEqualNP.Outside.L_meta_48488

theorem PEqualNP.Outside.L_meta_48488 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6
      (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 4272466048)
        (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s →
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 4272466048)
        (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_48488.table2_from_lowerBin 18368186892755183744 14
    PEqualNP.Outside.L_meta_48488.binaryLowerRoot PEqualNP.Outside.L_meta_48488.witness.gates PEqualNP.Outside.L_meta_48488.witness.output
    PEqualNP.Outside.L_meta_48488.witness_size PEqualNP.Outside.L_meta_48488.witness_mono PEqualNP.Outside.L_meta_48488.witness_eval

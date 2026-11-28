import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49265

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

theorem masked_zero (mask : Nat) : Masked mask 0 := by
  unfold Masked; simp

theorem masked_self (mask : Nat) : Masked mask mask := by
  unfold Masked; simp

theorem masked_land_right (mask w : Nat) : Masked mask (w &&& mask) := by
  unfold Masked; apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and]

theorem masked_xor {mask a b : Nat} (ha : Masked mask a) (hb : Masked mask b) :
    Masked mask (a ^^^ b) := by
  unfold Masked at ha hb ⊢
  apply Nat.eq_of_testBit_eq; intro i
  have ea := congrArg (fun x => x.testBit i) ha
  have eb := congrArg (fun x => x.testBit i) hb
  simp only [Nat.testBit_and, Nat.testBit_xor] at ea eb ⊢
  cases hm : mask.testBit i <;> simp_all

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

theorem canon_masked (mask w : Nat) : Masked mask (canon mask w) := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · rw [h0]; exact masked_zero mask
  · rw [h1]; exact masked_land_right mask w
  · rw [h2]; exact masked_xor (masked_self mask) (masked_land_right mask w)

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

def boundCloses (target : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, stock, lower, goal) := bound
  let (fuel, ws, hist) := state
  Nat.beq (canon cut target) goal && !(Nat.beq goal 0) &&
    forceW (fuel - flatCount cut ws) (fun rem =>
      if Nat.blt rem lower then
        forceWs (recipeStart cut stock ws) (fun start =>
          if Nat.blt (start.length + rem) lower then
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
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  simp only [Bool.and_eq_true, Nat.blt_eq] at scan
  obtain ⟨hlen, hsrc⟩ := scan
  set replay := replayRec cut (recipeClose cut stock hist (recipeStart cut stock ws)) hist.reverse stock
  have hgnf : canon cut goal ≠ 0 := hgeq.symm ▸ hgnz'
  have hsup : ∀ w ∈ ws.toFinset, Avail (replay ++ stock) (canon cut w) := by
    intro w hw
    exact availB_spec.mp (List.all_eq_true.mp hsrc w (List.mem_toFinset.mp hw))
  obtain ⟨ys, hylen, hybd, hyhit⟩ := maskedBuildBin sub hgnf hlive (replay ++ stock) hsup
  rw [← flatCount_card cut nd] at hylen
  have hboth := builds_append (replayRec_builds cut _ hist.reverse stock) hybd
  have hfinal : Avail ((replay ++ ys) ++ stock) bgoal := by
    rw [← hgeq]
    exact avail_weaken (fun u hu => by simp only [List.mem_append] at hu ⊢; tauto) hyhit
  have heno := hlow (replay ++ ys) hboth hfinal
  simp only [List.length_append] at heno
  omega

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

theorem block_join {a m b : Nat} {f : Nat → Bool}
    (h1 : ∀ i, a ≤ i → i < m → f i = true)
    (h2 : ∀ i, m ≤ i → i < b → f i = true) :
    ∀ i, a ≤ i → i < b → f i = true := by
  intro i hi1 hi2
  by_cases h : i < m
  · exact h1 i hi1 h
  · exact h2 i (by omega) hi2

def dagRef (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (parent token : Nat)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  match links parent token with
  | none => false
  | some dest =>
    Nat.blt dest count &&
      match states dest with
      | none => false
      | some saved => Nat.beq saved.1 state.1 && (saved.2.1 == state.2.1)

def dagCheckChildren (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
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
                        dagLocal mask goal bounds ch || ref (makeToken a b op keep) ch))))))))

def dagCheckNode (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildren mask goal bounds (dagRef count states links (i + 1)) st

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

theorem dagAllNodes {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1) (snd : stock.Nodup)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNode mask goal bounds count
      (dagTrace mask stock fuel forest) links i = true) :
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
    unfold dagCheckNode at hchk
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
          · have hopen := dagLocal_open (state := (rem - 1, ws', (z, x, y) :: hist)) hgm hknown hsub hnd' (k := k') (by omega) hlive'
            rw [hopen] at hloc; exact Bool.noConfusion hloc
          · unfold dagRef at href
            split at href
            · contradiction
            · rename_i dest _
              simp only [Bool.and_eq_true, Nat.blt_eq] at href
              obtain ⟨hdest, hst⟩ := href
              cases htr2 : dagTrace mask stock fuel forest dest with
              | none => rw [htr2] at hst; contradiction
              | some saved =>
                rw [htr2] at hst
                simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hst
                obtain ⟨hfEq, hwEq⟩ := hst
                have hbelow : rem - 1 < cap := by omega
                exact ih (rem - 1) hbelow dest saved hdest htr2 hfEq k' (by omega) (hwEq ▸ hlive')

theorem lowerDag {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hroots : dagCheckRoots mask goal bounds
      (dagRef count (dagTrace mask stock fuel forest) links 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNode mask goal bounds count
      (dagTrace mask stock fuel forest) links i = true) :
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
  · unfold dagRef at href
    split at href
    · contradiction
    · rename_i dest _
      simp only [Bool.and_eq_true, Nat.blt_eq] at href
      obtain ⟨hdest, hst⟩ := href
      cases htr : dagTrace mask stock fuel forest dest with
      | none => rw [htr] at hst; contradiction
      | some saved =>
        rw [htr] at hst
        simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hst
        obtain ⟨hfEq, hwEq⟩ := hst
        exact dagAllNodes hgm hknown hsub snd hnodes fuel dest saved hdest htr hfEq k (by omega) (hwEq ▸ hlive')

def unpack (data width idx : Nat) : Nat :=
  (data >>> (idx * width)) &&& ((1 <<< width) - 1)

def unpackForest (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := pBits + tBits
  let code := unpack data w i
  (code >>> tBits, code &&& ((1 <<< tBits) - 1))

def unpackLinks (index data idxW sizeBits tokBits destBits steps : Nat) : Nat → Nat → Option Nat :=
  fun parent tok =>
    let entry := unpack index idxW parent
    let sz := entry &&& ((1 <<< sizeBits) - 1)
    let off := entry >>> sizeBits
    let w := tokBits + destBits
    (Nat.rec (motive := fun _ => Nat → Nat → Option Nat) (fun _ _ => none)
      (fun _ next lo hi =>
        if Nat.blt lo hi then
          let mid := (lo + hi) / 2
          let code := unpack data w mid
          let key := code &&& ((1 <<< tokBits) - 1)
          if Nat.beq tok key then some (code >>> tokBits)
          else if Nat.blt tok key then next lo mid else next (mid + 1) hi
        else none) steps) off (off + sz)

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
          (forceWs (recipeCloseF cut stock hist start) (fun needed =>
            Bool.rec false
              (forceWs (replayRecF cut needed (revAccN hist []) stock) (fun replay =>
                Bool.rec false
                  (allN (fun w => availBF (appN replay stock) (canonF cut w)) ws)
                  (Nat.blt (Nat.add (lenN replay) rem) lower)))
              (Nat.blt (Nat.add (lenN needed) rem) lower)))
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
    · cases Nat.blt ((recipeClose cut stock hist (recipeStart cut stock ws)).length + (fuel - flatCount cut ws)) lower
      · rfl
      · cases Nat.blt ((replayRec cut (recipeClose cut stock hist (recipeStart cut stock ws)) hist.reverse stock).length + (fuel - flatCount cut ws)) lower <;> rfl

def knownClosesF (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  List.rec false (fun b _ rest => Bool.rec rest true (boundClosesF state b)) bounds

theorem knownClosesF_eq {target : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 target = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    knownClosesF bounds state = knownCloses target bounds state := by
  induction bounds with
  | nil => rfl
  | cons b bs ih =>
    change Bool.rec (knownClosesF bs state) true (boundClosesF state b) =
      (boundCloses target state b || knownCloses target bs state)
    have h0 := hgoals b List.mem_cons_self
    rw [boundClosesF_eq h0.1 h0.2, ih (fun x hx => hgoals x (List.mem_cons_of_mem _ hx))]
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

theorem knownCloses_of_mem {target : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {state : Nat × List Nat × List (Nat × Nat × Nat)} {b : Nat × List Nat × Nat × Nat}
    (hmem : b ∈ bounds) (hb : boundCloses target state b = true) :
    knownCloses target bounds state = true := by
  induction bounds with
  | nil => cases hmem
  | cons x xs ih =>
    change (boundCloses target state x || knownCloses target xs state) = true
    rcases List.mem_cons.mp hmem with rfl | htl
    · rw [hb]; rfl
    · rw [ih htl]; cases boundCloses target state x <;> rfl

theorem treeBlock_mono {lo hi : Nat} {f g : Nat → Bool}
    (hf : treeBlock lo hi f = true)
    (himp : ∀ i, lo ≤ i → i < hi → f i = true → g i = true) :
    treeBlock lo hi g = true := by
  unfold treeBlock at hf ⊢
  suffices ∀ steps a b,
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b = true →
      (∀ i, a ≤ i → i < b → f i = true → g i = true) →
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then g x else next x m && next m y
          else true) steps) a b = true from
    this (hi - lo + 1) lo hi hf himp
  intro steps
  induction steps with
  | zero => intro a b _ _; rfl
  | succ s ih =>
    intro a b h hfg
    dsimp only at h ⊢
    cases hlt : Nat.blt a b
    · rfl
    · simp only [hlt, ite_true] at h ⊢
      have hab : a < b := Nat.blt_eq.mp hlt
      cases heq : Nat.beq a ((a + b) / 2)
      · simp only [heq, Bool.false_eq_true, ite_false, Bool.and_eq_true] at h ⊢
        exact ⟨ih a ((a + b) / 2) h.1 (fun i h1 h2 => hfg i h1 (by omega)),
               ih ((a + b) / 2) b h.2 (fun i h1 h2 => hfg i (by omega) h2)⟩
      · simp only [heq, ite_true] at h ⊢
        exact hfg a (Nat.le_refl a) hab h

def nthBound (bounds : List (Nat × List Nat × Nat × Nat)) (i : Nat) :
    Option (Nat × List Nat × Nat × Nat) :=
  (List.rec (motive := fun _ => Nat → Option (Nat × List Nat × Nat × Nat))
    (fun _ => none)
    (fun b _ ih k => Nat.rec (some b) (fun m _ => ih m) k) bounds) i

theorem nthBound_mem {bounds : List (Nat × List Nat × Nat × Nat)} {i : Nat} {b : Nat × List Nat × Nat × Nat}
    (h : nthBound bounds i = some b) : b ∈ bounds := by
  induction bounds generalizing i with
  | nil => simp [nthBound] at h
  | cons x xs ih =>
    cases i with
    | zero => cases h; exact List.mem_cons_self
    | succ m => exact List.mem_cons_of_mem _ (ih h)

def knownClosesTopF (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  match bounds with
  | [] => false
  | b0 :: rest =>
    Bool.rec
      (match rest with
       | [] => false
       | b1 :: rest1 =>
         Bool.rec
           (match rest1 with
            | [] => false
            | b2 :: _ => boundClosesF state b2)
           true (boundClosesF state b1))
      true (boundClosesF state b0)

theorem knownClosesTopF_imp {target : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 target = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    {state : Nat × List Nat × List (Nat × Nat × Nat)}
    (h : knownClosesTopF bounds state = true) :
    knownCloses target bounds state = true := by
  cases bounds with
  | nil => exact Bool.noConfusion h
  | cons b0 rest =>
    unfold knownClosesTopF at h; dsimp only at h
    have h0 := hgoals b0 List.mem_cons_self
    cases hb0 : boundClosesF state b0
    · rw [hb0] at h; dsimp only at h
      cases rest with
      | nil => exact Bool.noConfusion h
      | cons b1 rest1 =>
        dsimp only at h
        have h1 := hgoals b1 (List.mem_cons_of_mem _ List.mem_cons_self)
        cases hb1 : boundClosesF state b1
        · rw [hb1] at h; dsimp only at h
          cases rest1 with
          | nil => exact Bool.noConfusion h
          | cons b2 rest2 =>
            dsimp only at h
            have h2 := hgoals b2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
            rw [boundClosesF_eq h2.1 h2.2] at h
            exact knownCloses_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) h
        · rw [boundClosesF_eq h1.1 h1.2] at hb1
          exact knownCloses_of_mem (List.mem_cons_of_mem _ List.mem_cons_self) hb1
    · rw [boundClosesF_eq h0.1 h0.2] at hb0
      exact knownCloses_of_mem List.mem_cons_self hb0

def edgeAxis (mask goal stride lm : Nat) : Nat :=
  let neg := Nat.xor mask goal
  Nat.land (Nat.lor (Nat.land (Nat.shiftRight goal stride) neg)
    (Nat.land goal (Nat.shiftRight neg stride))) lm

def edgePack (mask goal : Nat) : Nat :=
  Nat.lor (edgeAxis mask goal 1 0x5555555555555555)
    (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 2 0x3333333333333333) 64)
      (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 4 0x0f0f0f0f0f0f0f0f) 128)
        (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 8 0x00ff00ff00ff00ff) 192)
          (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 16 0x0000ffff0000ffff) 256)
            (Nat.shiftLeft (edgeAxis mask goal 32 0x00000000ffffffff) 320)))))

def sepAxis (stride lm w : Nat) : Nat :=
  Nat.land (Nat.xor (Nat.shiftRight w stride) w) lm

def sepPack (w : Nat) : Nat :=
  Nat.lor (sepAxis 1 0x5555555555555555 w)
    (Nat.lor (Nat.shiftLeft (sepAxis 2 0x3333333333333333 w) 64)
      (Nat.lor (Nat.shiftLeft (sepAxis 4 0x0f0f0f0f0f0f0f0f w) 128)
        (Nat.lor (Nat.shiftLeft (sepAxis 8 0x00ff00ff00ff00ff w) 192)
          (Nat.lor (Nat.shiftLeft (sepAxis 16 0x0000ffff0000ffff w) 256)
            (Nat.shiftLeft (sepAxis 32 0x00000000ffffffff w) 320)))))

def orSep (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ ih => Nat.lor (sepPack w) ih) ws

theorem edgeAxis_live {mask goal stride lm k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset)
    {n : Nat} (he : (edgeAxis mask goal stride lm).testBit n = true) :
    ∃ w ∈ ws, (sepAxis stride lm w).testBit n = true := by
  unfold edgeAxis at he
  change (((goal >>> stride &&& (mask ^^^ goal)) ||| (goal &&& ((mask ^^^ goal) >>> stride))) &&& lm).testBit n = true at he
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight, Bool.and_eq_true, Bool.or_eq_true] at he
  obtain ⟨hcases, hlm⟩ := he
  have hpm : ∀ j, goal.testBit j = true → mask.testBit j = true := fun j hg => by
    have e := congrArg (fun x => x.testBit j) hgm
    simp only [Nat.testBit_and, hg, Bool.true_and] at e; exact e
  have hnm : ∀ j, (mask ^^^ goal).testBit j = true → mask.testBit j = true ∧ goal.testBit j = false := fun j hn => by
    rw [Nat.testBit_xor] at hn
    cases hm : mask.testBit j <;> cases hg : goal.testBit j <;> simp_all
  have hsep : ∃ w ∈ ws, w.testBit (stride + n) ≠ w.testBit n := by
    by_contra! hall
    rcases hcases with ⟨hg1, hn0⟩ | ⟨hg0, hn1⟩
    · have h1 := hpm (stride + n) hg1
      have h0 := hnm n hn0
      have eq := liveBin_agrees h1 h0.1 hlive (fun w hw => hall w (List.mem_toFinset.mp hw))
      rw [hg1, h0.2] at eq; exact Bool.noConfusion eq
    · have h0 := hpm n hg0
      have h1 := hnm (stride + n) hn1
      have eq := liveBin_agrees h0 h1.1 hlive (fun w hw => (hall w (List.mem_toFinset.mp hw)).symm)
      rw [hg0, h1.2] at eq; exact Bool.noConfusion eq
  obtain ⟨w, hw, hne⟩ := hsep
  refine ⟨w, hw, ?_⟩
  unfold sepAxis
  change (((w >>> stride) ^^^ w) &&& lm).testBit n = true
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight, hlm, Bool.and_true]
  cases hb1 : w.testBit (stride + n) <;> cases hb2 : w.testBit n <;> simp_all

theorem orSep_testBit {ws : List Nat} {w j : Nat}
    (hw : w ∈ ws) (hb : (sepPack w).testBit j = true) : (orSep ws).testBit j = true := by
  induction ws with
  | nil => cases hw
  | cons x xs ih =>
    change (sepPack x ||| orSep xs).testBit j = true
    rw [Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.mp hw with rfl | htl
    · exact Or.inl hb
    · exact Or.inr (ih htl)

theorem sepPack_live {mask goal k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset) :
    Nat.beq (Nat.land (edgePack mask goal) (orSep ws)) (edgePack mask goal) = true := by
  apply Nat.beq_eq.mpr
  apply Nat.eq_of_testBit_eq; intro j
  change ((edgePack mask goal) &&& (orSep ws)).testBit j = (edgePack mask goal).testBit j
  rw [Nat.testBit_and]
  cases he : (edgePack mask goal).testBit j
  · rfl
  · simp only [Bool.true_and]
    have hlane (stride lm shift : Nat)
        (hl : (edgeAxis mask goal stride lm <<< shift).testBit j = true)
        (hs : ∀ w, (sepAxis stride lm w <<< shift).testBit j = true → (sepPack w).testBit j = true) :
        (orSep ws).testBit j = true := by
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at hl
      obtain ⟨w, hw, hsw⟩ := edgeAxis_live hgm hlive hl.2
      apply orSep_testBit hw
      apply hs w
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hl.1, hsw⟩
    unfold edgePack at he
    change (edgeAxis mask goal 1 0x5555555555555555 |||
      ((edgeAxis mask goal 2 0x3333333333333333 <<< 64) |||
        ((edgeAxis mask goal 4 0x0f0f0f0f0f0f0f0f <<< 128) |||
          ((edgeAxis mask goal 8 0x00ff00ff00ff00ff <<< 192) |||
            ((edgeAxis mask goal 16 0x0000ffff0000ffff <<< 256) |||
              (edgeAxis mask goal 32 0x00000000ffffffff <<< 320)))))).testBit j = true at he
    simp only [Nat.testBit_or, Bool.or_eq_true] at he
    rcases he with h0 | h1 | h2 | h3 | h4 | h5
    · obtain ⟨w, hw, hsw⟩ := edgeAxis_live hgm hlive h0
      exact orSep_testBit hw (by
        unfold sepPack
        change (sepAxis 1 0x5555555555555555 w ||| _).testBit j = true
        simp [Nat.testBit_or, hsw])
    · exact hlane 2 0x3333333333333333 64 h1 (fun w hw => by
        unfold sepPack
        change (_ ||| ((sepAxis 2 0x3333333333333333 w <<< 64) ||| _)).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 4 0x0f0f0f0f0f0f0f0f 128 h2 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| ((sepAxis 4 0x0f0f0f0f0f0f0f0f w <<< 128) ||| _))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 8 0x00ff00ff00ff00ff 192 h3 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| ((sepAxis 8 0x00ff00ff00ff00ff w <<< 192) ||| _)))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 16 0x0000ffff0000ffff 256 h4 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| (_ ||| ((sepAxis 16 0x0000ffff0000ffff w <<< 256) ||| _))))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 32 0x00000000ffffffff 320 h5 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| (_ ||| (_ ||| (sepAxis 32 0x00000000ffffffff w <<< 320)))))).testBit j = true
        simp [Nat.testBit_or, hw])

def mapSep (ws : List Nat) : List (Nat × Nat) :=
  List.rec [] (fun w _ ih => (w, sepPack w) :: ih) ws

def forceSepPairs : List Nat → (List (Nat × Nat) → Bool) → Bool
  | [], k => k []
  | w :: ws, k => forceW (sepPack w) (fun sp => forceSepPairs ws (fun rest => k ((w, sp) :: rest)))

theorem forceSepPairs_eq (ws : List Nat) (k : List (Nat × Nat) → Bool) :
    forceSepPairs ws k = k (mapSep ws) := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceW (sepPack w) (fun sp => forceSepPairs ws (fun rest => k ((w, sp) :: rest))) = _
    rw [forceW_eq, ih]; rfl

def orSepAll (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Nat.lor p.2 ih) ps

def orSepSkip (x : Nat) (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Bool.rec (Nat.lor p.2 ih) ih (Nat.beq p.1 x)) ps

def orSepSkip2 (x y : Nat) (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Bool.rec (Bool.rec (Nat.lor p.2 ih) ih (Nat.beq p.1 y)) ih (Nat.beq p.1 x)) ps

theorem orSepAll_mapSep (ws : List Nat) : orSepAll (mapSep ws) = orSep ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => change Nat.lor (sepPack w) (orSepAll (mapSep ws)) = Nat.lor (sepPack w) (orSep ws); rw [ih]

theorem orSepSkip_mapSep (x : Nat) (ws : List Nat) :
    orSepSkip x (mapSep ws) = orSep (dropVal true x ws) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (Nat.lor (sepPack w) (orSepSkip x (mapSep ws))) (orSepSkip x (mapSep ws)) (Nat.beq w x) =
      orSep (bsel (Nat.beq w x) (dropVal true x ws) (w :: dropVal true x ws))
    rw [ih]
    cases Nat.beq w x <;> rfl

theorem dropVal_comm (x y : Nat) (l : List Nat) :
    dropVal true y (dropVal true x l) = dropVal true x (dropVal true y l) := by
  induction l with
  | nil => rfl
  | cons u us ih =>
    change dropVal true y (bsel (Nat.beq u x) (dropVal true x us) (u :: dropVal true x us)) =
      dropVal true x (bsel (Nat.beq u y) (dropVal true y us) (u :: dropVal true y us))
    cases hux : Nat.beq u x <;> cases huy : Nat.beq u y
    · simp only [bsel_false]
      change bsel (Nat.beq u y) (dropVal true y (dropVal true x us)) (u :: dropVal true y (dropVal true x us)) =
        bsel (Nat.beq u x) (dropVal true x (dropVal true y us)) (u :: dropVal true x (dropVal true y us))
      rw [huy, hux, bsel_false, bsel_false, ih]
    · simp only [bsel_false, bsel_true]
      change bsel (Nat.beq u y) (dropVal true y (dropVal true x us)) (u :: dropVal true y (dropVal true x us)) = _
      rw [huy, bsel_true, ih]
    · simp only [bsel_true, bsel_false]
      change _ = bsel (Nat.beq u x) (dropVal true x (dropVal true y us)) (u :: dropVal true x (dropVal true y us))
      rw [hux, bsel_true, ih]
    · simp only [bsel_true]; exact ih

theorem orSepSkip2_mapSep (x y : Nat) (ws : List Nat) :
    orSepSkip2 x y (mapSep ws) = orSep (dropVal true y (dropVal true x ws)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (Nat.lor (sepPack w) (orSepSkip2 x y (mapSep ws))) (orSepSkip2 x y (mapSep ws)) (Nat.beq w y))
      (orSepSkip2 x y (mapSep ws)) (Nat.beq w x) =
      orSep (dropVal true y (bsel (Nat.beq w x) (dropVal true x ws) (w :: dropVal true x ws)))
    rw [ih]
    cases hx : Nat.beq w x
    · rw [bsel_false]
      change Bool.rec (Nat.lor (sepPack w) (orSep (dropVal true y (dropVal true x ws))))
        (orSep (dropVal true y (dropVal true x ws))) (Nat.beq w y) =
        orSep (bsel (Nat.beq w y) (dropVal true y (dropVal true x ws)) (w :: dropVal true y (dropVal true x ws)))
      cases Nat.beq w y <;> rfl
    · rw [bsel_true]

def treeBlockF (lo hi : Nat) (f : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      Bool.rec true
        (let m := Nat.shiftRight (Nat.add a b) 1
         Bool.rec (Bool.rec false (next m b) (next a m)) (f a) (Nat.beq a m))
        (Nat.blt a b)) (Nat.add (Nat.sub hi lo) 1)) lo hi

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

theorem treeBlockF_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlockF lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  rw [treeBlockF_eq] at h; exact treeBlock_at h

def forceWC (w : Nat) (k : Nat → Bool × List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  match w with
  | 0 => k 0
  | m + 1 => k (m + 1)

theorem forceWC_eq (w : Nat) (k : Nat → Bool × List (Nat × Nat)) : forceWC w k = k w := by
  cases w <;> rfl

def closeFallbackV4 (mask goal ep : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (st : Nat × List Nat × List (Nat × Nat × Nat)) (sp : Nat) : Bool :=
  Bool.rec true
    (Bool.rec
      (Bool.rec true false (dagPartF st.2.1 goal (Nat.xor mask goal)))
      true (knownClosesTopF bounds st))
    (Nat.beq (Nat.land ep sp) ep)

theorem closeFallbackV4_open {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {st : Nat × List Nat × List (Nat × Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (nd : st.2.1.Nodup) {k : Nat} (hk : k ≤ st.1)
    (hlive : LiveBin mask goal k st.2.1.toFinset) :
    closeFallbackV4 mask goal (edgePack mask goal) bounds st (orSep st.2.1) = false := by
  unfold closeFallbackV4
  have hsp : Nat.beq (Nat.land (edgePack mask goal) (orSep st.2.1)) (edgePack mask goal) = true :=
    sepPack_live hgm hlive
  have hkt : knownClosesTopF bounds st = false := by
    cases h : knownClosesTopF bounds st
    · rfl
    · have hk1 := knownClosesTopF_imp hgoals h
      have hk0 := knownCloses_sound hknown hsub nd hk hlive
      rw [hk0] at hk1; exact Bool.noConfusion hk1
  have hdp : dagPartF st.2.1 goal (Nat.xor mask goal) = true := by
    have heq : dagPartF st.2.1 goal (Nat.xor mask goal) = dagPart st.2.1 goal (mask ^^^ goal) :=
      dagPartF_eq st.2.1 goal (mask ^^^ goal)
    rw [heq]; exact dagPart_live hgm hlive
  rw [hsp, hkt, hdp]

def stepLeafV4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel1 z spZ baseSp : Nat) (rest : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tok : Nat) (cur : List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  match cur with
  | (t, code) :: tl =>
    Bool.rec
      (closeFallbackV4 mask goal ep bounds (fuel1, z :: rest, hist1) (Nat.lor spZ baseSp), cur)
      (Bool.rec
        (match nthBound bounds (Nat.shiftRight code 1) with
         | none => (false, tl)
         | some b => (boundClosesF (fuel1, z :: rest, hist1) b, tl))
        (let dest := Nat.shiftRight code 1
         let ok := Bool.rec false
           (match states dest with
            | none => false
            | some saved => Bool.rec false (eqListN saved.2.1 (insertSortedF z rest)) (Nat.beq saved.1 fuel1))
           (Nat.blt dest count)
         (ok, tl))
        (Nat.beq (Nat.land code 1) 0))
      (Nat.beq tok t)
  | [] =>
    (closeFallbackV4 mask goal ep bounds (fuel1, z :: rest, hist1) (Nat.lor spZ baseSp), [])

theorem stepLeafV4_ref {mask goal count fuel1 z tok : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {rest : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (nd : (z :: rest).Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k (z :: rest).toFinset)
    (h : (stepLeafV4 mask goal (edgePack mask goal) count bounds states fuel1 z (sepPack z) (orSep rest) rest hist1 tok cur).1 = true) :
    ∃ dest < count, ∃ saved, states dest = some saved ∧ saved.1 = fuel1 ∧ saved.2.1 = insertSorted z rest := by
  have hfb : closeFallbackV4 mask goal (edgePack mask goal) bounds (fuel1, z :: rest, hist1) (Nat.lor (sepPack z) (orSep rest)) = false :=
    closeFallbackV4_open (st := (fuel1, z :: rest, hist1)) hgm hknown hsub hgoals nd hk hlive
  unfold stepLeafV4 at h
  cases cur with
  | nil => dsimp only at h; rw [hfb] at h; exact Bool.noConfusion h
  | cons hd tl =>
    obtain ⟨t, code⟩ := hd
    dsimp only at h
    cases ht : Nat.beq tok t
    · rw [ht] at h; dsimp only at h; rw [hfb] at h; exact Bool.noConfusion h
    · rw [ht] at h; dsimp only at h
      cases hev : Nat.beq (Nat.land code 1) 0
      · rw [hev] at h; dsimp only at h
        cases hb : nthBound bounds (Nat.shiftRight code 1) with
        | none => rw [hb] at h; exact Bool.noConfusion h
        | some b =>
          rw [hb] at h; dsimp only at h
          have hmem := nthBound_mem hb
          have hg := hgoals b hmem
          rw [boundClosesF_eq hg.1 hg.2] at h
          have h0 := boundCloses_sound (state := (fuel1, z :: rest, hist1)) (hknown b hmem) (hsub b hmem) nd hk hlive
          rw [h0] at h; exact Bool.noConfusion h
      · rw [hev] at h; dsimp only at h
        cases hlt : Nat.blt (Nat.shiftRight code 1) count
        · rw [hlt] at h; exact Bool.noConfusion h
        · rw [hlt] at h; dsimp only at h
          cases hst : states (Nat.shiftRight code 1) with
          | none => rw [hst] at h; exact Bool.noConfusion h
          | some saved =>
            rw [hst] at h; dsimp only at h
            cases hf : Nat.beq saved.1 fuel1
            · rw [hf] at h; exact Bool.noConfusion h
            · rw [hf] at h; dsimp only at h
              rw [eqListN_eq, insertSortedF_eq, beq_iff_eq] at h
              exact ⟨Nat.shiftRight code 1, Nat.blt_eq.mp hlt, saved, hst, Nat.beq_eq.mp hf, h⟩

def checkKeepsV4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n z spZ spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tokBase : Nat) (cur : List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  let (ok0, c1) : Bool × List (Nat × Nat) := Bool.rec
    (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur)
    (true, cur) (Nat.blt fuel (Nat.sub n 1))
  Bool.rec (false, c1)
    (let (ok1, c2) : Bool × List (Nat × Nat) := Bool.rec
       (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1)
       (true, c1) (Nat.blt fuel n)
     Bool.rec (false, c2)
       (let (ok2, c3) : Bool × List (Nat × Nat) := Bool.rec
          (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2)
          (true, c2) (Nat.blt fuel n)
        Bool.rec (false, c3)
          (Bool.rec
            (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spAll ws0 hist1 (Nat.add tokBase 3) c3)
            (true, c3) (Nat.blt fuel (Nat.add n 1)))
          ok2)
       ok1)
    ok0

theorem checkKeepsV4_at {mask goal ep count fuel fuel1 n z spZ spAll spNoA spNoB spNoAB tokBase : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)}
    (h : (checkKeepsV4 mask goal ep count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
      ws0 wsNoA wsNoB wsNoAB hist1 tokBase cur).1 = true)
    (keepA keepB : Bool) :
    match keepA, keepB with
    | false, false => Nat.blt fuel (n - 1) = true ∨ ∃ c, (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase c).1 = true
    | true, false => Nat.blt fuel n = true ∨ ∃ c, (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoB wsNoB hist1 (tokBase + 1) c).1 = true
    | false, true => Nat.blt fuel n = true ∨ ∃ c, (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoA wsNoA hist1 (tokBase + 2) c).1 = true
    | true, true => Nat.blt fuel (n + 1) = true ∨ ∃ c, (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spAll ws0 hist1 (tokBase + 3) c).1 = true := by
  unfold checkKeepsV4 at h
  generalize hp0 : (Bool.rec (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur)
    (true, cur) (Nat.blt fuel (Nat.sub n 1)) : Bool × List (Nat × Nat)) = p0 at h
  obtain ⟨ok0, c1⟩ := p0
  dsimp only at h
  cases ok0
  · exact Bool.noConfusion h
  · dsimp only at h
    generalize hp1 : (Bool.rec (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1)
      (true, c1) (Nat.blt fuel n) : Bool × List (Nat × Nat)) = p1 at h
    obtain ⟨ok1, c2⟩ := p1
    dsimp only at h
    cases ok1
    · exact Bool.noConfusion h
    · dsimp only at h
      generalize hp2 : (Bool.rec (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2)
        (true, c2) (Nat.blt fuel n) : Bool × List (Nat × Nat)) = p2 at h
      obtain ⟨ok2, c3⟩ := p2
      dsimp only at h
      cases ok2
      · exact Bool.noConfusion h
      · dsimp only at h
        cases keepA <;> cases keepB
        · cases hw : Nat.blt fuel (n - 1)
          · have hw' : Nat.blt fuel (Nat.sub n 1) = false := hw
            rw [hw'] at hp0; exact Or.inr ⟨cur, congrArg Prod.fst hp0⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp2; exact Or.inr ⟨c2, congrArg Prod.fst hp2⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp1; exact Or.inr ⟨c1, congrArg Prod.fst hp1⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel (n + 1)
          · have hw' : Nat.blt fuel (Nat.add n 1) = false := hw
            rw [hw'] at h; exact Or.inr ⟨c3, h⟩
          · exact Or.inl rfl

def checkOpV4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x y rawZ op : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  forceWC (canonF mask rawZ) (fun z =>
    Bool.rec
      (Bool.rec
        (forceWC (sepPack z) (fun spZ =>
          checkKeepsV4 mask goal ep count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
            ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) cur))
        (true, cur) (memN z ws0))
      (true, cur) (Nat.beq z 0))

def check4OpsV4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x nx y : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  let (o0, c1) := checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur
  Bool.rec (false, c1)
    (let (o1, c2) := checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1
     Bool.rec (false, c2)
       (let (o2, c3) := checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2
        Bool.rec (false, c3)
          (checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.land nx y) 3 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c3) o2) o1) o0

theorem check4OpsV4_at {mask goal ep count fuel fuel1 n x y spAll spNoA spNoB spNoAB tokAB op : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)}
    (hop : op < 4)
    (h : (check4OpsV4 mask goal ep count bounds states fuel fuel1 n x (Nat.xor mask x) y
      spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur).1 = true) :
    let z := binOp mask op x y
    z = 0 ∨ ws0.contains z = true ∨
      ∃ c, (checkKeepsV4 mask goal ep count bounds states fuel fuel1 n z (sepPack z) spAll spNoA spNoB spNoAB
        ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) c).1 = true := by
  unfold check4OpsV4 at h
  generalize hp0 : checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur = p0 at h
  obtain ⟨o0, c1⟩ := p0; dsimp only at h
  cases o0
  · exact Bool.noConfusion h
  · dsimp only at h
    generalize hp1 : checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1 = p1 at h
    obtain ⟨o1, c2⟩ := p1; dsimp only at h
    cases o1
    · exact Bool.noConfusion h
    · dsimp only at h
      generalize hp2 : checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2 = p2 at h
      obtain ⟨o2, c3⟩ := p2; dsimp only at h
      cases o2
      · exact Bool.noConfusion h
      · dsimp only at h
        have extract (rawZ op' : Nat) (c0 : List (Nat × Nat))
            (hz : canon mask rawZ = binOp mask op' x y)
            (hok : (checkOpV4 mask goal ep count bounds states fuel fuel1 n x y rawZ op' spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c0).1 = true) :
            binOp mask op' x y = 0 ∨ ws0.contains (binOp mask op' x y) = true ∨
              ∃ c, (checkKeepsV4 mask goal ep count bounds states fuel fuel1 n (binOp mask op' x y) (sepPack (binOp mask op' x y))
                spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB ((binOp mask op' x y, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op') 2) c).1 = true := by
          unfold checkOpV4 at hok
          rw [forceWC_eq, canonF_eq, hz] at hok
          cases h0 : Nat.beq (binOp mask op' x y) 0
          · rw [h0] at hok; dsimp only at hok
            cases hm : memN (binOp mask op' x y) ws0
            · rw [hm] at hok; dsimp only at hok
              rw [forceWC_eq] at hok
              exact Or.inr (Or.inr ⟨c0, hok⟩)
            · rw [memN_eq] at hm; exact Or.inr (Or.inl hm)
          · exact Or.inl (Nat.beq_eq.mp h0)
        rcases (by omega : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3) with rfl | rfl | rfl | rfl
        · exact extract _ 0 cur rfl (congrArg Prod.fst hp0)
        · exact extract _ 1 c1 rfl (congrArg Prod.fst hp1)
        · exact extract _ 2 c2 rfl (congrArg Prod.fst hp2)
        · exact extract _ 3 c3 rfl h

def loopB_V4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n a x nx spAll spNoA : Nat) (ws0 wsNoA : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Bool × List (Nat × Nat)
  | 0, _, c => (true, c)
  | rem + 1, b, cur =>
    let y := getDN ws0 b
    let wsNoB := dropValF true y ws0
    let wsNoAB := dropValF true y wsNoA
    forceWC (orSepSkip y ps) (fun spNoB =>
      forceWC (orSepSkip2 x y ps) (fun spNoAB =>
        let tokAB := Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2
        let (ok, cur1) := check4OpsV4 mask goal ep count bounds states fuel fuel1 n x nx y spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur
        Bool.rec (false, cur1) (loopB_V4 mask goal ep count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem (Nat.add b 1) cur1) ok))

theorem loopB_V4_at {mask goal ep count fuel fuel1 n a x nx spAll spNoA : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem b0 b : Nat} {cur : List (Nat × Nat)}
    (hb1 : b0 ≤ b) (hb2 : b < b0 + rem)
    (h : (loopB_V4 mask goal ep count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem b0 cur).1 = true) :
    let y := getDN ws0 b
    ∃ c, (check4OpsV4 mask goal ep count bounds states fuel fuel1 n x nx y spAll spNoA
      (orSepSkip y ps) (orSepSkip2 x y ps) ws0 wsNoA (dropValF true y ws0) (dropValF true y wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) c).1 = true := by
  induction rem generalizing b0 cur with
  | zero => omega
  | succ r ih =>
    unfold loopB_V4 at h; dsimp only at h
    rw [forceWC_eq, forceWC_eq] at h
    cases hp : check4OpsV4 mask goal ep count bounds states fuel fuel1 n x nx (getDN ws0 b0) spAll spNoA
      (orSepSkip (getDN ws0 b0) ps) (orSepSkip2 x (getDN ws0 b0) ps) ws0 wsNoA
      (dropValF true (getDN ws0 b0) ws0) (dropValF true (getDN ws0 b0) wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b0) 2) cur with
    | mk ok cur1 =>
      rw [hp] at h; dsimp only at h
      cases ok
      · exact Bool.noConfusion h
      · dsimp only at h
        by_cases heq : b = b0
        · subst heq; exact ⟨cur, by rw [hp]⟩
        · exact ih (by change b0 + 1 ≤ b; omega) (by change b < (b0 + 1) + r; omega) h

def loopA_V4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n spAll : Nat) (ws0 : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Bool × List (Nat × Nat)
  | 0, _, c => (true, c)
  | rem + 1, a, cur =>
    let x := getDN ws0 a
    let wsNoA := dropValF true x ws0
    forceWC (Nat.xor mask x) (fun nx =>
      forceWC (orSepSkip x ps) (fun spNoA =>
        let (ok, cur1) := loopB_V4 mask goal ep count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) cur
        Bool.rec (false, cur1) (loopA_V4 mask goal ep count bounds states fuel fuel1 n spAll ws0 ps hist rem (Nat.add a 1) cur1) ok))

theorem loopA_V4_at {mask goal ep count fuel fuel1 n spAll : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem a0 a : Nat} {cur : List (Nat × Nat)}
    (ha1 : a0 ≤ a) (ha2 : a < a0 + rem)
    (h : (loopA_V4 mask goal ep count bounds states fuel fuel1 n spAll ws0 ps hist rem a0 cur).1 = true) :
    let x := getDN ws0 a
    ∃ c, (loopB_V4 mask goal ep count bounds states fuel fuel1 n a x (Nat.xor mask x) spAll
      (orSepSkip x ps) ws0 (dropValF true x ws0) ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) c).1 = true := by
  induction rem generalizing a0 cur with
  | zero => omega
  | succ r ih =>
    unfold loopA_V4 at h; dsimp only at h
    rw [forceWC_eq, forceWC_eq] at h
    cases hp : loopB_V4 mask goal ep count bounds states fuel fuel1 n a0 (getDN ws0 a0) (Nat.xor mask (getDN ws0 a0)) spAll
      (orSepSkip (getDN ws0 a0) ps) ws0 (dropValF true (getDN ws0 a0) ws0) ps hist (Nat.sub n (Nat.add a0 1)) (Nat.add a0 1) cur with
    | mk ok cur1 =>
      rw [hp] at h; dsimp only at h
      cases ok
      · exact Bool.noConfusion h
      · dsimp only at h
        by_cases heq : a = a0
        · subst heq; exact ⟨cur, by rw [hp]⟩
        · exact ih (by change a0 + 1 ≤ a; omega) (by change a < (a0 + 1) + r; omega) h

def dagCheckNodeV4 (mask goal ep : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (cursors : Nat → List (Nat × Nat)) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, hist) =>
    forceWs ws (fun ws0 =>
      let n := lenN ws0
      Bool.rec
        (Bool.rec
          (Bool.rec false
            (forceSepPairs ws0 (fun ps =>
              forceW (orSepAll ps) (fun spAll =>
                (loopA_V4 mask goal ep count bounds states fuel (Nat.sub fuel 1) n spAll ws0 ps hist n 0 (cursors (Nat.add i 1))).1)))
            (Nat.blt n 17))
          true (Nat.beq fuel 0))
        false (memN goal ws0))

def stepRootV4 (mask goal ep count fuel : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (ws : List Nat) (tok : Nat) (cur : List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  Bool.rec
    (match cur with
     | (t, code) :: tl =>
       Bool.rec
         (closeFallbackV4 mask goal ep bounds (fuel, ws, []) (orSep ws), cur)
         (Bool.rec
           (match nthBound bounds (Nat.shiftRight code 1) with
            | none => (false, tl)
            | some b => (boundClosesF (fuel, ws, []) b, tl))
           (let dest := Nat.shiftRight code 1
            let ok := Bool.rec false
              (match states dest with
               | none => false
               | some saved => Bool.rec false (eqListN saved.2.1 ws) (Nat.beq saved.1 fuel))
              (Nat.blt dest count)
            (ok, tl))
           (Nat.beq (Nat.land code 1) 0))
         (Nat.beq tok t)
     | [] =>
       (closeFallbackV4 mask goal ep bounds (fuel, ws, []) (orSep ws), []))
    (true, cur) (Nat.blt (Nat.add fuel 1) (lenN ws))

def loopRootsV4 (mask goal ep count fuel : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (stock : List Nat) : Nat → Nat → List (Nat × Nat) → Bool × List (Nat × Nat)
  | 0, _, c => (true, c)
  | rem + 1, tok, cur =>
    let ws := subsetWordsF stock tok
    let (ok, cur1) := stepRootV4 mask goal ep count fuel bounds states ws tok cur
    Bool.rec (false, cur1) (loopRootsV4 mask goal ep count fuel bounds states stock rem (Nat.add tok 1) cur1) ok

def dagCheckRootsV4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (rootCur : List (Nat × Nat)) (stock : List Nat) (fuel : Nat) : Bool :=
  (loopRootsV4 mask goal ep count fuel bounds states stock (Nat.shiftLeft 1 (lenN stock)) 0 rootCur).1

theorem loopRootsV4_at {mask goal ep count fuel : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {stock : List Nat} {rem t0 tok : Nat} {cur : List (Nat × Nat)}
    (ht1 : t0 ≤ tok) (ht2 : tok < t0 + rem)
    (h : (loopRootsV4 mask goal ep count fuel bounds states stock rem t0 cur).1 = true) :
    ∃ c, (stepRootV4 mask goal ep count fuel bounds states (subsetWordsF stock tok) tok c).1 = true := by
  induction rem generalizing t0 cur with
  | zero => omega
  | succ r ih =>
    unfold loopRootsV4 at h; dsimp only at h
    cases hp : stepRootV4 mask goal ep count fuel bounds states (subsetWordsF stock t0) t0 cur with
    | mk ok cur1 =>
      rw [hp] at h; dsimp only at h
      cases ok
      · exact Bool.noConfusion h
      · dsimp only at h
        by_cases heq : tok = t0
        · subst heq; exact ⟨cur, by rw [hp]⟩
        · exact ih (by change t0 + 1 ≤ tok; omega) (by change tok < (t0 + 1) + r; omega) h

theorem dagAllNodesV4 {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (snd : stock.Nodup)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV4 mask goal (edgePack mask goal) bounds count
      (dagTrace mask stock fuel forest) cursors i = true) :
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
    unfold dagCheckNodeV4 at hchk
    rw [htr] at hchk; dsimp only at hchk
    rw [forceWs_eq, lenN_eq, memN_eq] at hchk
    generalize hS : ws.toFinset = S at hlive
    cases hlive with
    | done =>
      have hgm' : goal ∈ ws := List.mem_toFinset.mp (hS.symm ▸ Finset.mem_singleton_self goal)
      have hc : ws.contains goal = true := List.contains_iff_mem.mpr hgm'
      rw [hc] at hchk; exact Bool.noConfusion hchk
    | @step k' _ a0 b0 op0 ha0 hb0 hab0 _ _ hop0 hz0 hf0 keepA0 keepB0 tail0 =>
      rw [← hS] at ha0 hb0 hf0 tail0
      have hrem_pos : rem ≠ 0 := by omega
      cases hcg : ws.contains goal
      · rw [hcg] at hchk; dsimp only at hchk
        have hrem0 : Nat.beq rem 0 = false := beq_false_ne hrem_pos
        rw [hrem0] at hchk; dsimp only at hchk
        cases h17 : Nat.blt ws.length 17
        · rw [h17] at hchk; exact Bool.noConfusion hchk
        · rw [h17] at hchk; dsimp only at hchk
          rw [forceSepPairs_eq, forceW_eq] at hchk
          have haM : a0 ∈ ws := List.mem_toFinset.mp ha0
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
          obtain ⟨cA, hB⟩ := loopA_V4_at (a := a) (Nat.zero_le a) (by omega) hchk
          obtain ⟨cB, hO⟩ := loopB_V4_at (b := b) (by change a + 1 ≤ b; omega) (by change b < (a + 1) + (ws.length - (a + 1)); omega) hB
          simp only [getDN_eq, dropValF_eq, orSepAll_mapSep, orSepSkip_mapSep, orSepSkip2_mapSep] at hO
          set x := ws.getD a 0
          set y := ws.getD b 0
          set z := binOp mask op x y
          have hznz : z ≠ 0 := hzeq.symm ▸ hz0
          have hznm : ws.contains z = false := by
            cases h : ws.contains z
            · rfl
            · exact absurd (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)) (hzeq.symm ▸ hf0)
          rcases check4OpsV4_at hop_lt hO with hz' | hcm | ⟨cK, hK⟩
          · exact hznz hz'
          · rw [hznm] at hcm; exact Bool.noConfusion hcm
          · have hxM : x ∈ ws := by simp only [x, hax]; split; exact haM; exact hbM
            have hyM : y ∈ ws := by simp only [y, hby]; split; exact hbM; exact haM
            have hxy : x ≠ y := by simp only [x, y, hax, hby]; split; exact hab0; exact hab0.symm
            have hzNotW : z ∉ ws := fun hm => by
              have := List.contains_iff_mem.mpr hm; rw [hznm] at this; exact Bool.noConfusion this
            have hdropComm : dropVal true y (dropVal true x ws) = dropVal true x (dropVal true y ws) :=
              dropVal_comm x y ws
            set rest := dropVal (!keepA) x (dropVal (!keepB) y ws)
            have hnd_u : (z :: rest).Nodup :=
              List.nodup_cons.mpr ⟨fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1,
                dropVal_nodup (dropVal_nodup nd)⟩
            have hset_u : (z :: rest).toFinset = insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
              ext w; simp only [rest, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, ← dropVal_toFinset]
            have hlive_u : LiveBin mask goal k' (z :: rest).toFinset := by rwa [hset_u]
            have hset_s : (insertSorted z rest).toFinset = (z :: rest).toFinset := by
              ext w; simp only [List.mem_toFinset, insertSorted_mem, List.mem_cons]
            have hlive_s : LiveBin mask goal k' (insertSorted z rest).toFinset := by rwa [hset_s]
            have hlen' : (insertSorted z rest).length =
                ws.length - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0) :=
              list_len_child (z := z) (keepA := keepA) (keepB := keepB) nd hxM hyM hxy hzNotW
            have hcard' : (insertSorted z rest).length ≤ rem := by
              have hnd_s : (insertSorted z rest).Nodup :=
                insertSorted_nodup (fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
              have := liveBin_card_le hlive_s
              rw [List.toFinset_card_of_nodup hnd_s] at this; omega
            have h2len : 2 ≤ ws.length := by
              have hsub2 : ({x, y} : Finset Nat) ⊆ ws.toFinset := by
                intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
                · exact List.mem_toFinset.mpr hxM
                · rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hyM
              have hpair : ({x, y} : Finset Nat).card = 2 := Finset.card_pair hxy
              have hc := Finset.card_le_card hsub2
              rw [List.toFinset_card_of_nodup nd] at hc; omega
            have hka := checkKeepsV4_at hK keepA keepB
            have finish {tok' : Nat} {c' : List (Nat × Nat)}
                (hstep : (stepLeafV4 mask goal (edgePack mask goal) count bounds (dagTrace mask stock fuel forest)
                  (Nat.sub rem 1) z (sepPack z) (orSep rest) rest ((z, x, y) :: hist) tok' c').1 = true) : False := by
              obtain ⟨dest, hdest, saved, htr2, hfEq, hwEq⟩ :=
                stepLeafV4_ref hgm hknown hsub hgoals hnd_u (k := k') (by change k' ≤ rem - 1; omega) hlive_u hstep
              exact ih (rem - 1) (by omega) dest saved hdest htr2 hfEq k' (by omega) (hwEq ▸ hlive_s)
            cases keepA <;> cases keepB
            · rcases hka with hwide | ⟨c', hst⟩
              · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false] at hlen'; omega
              · rw [hdropComm] at hst
                exact finish hst
            · rcases hka with hwide | ⟨c', hst⟩
              · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
              · exact finish hst
            · rcases hka with hwide | ⟨c', hst⟩
              · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
              · exact finish hst
            · rcases hka with hwide | ⟨c', hst⟩
              · have := Nat.blt_eq.mp hwide; simp only [ite_true] at hlen'; omega
              · exact finish hst
      · rw [hcg] at hchk; exact Bool.noConfusion hchk

theorem lowerDagV4 {mask goal ep fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hep : ep = edgePack mask goal)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hroots : dagCheckRootsV4 mask goal ep count bounds
      (dagTraceF mask stock fuel forest) (cursors 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV4 mask goal ep bounds count
      (dagTraceF mask stock fuel forest) cursors i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  subst hep
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr] at hroots hnodes
  intro vs hbuild hhit
  by_contra! hlt
  have hcs' : ∀ w ∈ stock, canon mask w = w := fun w hw =>
    Nat.beq_eq.mp (List.all_eq_true.mp hcs w hw)
  obtain ⟨k, S, hk, hSsub, hlive⟩ := extractLiveBin hgnz hcs' hbuild hhit
  obtain ⟨tok, htok, hteq⟩ := exists_subsetToken stock S
  rw [Finset.inter_eq_left.mpr hSsub] at hteq
  unfold dagCheckRootsV4 at hroots
  have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
    rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [hpow] at hroots
  obtain ⟨c, hsr⟩ := loopRootsV4_at (tok := tok) (Nat.zero_le tok) (by omega) hroots
  rw [subsetWordsF_eq] at hsr
  have hnd : (subsetWords stock tok).Nodup := subsetWords_nodup snd tok
  have hlive' : LiveBin mask goal k (subsetWords stock tok).toFinset := by rwa [hteq]
  have hcard : (subsetWords stock tok).length ≤ fuel + 1 := by
    have := liveBin_card_le hlive'
    rw [List.toFinset_card_of_nodup hnd] at this; omega
  have hnw : Nat.blt (Nat.add fuel 1) (lenN (subsetWords stock tok)) = false := by
    rw [lenN_eq]
    cases h : Nat.blt (Nat.add fuel 1) (subsetWords stock tok).length
    · rfl
    · have hlt' : fuel + 1 < (subsetWords stock tok).length := Nat.blt_eq.mp h
      omega
  have hfb := closeFallbackV4_open (st := (fuel, subsetWords stock tok, [])) hgm hknown hsub hgoals hnd (k := k) (by omega) hlive'
  unfold stepRootV4 at hsr
  rw [hnw] at hsr; dsimp only at hsr
  cases c with
  | nil => dsimp only at hsr; rw [hfb] at hsr; exact Bool.noConfusion hsr
  | cons hd tl =>
    obtain ⟨t, code⟩ := hd
    dsimp only at hsr
    cases ht : Nat.beq tok t
    · rw [ht] at hsr; dsimp only at hsr; rw [hfb] at hsr; exact Bool.noConfusion hsr
    · rw [ht] at hsr; dsimp only at hsr
      cases hev : Nat.beq (Nat.land code 1) 0
      · rw [hev] at hsr; dsimp only at hsr
        cases hb : nthBound bounds (Nat.shiftRight code 1) with
        | none => rw [hb] at hsr; exact Bool.noConfusion hsr
        | some b =>
          rw [hb] at hsr; dsimp only at hsr
          have hmem := nthBound_mem hb
          have hg := hgoals b hmem
          rw [boundClosesF_eq hg.1 hg.2] at hsr
          have h0 := boundCloses_sound (state := (fuel, subsetWords stock tok, [])) (hknown b hmem) (hsub b hmem) hnd (k := k) (by omega) hlive'
          rw [h0] at hsr; exact Bool.noConfusion hsr
      · rw [hev] at hsr; dsimp only at hsr
        cases hltc : Nat.blt (Nat.shiftRight code 1) count
        · rw [hltc] at hsr; exact Bool.noConfusion hsr
        · rw [hltc] at hsr; dsimp only at hsr
          cases htr2 : dagTrace mask stock fuel forest (Nat.shiftRight code 1) with
          | none => rw [htr2] at hsr; exact Bool.noConfusion hsr
          | some saved =>
            rw [htr2] at hsr; dsimp only at hsr
            cases hf : Nat.beq saved.1 fuel
            · rw [hf] at hsr; exact Bool.noConfusion hsr
            · rw [hf] at hsr; dsimp only at hsr
              rw [eqListN_eq, beq_iff_eq] at hsr
              exact dagAllNodesV4 hgm hknown hsub hgoals snd hnodes fuel (Nat.shiftRight code 1) saved
                (Nat.blt_eq.mp hltc) htr2 (Nat.beq_eq.mp hf) k (by omega) (hsr ▸ hlive')

def unpackF (data width idx : Nat) : Nat :=
  Nat.land (Nat.shiftRight data (Nat.mul idx width)) (Nat.sub (Nat.shiftLeft 1 width) 1)

def unpackForestF (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := Nat.add pBits tBits
  let code := unpackF data w i
  (Nat.shiftRight code tBits, Nat.land code (Nat.sub (Nat.shiftLeft 1 tBits) 1))

def unpackListAux (data off w wMask tokBits tokMask : Nat) : Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, acc => acc
  | k + 1, acc =>
    let code := Nat.land (Nat.shiftRight data (Nat.mul (Nat.add off k) w)) wMask
    unpackListAux data off w wMask tokBits tokMask k ((Nat.land code tokMask, Nat.shiftRight code tokBits) :: acc)

def unpackCursorV4 (index data idxW idxMask sizeBits sizeMask tokBits tokMask w wMask : Nat) :
    Nat → List (Nat × Nat) :=
  fun parent =>
    let entry := Nat.land (Nat.shiftRight index (Nat.mul parent idxW)) idxMask
    let sz := Nat.land entry sizeMask
    let off := Nat.shiftRight entry sizeBits
    unpackListAux data off w wMask tokBits tokMask sz []

def m_0 : Nat := 0xcccc0000
def s_0 : List Nat := [0x44440000, 0xc0c0000, 0xcc0000]
def g_0 : Nat := 0x44c0000
def ep_0 : Nat := 0x480000000000000408000000000000000000000000000004400000
theorem epk_0 : ep_0 = edgePack m_0 g_0 := by decide +kernel
def bds_0 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_0 : KnownBin bds_0 := by intro b hb; simp [bds_0] at hb
theorem sub_0 : ∀ b ∈ bds_0, m_0 &&& b.1 = b.1 := by intro b hb; simp [bds_0] at hb
theorem gl_0 : ∀ b ∈ bds_0, canon b.1 g_0 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_0] at hb
def cur_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_0 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_0 : dagCheckRootsV4 m_0 g_0 ep_0 1 bds_0 (dagTraceF m_0 s_0 3 f_0) (cur_0 0) s_0 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_0 : treeBlockF 0 1 (dagCheckNodeV4 m_0 g_0 ep_0 bds_0 1 (dagTraceF m_0 s_0 3 f_0) cur_0) = true := by decide +kernel
theorem nc_0 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_0 g_0 ep_0 bds_0 1 (dagTraceF m_0 s_0 3 f_0) cur_0) i = true := fun _ h1 h2 => treeBlockF_at nb_0 h1 h2
theorem lb_0 : LowerBin m_0 s_0 g_0 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_0 kn_0 sub_0 gl_0 rc_0 nc_0

def m_1 : Nat := 0xf000f000000000
def s_1 : List Nat := [0x50005000000000, 0x30003000000000, 0xf000000000]
def g_1 : Nat := 0x10007000000000
def ep_1 : Nat := 0x60000000000000000000000000000000000000000000100020000000000010004000000000
theorem epk_1 : ep_1 = edgePack m_1 g_1 := by decide +kernel
def bds_1 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_1 : KnownBin bds_1 := by intro b hb; simp [bds_1] at hb
theorem sub_1 : ∀ b ∈ bds_1, m_1 &&& b.1 = b.1 := by intro b hb; simp [bds_1] at hb
theorem gl_1 : ∀ b ∈ bds_1, canon b.1 g_1 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_1] at hb
def cur_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_1 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_1 : dagCheckRootsV4 m_1 g_1 ep_1 1 bds_1 (dagTraceF m_1 s_1 3 f_1) (cur_1 0) s_1 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_1 : treeBlockF 0 1 (dagCheckNodeV4 m_1 g_1 ep_1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) cur_1) = true := by decide +kernel
theorem nc_1 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_1 g_1 ep_1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) cur_1) i = true := fun _ h1 h2 => treeBlockF_at nb_1 h1 h2
theorem lb_1 : LowerBin m_1 s_1 g_1 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_1 kn_1 sub_1 gl_1 rc_1 nc_1

def m_2 : Nat := 0xc000c000c000c0
def s_2 : List Nat := [0x40004000400040, 0xc0000000c0, 0xc000c0]
def g_2 : Nat := 0x40004000c0
def ep_2 : Nat := 0x40008000000040000000800000000000000000000000000000000000000000000000000000004000400000
theorem epk_2 : ep_2 = edgePack m_2 g_2 := by decide +kernel
def bds_2 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_2 : KnownBin bds_2 := by intro b hb; simp [bds_2] at hb
theorem sub_2 : ∀ b ∈ bds_2, m_2 &&& b.1 = b.1 := by intro b hb; simp [bds_2] at hb
theorem gl_2 : ∀ b ∈ bds_2, canon b.1 g_2 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_2] at hb
def cur_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_2 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_2 : dagCheckRootsV4 m_2 g_2 ep_2 1 bds_2 (dagTraceF m_2 s_2 3 f_2) (cur_2 0) s_2 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_2 : treeBlockF 0 1 (dagCheckNodeV4 m_2 g_2 ep_2 bds_2 1 (dagTraceF m_2 s_2 3 f_2) cur_2) = true := by decide +kernel
theorem nc_2 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_2 g_2 ep_2 bds_2 1 (dagTraceF m_2 s_2 3 f_2) cur_2) i = true := fun _ h1 h2 => treeBlockF_at nb_2 h1 h2
theorem lb_2 : LowerBin m_2 s_2 g_2 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_2 kn_2 sub_2 gl_2 rc_2 nc_2

def m_3 : Nat := 0x2200220022002200
def s_3 : List Nat := [0x200020002000200, 0x220000002200, 0x22002200]
def g_3 : Nat := 0x20002002200
def ep_3 : Nat := 0x200200000000200000020000000000000000000000002000200000000000000000000000000000000000000
theorem epk_3 : ep_3 = edgePack m_3 g_3 := by decide +kernel
def bds_3 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_3 : KnownBin bds_3 := by intro b hb; simp [bds_3] at hb
theorem sub_3 : ∀ b ∈ bds_3, m_3 &&& b.1 = b.1 := by intro b hb; simp [bds_3] at hb
theorem gl_3 : ∀ b ∈ bds_3, canon b.1 g_3 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_3] at hb
def cur_3 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_3 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_3 : dagCheckRootsV4 m_3 g_3 ep_3 1 bds_3 (dagTraceF m_3 s_3 3 f_3) (cur_3 0) s_3 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_3 : treeBlockF 0 1 (dagCheckNodeV4 m_3 g_3 ep_3 bds_3 1 (dagTraceF m_3 s_3 3 f_3) cur_3) = true := by decide +kernel
theorem nc_3 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_3 g_3 ep_3 bds_3 1 (dagTraceF m_3 s_3 3 f_3) cur_3) i = true := fun _ h1 h2 => treeBlockF_at nb_3 h1 h2
theorem lb_3 : LowerBin m_3 s_3 g_3 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_3 kn_3 sub_3 gl_3 rc_3 nc_3

def m_4 : Nat := 0x4400440044004400
def s_4 : List Nat := [0x400040004000400, 0x440000004400, 0x44004400]
def g_4 : Nat := 0x40004004400
def ep_4 : Nat := 0x400400000000400000040000000000000000000000004000400000000000000000000000000000000000000
theorem epk_4 : ep_4 = edgePack m_4 g_4 := by decide +kernel
def bds_4 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_4 : KnownBin bds_4 := by intro b hb; simp [bds_4] at hb
theorem sub_4 : ∀ b ∈ bds_4, m_4 &&& b.1 = b.1 := by intro b hb; simp [bds_4] at hb
theorem gl_4 : ∀ b ∈ bds_4, canon b.1 g_4 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_4] at hb
def cur_4 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_4 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_4 : dagCheckRootsV4 m_4 g_4 ep_4 1 bds_4 (dagTraceF m_4 s_4 3 f_4) (cur_4 0) s_4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_4 : treeBlockF 0 1 (dagCheckNodeV4 m_4 g_4 ep_4 bds_4 1 (dagTraceF m_4 s_4 3 f_4) cur_4) = true := by decide +kernel
theorem nc_4 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_4 g_4 ep_4 bds_4 1 (dagTraceF m_4 s_4 3 f_4) cur_4) i = true := fun _ h1 h2 => treeBlockF_at nb_4 h1 h2
theorem lb_4 : LowerBin m_4 s_4 g_4 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_4 kn_4 sub_4 gl_4 rc_4 nc_4

def m_5 : Nat := 0xf000f0000000000
def s_5 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_5 : Nat := 0x100070000000000
def ep_5 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
theorem epk_5 : ep_5 = edgePack m_5 g_5 := by decide +kernel
def bds_5 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_5 : KnownBin bds_5 := by intro b hb; simp [bds_5] at hb
theorem sub_5 : ∀ b ∈ bds_5, m_5 &&& b.1 = b.1 := by intro b hb; simp [bds_5] at hb
theorem gl_5 : ∀ b ∈ bds_5, canon b.1 g_5 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_5] at hb
def cur_5 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_5 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_5 : dagCheckRootsV4 m_5 g_5 ep_5 1 bds_5 (dagTraceF m_5 s_5 3 f_5) (cur_5 0) s_5 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_5 : treeBlockF 0 1 (dagCheckNodeV4 m_5 g_5 ep_5 bds_5 1 (dagTraceF m_5 s_5 3 f_5) cur_5) = true := by decide +kernel
theorem nc_5 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_5 g_5 ep_5 bds_5 1 (dagTraceF m_5 s_5 3 f_5) cur_5) i = true := fun _ h1 h2 => treeBlockF_at nb_5 h1 h2
theorem lb_5 : LowerBin m_5 s_5 g_5 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_5 kn_5 sub_5 gl_5 rc_5 nc_5

def m_6 : Nat := 0xc000c000c000c00
def s_6 : List Nat := [0x400040004000400, 0xc0000000c00, 0xc000c00]
def g_6 : Nat := 0x40004000c00
def ep_6 : Nat := 0x400080000000400000008000000000000000000000000000000000000000000000000000000040004000000
theorem epk_6 : ep_6 = edgePack m_6 g_6 := by decide +kernel
def bds_6 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_6 : KnownBin bds_6 := by intro b hb; simp [bds_6] at hb
theorem sub_6 : ∀ b ∈ bds_6, m_6 &&& b.1 = b.1 := by intro b hb; simp [bds_6] at hb
theorem gl_6 : ∀ b ∈ bds_6, canon b.1 g_6 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_6] at hb
def cur_6 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_6 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_6 : dagCheckRootsV4 m_6 g_6 ep_6 1 bds_6 (dagTraceF m_6 s_6 3 f_6) (cur_6 0) s_6 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_6 : treeBlockF 0 1 (dagCheckNodeV4 m_6 g_6 ep_6 bds_6 1 (dagTraceF m_6 s_6 3 f_6) cur_6) = true := by decide +kernel
theorem nc_6 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_6 g_6 ep_6 bds_6 1 (dagTraceF m_6 s_6 3 f_6) cur_6) i = true := fun _ h1 h2 => treeBlockF_at nb_6 h1 h2
theorem lb_6 : LowerBin m_6 s_6 g_6 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_6 kn_6 sub_6 gl_6 rc_6 nc_6

def m_7 : Nat := 0x4040404040404040
def s_7 : List Nat := [0x40004000400040, 0x404000004040, 0x40404040]
def g_7 : Nat := 0x4000404040
def ep_7 : Nat := 0x40400000000040000040000000004000400000000000000000000000000000000000000000000000000000
theorem epk_7 : ep_7 = edgePack m_7 g_7 := by decide +kernel
def bds_7 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_7 : KnownBin bds_7 := by intro b hb; simp [bds_7] at hb
theorem sub_7 : ∀ b ∈ bds_7, m_7 &&& b.1 = b.1 := by intro b hb; simp [bds_7] at hb
theorem gl_7 : ∀ b ∈ bds_7, canon b.1 g_7 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_7] at hb
def cur_7 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_7 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_7 : dagCheckRootsV4 m_7 g_7 ep_7 1 bds_7 (dagTraceF m_7 s_7 3 f_7) (cur_7 0) s_7 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_7 : treeBlockF 0 1 (dagCheckNodeV4 m_7 g_7 ep_7 bds_7 1 (dagTraceF m_7 s_7 3 f_7) cur_7) = true := by decide +kernel
theorem nc_7 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_7 g_7 ep_7 bds_7 1 (dagTraceF m_7 s_7 3 f_7) cur_7) i = true := fun _ h1 h2 => treeBlockF_at nb_7 h1 h2
theorem lb_7 : LowerBin m_7 s_7 g_7 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_7 kn_7 sub_7 gl_7 rc_7 nc_7

def m_8 : Nat := 0x4444444400000000
def s_8 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_8 : Nat := 0x4044400000000
def ep_8 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
theorem epk_8 : ep_8 = edgePack m_8 g_8 := by decide +kernel
def bds_8 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_8 : KnownBin bds_8 := by intro b hb; simp [bds_8] at hb
theorem sub_8 : ∀ b ∈ bds_8, m_8 &&& b.1 = b.1 := by intro b hb; simp [bds_8] at hb
theorem gl_8 : ∀ b ∈ bds_8, canon b.1 g_8 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_8] at hb
def cur_8 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_8 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_8 : dagCheckRootsV4 m_8 g_8 ep_8 1 bds_8 (dagTraceF m_8 s_8 3 f_8) (cur_8 0) s_8 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_8 : treeBlockF 0 1 (dagCheckNodeV4 m_8 g_8 ep_8 bds_8 1 (dagTraceF m_8 s_8 3 f_8) cur_8) = true := by decide +kernel
theorem nc_8 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_8 g_8 ep_8 bds_8 1 (dagTraceF m_8 s_8 3 f_8) cur_8) i = true := fun _ h1 h2 => treeBlockF_at nb_8 h1 h2
theorem lb_8 : LowerBin m_8 s_8 g_8 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_8 kn_8 sub_8 gl_8 rc_8 nc_8

def m_9 : Nat := 0x2222222200000000
def s_9 : List Nat := [0x202020200000000, 0x22002200000000, 0x222200000000]
def g_9 : Nat := 0x2022200000000
def ep_9 : Nat := 0x220000000000002002000000000000202000000000000000000000000000000000000000000
theorem epk_9 : ep_9 = edgePack m_9 g_9 := by decide +kernel
def bds_9 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_9 : KnownBin bds_9 := by intro b hb; simp [bds_9] at hb
theorem sub_9 : ∀ b ∈ bds_9, m_9 &&& b.1 = b.1 := by intro b hb; simp [bds_9] at hb
theorem gl_9 : ∀ b ∈ bds_9, canon b.1 g_9 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_9] at hb
def cur_9 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_9 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_9 : dagCheckRootsV4 m_9 g_9 ep_9 1 bds_9 (dagTraceF m_9 s_9 3 f_9) (cur_9 0) s_9 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_9 : treeBlockF 0 1 (dagCheckNodeV4 m_9 g_9 ep_9 bds_9 1 (dagTraceF m_9 s_9 3 f_9) cur_9) = true := by decide +kernel
theorem nc_9 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_9 g_9 ep_9 bds_9 1 (dagTraceF m_9 s_9 3 f_9) cur_9) i = true := fun _ h1 h2 => treeBlockF_at nb_9 h1 h2
theorem lb_9 : LowerBin m_9 s_9 g_9 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_9 kn_9 sub_9 gl_9 rc_9 nc_9

def m_10 : Nat := 0xaaaa00000000
def s_10 : List Nat := [0x222200000000, 0xa0a00000000, 0xaa00000000]
def g_10 : Nat := 0x22a00000000
def ep_10 : Nat := 0x2800000000000002080000000000000220000000000000000000000000
theorem epk_10 : ep_10 = edgePack m_10 g_10 := by decide +kernel
def bds_10 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_10 : KnownBin bds_10 := by intro b hb; simp [bds_10] at hb
theorem sub_10 : ∀ b ∈ bds_10, m_10 &&& b.1 = b.1 := by intro b hb; simp [bds_10] at hb
theorem gl_10 : ∀ b ∈ bds_10, canon b.1 g_10 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_10] at hb
def cur_10 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_10 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_10 : dagCheckRootsV4 m_10 g_10 ep_10 1 bds_10 (dagTraceF m_10 s_10 3 f_10) (cur_10 0) s_10 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_10 : treeBlockF 0 1 (dagCheckNodeV4 m_10 g_10 ep_10 bds_10 1 (dagTraceF m_10 s_10 3 f_10) cur_10) = true := by decide +kernel
theorem nc_10 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_10 g_10 ep_10 bds_10 1 (dagTraceF m_10 s_10 3 f_10) cur_10) i = true := fun _ h1 h2 => treeBlockF_at nb_10 h1 h2
theorem lb_10 : LowerBin m_10 s_10 g_10 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_10 kn_10 sub_10 gl_10 rc_10 nc_10

def m_11 : Nat := 0xcccc00000000
def s_11 : List Nat := [0x444400000000, 0xc0c00000000, 0xcc00000000]
def g_11 : Nat := 0x44c00000000
def ep_11 : Nat := 0x4800000000000004080000000000000000000000000000044000000000
theorem epk_11 : ep_11 = edgePack m_11 g_11 := by decide +kernel
def bds_11 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_11 : KnownBin bds_11 := by intro b hb; simp [bds_11] at hb
theorem sub_11 : ∀ b ∈ bds_11, m_11 &&& b.1 = b.1 := by intro b hb; simp [bds_11] at hb
theorem gl_11 : ∀ b ∈ bds_11, canon b.1 g_11 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_11] at hb
def cur_11 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_11 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsV4 m_11 g_11 ep_11 1 bds_11 (dagTraceF m_11 s_11 3 f_11) (cur_11 0) s_11 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_11 : treeBlockF 0 1 (dagCheckNodeV4 m_11 g_11 ep_11 bds_11 1 (dagTraceF m_11 s_11 3 f_11) cur_11) = true := by decide +kernel
theorem nc_11 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_11 g_11 ep_11 bds_11 1 (dagTraceF m_11 s_11 3 f_11) cur_11) i = true := fun _ h1 h2 => treeBlockF_at nb_11 h1 h2
theorem lb_11 : LowerBin m_11 s_11 g_11 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_11 kn_11 sub_11 gl_11 rc_11 nc_11

def m_12 : Nat := 0xff000000
def s_12 : List Nat := [0x55000000, 0x33000000, 0xf000000]
def g_12 : Nat := 0x17000000
def ep_12 : Nat := 0x600000000000000120000000000000014000000
theorem epk_12 : ep_12 = edgePack m_12 g_12 := by decide +kernel
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_12 : KnownBin bds_12 := by intro b hb; simp [bds_12] at hb
theorem sub_12 : ∀ b ∈ bds_12, m_12 &&& b.1 = b.1 := by intro b hb; simp [bds_12] at hb
theorem gl_12 : ∀ b ∈ bds_12, canon b.1 g_12 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_12] at hb
def cur_12 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_12 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsV4 m_12 g_12 ep_12 1 bds_12 (dagTraceF m_12 s_12 3 f_12) (cur_12 0) s_12 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12 : treeBlockF 0 1 (dagCheckNodeV4 m_12 g_12 ep_12 bds_12 1 (dagTraceF m_12 s_12 3 f_12) cur_12) = true := by decide +kernel
theorem nc_12 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_12 g_12 ep_12 bds_12 1 (dagTraceF m_12 s_12 3 f_12) cur_12) i = true := fun _ h1 h2 => treeBlockF_at nb_12 h1 h2
theorem lb_12 : LowerBin m_12 s_12 g_12 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_12 kn_12 sub_12 gl_12 rc_12 nc_12

def m_13 : Nat := 0xc0c00000c0c0
def s_13 : List Nat := [0x404000004040, 0xc0000000c0, 0xc0c0]
def g_13 : Nat := 0x40000040c0
def ep_13 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000
theorem epk_13 : ep_13 = edgePack m_13 g_13 := by decide +kernel
def bds_13 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_13 : KnownBin bds_13 := by intro b hb; simp [bds_13] at hb
theorem sub_13 : ∀ b ∈ bds_13, m_13 &&& b.1 = b.1 := by intro b hb; simp [bds_13] at hb
theorem gl_13 : ∀ b ∈ bds_13, canon b.1 g_13 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_13] at hb
def cur_13 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_13 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsV4 m_13 g_13 ep_13 1 bds_13 (dagTraceF m_13 s_13 3 f_13) (cur_13 0) s_13 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_13 : treeBlockF 0 1 (dagCheckNodeV4 m_13 g_13 ep_13 bds_13 1 (dagTraceF m_13 s_13 3 f_13) cur_13) = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_13 g_13 ep_13 bds_13 1 (dagTraceF m_13 s_13 3 f_13) cur_13) i = true := fun _ h1 h2 => treeBlockF_at nb_13 h1 h2
theorem lb_13 : LowerBin m_13 s_13 g_13 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_13 kn_13 sub_13 gl_13 rc_13 nc_13

def m_14 : Nat := 0xf0000000f000000
def s_14 : List Nat := [0x500000005000000, 0x300000003000000, 0xf000000]
def g_14 : Nat := 0x100000007000000
def ep_14 : Nat := 0x600000000000000000000000000000000000000000000000000000001000000020000000100000004000000
theorem epk_14 : ep_14 = edgePack m_14 g_14 := by decide +kernel
def bds_14 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_14 : KnownBin bds_14 := by intro b hb; simp [bds_14] at hb
theorem sub_14 : ∀ b ∈ bds_14, m_14 &&& b.1 = b.1 := by intro b hb; simp [bds_14] at hb
theorem gl_14 : ∀ b ∈ bds_14, canon b.1 g_14 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_14] at hb
def cur_14 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_14 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsV4 m_14 g_14 ep_14 1 bds_14 (dagTraceF m_14 s_14 3 f_14) (cur_14 0) s_14 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14 : treeBlockF 0 1 (dagCheckNodeV4 m_14 g_14 ep_14 bds_14 1 (dagTraceF m_14 s_14 3 f_14) cur_14) = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_14 g_14 ep_14 bds_14 1 (dagTraceF m_14 s_14 3 f_14) cur_14) i = true := fun _ h1 h2 => treeBlockF_at nb_14 h1 h2
theorem lb_14 : LowerBin m_14 s_14 g_14 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_14 kn_14 sub_14 gl_14 rc_14 nc_14

def m_15 : Nat := 0xa0a00000a0a0
def s_15 : List Nat := [0x202000002020, 0xa0000000a0, 0xa0a0]
def g_15 : Nat := 0x20000020a0
def ep_15 : Nat := 0x208000000000000000000000002000000080000000000000000000000020000020000000000000000000
theorem epk_15 : ep_15 = edgePack m_15 g_15 := by decide +kernel
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_15 : KnownBin bds_15 := by intro b hb; simp [bds_15] at hb
theorem sub_15 : ∀ b ∈ bds_15, m_15 &&& b.1 = b.1 := by intro b hb; simp [bds_15] at hb
theorem gl_15 : ∀ b ∈ bds_15, canon b.1 g_15 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_15] at hb
def cur_15 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_15 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV4 m_15 g_15 ep_15 1 bds_15 (dagTraceF m_15 s_15 3 f_15) (cur_15 0) s_15 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15 : treeBlockF 0 1 (dagCheckNodeV4 m_15 g_15 ep_15 bds_15 1 (dagTraceF m_15 s_15 3 f_15) cur_15) = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_15 g_15 ep_15 bds_15 1 (dagTraceF m_15 s_15 3 f_15) cur_15) i = true := fun _ h1 h2 => treeBlockF_at nb_15 h1 h2
theorem lb_15 : LowerBin m_15 s_15 g_15 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_15 kn_15 sub_15 gl_15 rc_15 nc_15

def m_16 : Nat := 0xcc000000cc00
def s_16 : List Nat := [0x440000004400, 0xc0000000c00, 0xcc00]
def g_16 : Nat := 0x40000004c00
def ep_16 : Nat := 0x480000000000000000000000000000000000000004000000080000000000000000000000040000004000
theorem epk_16 : ep_16 = edgePack m_16 g_16 := by decide +kernel
def bds_16 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_16 : KnownBin bds_16 := by intro b hb; simp [bds_16] at hb
theorem sub_16 : ∀ b ∈ bds_16, m_16 &&& b.1 = b.1 := by intro b hb; simp [bds_16] at hb
theorem gl_16 : ∀ b ∈ bds_16, canon b.1 g_16 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_16] at hb
def cur_16 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_16 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV4 m_16 g_16 ep_16 1 bds_16 (dagTraceF m_16 s_16 3 f_16) (cur_16 0) s_16 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16 : treeBlockF 0 1 (dagCheckNodeV4 m_16 g_16 ep_16 bds_16 1 (dagTraceF m_16 s_16 3 f_16) cur_16) = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_16 g_16 ep_16 bds_16 1 (dagTraceF m_16 s_16 3 f_16) cur_16) i = true := fun _ h1 h2 => treeBlockF_at nb_16 h1 h2
theorem lb_16 : LowerBin m_16 s_16 g_16 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_16 kn_16 sub_16 gl_16 rc_16 nc_16

def m_17 : Nat := 0x4444000044440000
def s_17 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_17 : Nat := 0x4000004440000
def ep_17 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
theorem epk_17 : ep_17 = edgePack m_17 g_17 := by decide +kernel
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_17 : KnownBin bds_17 := by intro b hb; simp [bds_17] at hb
theorem sub_17 : ∀ b ∈ bds_17, m_17 &&& b.1 = b.1 := by intro b hb; simp [bds_17] at hb
theorem gl_17 : ∀ b ∈ bds_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_17] at hb
def cur_17 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_17 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV4 m_17 g_17 ep_17 1 bds_17 (dagTraceF m_17 s_17 3 f_17) (cur_17 0) s_17 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17 : treeBlockF 0 1 (dagCheckNodeV4 m_17 g_17 ep_17 bds_17 1 (dagTraceF m_17 s_17 3 f_17) cur_17) = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_17 g_17 ep_17 bds_17 1 (dagTraceF m_17 s_17 3 f_17) cur_17) i = true := fun _ h1 h2 => treeBlockF_at nb_17 h1 h2
theorem lb_17 : LowerBin m_17 s_17 g_17 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_17 kn_17 sub_17 gl_17 rc_17 nc_17

def m_18 : Nat := 0xff0000000000
def s_18 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_18 : Nat := 0x170000000000
def ep_18 : Nat := 0x6000000000000001200000000000000140000000000
theorem epk_18 : ep_18 = edgePack m_18 g_18 := by decide +kernel
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_18 : KnownBin bds_18 := by intro b hb; simp [bds_18] at hb
theorem sub_18 : ∀ b ∈ bds_18, m_18 &&& b.1 = b.1 := by intro b hb; simp [bds_18] at hb
theorem gl_18 : ∀ b ∈ bds_18, canon b.1 g_18 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_18] at hb
def cur_18 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_18 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV4 m_18 g_18 ep_18 1 bds_18 (dagTraceF m_18 s_18 3 f_18) (cur_18 0) s_18 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18 : treeBlockF 0 1 (dagCheckNodeV4 m_18 g_18 ep_18 bds_18 1 (dagTraceF m_18 s_18 3 f_18) cur_18) = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_18 g_18 ep_18 bds_18 1 (dagTraceF m_18 s_18 3 f_18) cur_18) i = true := fun _ h1 h2 => treeBlockF_at nb_18 h1 h2
theorem lb_18 : LowerBin m_18 s_18 g_18 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_18 kn_18 sub_18 gl_18 rc_18 nc_18

def m_19 : Nat := 0xa000a000a000a00
def s_19 : List Nat := [0x200020002000200, 0xa0000000a00, 0xa000a00]
def g_19 : Nat := 0x20002000a00
def ep_19 : Nat := 0x200080000000200000008000000000000000000000000000000000000000200020000000000000000000000
theorem epk_19 : ep_19 = edgePack m_19 g_19 := by decide +kernel
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_19 : KnownBin bds_19 := by intro b hb; simp [bds_19] at hb
theorem sub_19 : ∀ b ∈ bds_19, m_19 &&& b.1 = b.1 := by intro b hb; simp [bds_19] at hb
theorem gl_19 : ∀ b ∈ bds_19, canon b.1 g_19 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_19] at hb
def cur_19 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_19 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV4 m_19 g_19 ep_19 1 bds_19 (dagTraceF m_19 s_19 3 f_19) (cur_19 0) s_19 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19 : treeBlockF 0 1 (dagCheckNodeV4 m_19 g_19 ep_19 bds_19 1 (dagTraceF m_19 s_19 3 f_19) cur_19) = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_19 g_19 ep_19 bds_19 1 (dagTraceF m_19 s_19 3 f_19) cur_19) i = true := fun _ h1 h2 => treeBlockF_at nb_19 h1 h2
theorem lb_19 : LowerBin m_19 s_19 g_19 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_19 kn_19 sub_19 gl_19 rc_19 nc_19

def m_20 : Nat := 0xaa000000aa00
def s_20 : List Nat := [0x220000002200, 0xa0000000a00, 0xaa00]
def g_20 : Nat := 0x20000002a00
def ep_20 : Nat := 0x280000000000000000000000000000000000000002000000080000000200000020000000000000000000
theorem epk_20 : ep_20 = edgePack m_20 g_20 := by decide +kernel
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_20 : KnownBin bds_20 := by intro b hb; simp [bds_20] at hb
theorem sub_20 : ∀ b ∈ bds_20, m_20 &&& b.1 = b.1 := by intro b hb; simp [bds_20] at hb
theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_20] at hb
def cur_20 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_20 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV4 m_20 g_20 ep_20 1 bds_20 (dagTraceF m_20 s_20 3 f_20) (cur_20 0) s_20 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20 : treeBlockF 0 1 (dagCheckNodeV4 m_20 g_20 ep_20 bds_20 1 (dagTraceF m_20 s_20 3 f_20) cur_20) = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_20 g_20 ep_20 bds_20 1 (dagTraceF m_20 s_20 3 f_20) cur_20) i = true := fun _ h1 h2 => treeBlockF_at nb_20 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_20 kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0xaa00aa00
def s_21 : List Nat := [0x22002200, 0xa000a00, 0xaa00]
def g_21 : Nat := 0x2002a00
def ep_21 : Nat := 0x28000000000000000000000000000200080000000000020020000000000000000000
theorem epk_21 : ep_21 = edgePack m_21 g_21 := by decide +kernel
def bds_21 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_21 : KnownBin bds_21 := by intro b hb; simp [bds_21] at hb
theorem sub_21 : ∀ b ∈ bds_21, m_21 &&& b.1 = b.1 := by intro b hb; simp [bds_21] at hb
theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_21] at hb
def cur_21 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_21 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV4 m_21 g_21 ep_21 1 bds_21 (dagTraceF m_21 s_21 3 f_21) (cur_21 0) s_21 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21 : treeBlockF 0 1 (dagCheckNodeV4 m_21 g_21 ep_21 bds_21 1 (dagTraceF m_21 s_21 3 f_21) cur_21) = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_21 g_21 ep_21 bds_21 1 (dagTraceF m_21 s_21 3 f_21) cur_21) i = true := fun _ h1 h2 => treeBlockF_at nb_21 h1 h2
theorem lb_21 : LowerBin m_21 s_21 g_21 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_21 kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0xcc00cc00
def s_22 : List Nat := [0x44004400, 0xc000c00, 0xcc00]
def g_22 : Nat := 0x4004c00
def ep_22 : Nat := 0x48000000000000000000000000000400080000000000000000000000000004004000
theorem epk_22 : ep_22 = edgePack m_22 g_22 := by decide +kernel
def bds_22 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_22 : KnownBin bds_22 := by intro b hb; simp [bds_22] at hb
theorem sub_22 : ∀ b ∈ bds_22, m_22 &&& b.1 = b.1 := by intro b hb; simp [bds_22] at hb
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_22] at hb
def cur_22 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_22 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV4 m_22 g_22 ep_22 1 bds_22 (dagTraceF m_22 s_22 3 f_22) (cur_22 0) s_22 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22 : treeBlockF 0 1 (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 1 (dagTraceF m_22 s_22 3 f_22) cur_22) = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 1 (dagTraceF m_22 s_22 3 f_22) cur_22) i = true := fun _ h1 h2 => treeBlockF_at nb_22 h1 h2
theorem lb_22 : LowerBin m_22 s_22 g_22 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_22 kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0xf0000000f000
def s_23 : List Nat := [0x500000005000, 0x300000003000, 0xf000]
def g_23 : Nat := 0x100000007000
def ep_23 : Nat := 0x600000000000000000000000000000000000000000000000000000001000000020000000100000004000
theorem epk_23 : ep_23 = edgePack m_23 g_23 := by decide +kernel
def bds_23 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_23 : KnownBin bds_23 := by intro b hb; simp [bds_23] at hb
theorem sub_23 : ∀ b ∈ bds_23, m_23 &&& b.1 = b.1 := by intro b hb; simp [bds_23] at hb
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_23] at hb
def cur_23 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_23 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV4 m_23 g_23 ep_23 1 bds_23 (dagTraceF m_23 s_23 3 f_23) (cur_23 0) s_23 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23 : treeBlockF 0 1 (dagCheckNodeV4 m_23 g_23 ep_23 bds_23 1 (dagTraceF m_23 s_23 3 f_23) cur_23) = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_23 g_23 ep_23 bds_23 1 (dagTraceF m_23 s_23 3 f_23) cur_23) i = true := fun _ h1 h2 => treeBlockF_at nb_23 h1 h2
theorem lb_23 : LowerBin m_23 s_23 g_23 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_23 kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0xf000f000
def s_24 : List Nat := [0x50005000, 0x30003000, 0xf000]
def g_24 : Nat := 0x10007000
def ep_24 : Nat := 0x60000000000000000000000000000000000000000000100020000000000010004000
theorem epk_24 : ep_24 = edgePack m_24 g_24 := by decide +kernel
def bds_24 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_24 : KnownBin bds_24 := by intro b hb; simp [bds_24] at hb
theorem sub_24 : ∀ b ∈ bds_24, m_24 &&& b.1 = b.1 := by intro b hb; simp [bds_24] at hb
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_24] at hb
def cur_24 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_24 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV4 m_24 g_24 ep_24 1 bds_24 (dagTraceF m_24 s_24 3 f_24) (cur_24 0) s_24 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24 : treeBlockF 0 1 (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 1 (dagTraceF m_24 s_24 3 f_24) cur_24) = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 1 (dagTraceF m_24 s_24 3 f_24) cur_24) i = true := fun _ h1 h2 => treeBlockF_at nb_24 h1 h2
theorem lb_24 : LowerBin m_24 s_24 g_24 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_24 kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0xc0c0c0c0
def s_25 : List Nat := [0x40404040, 0xc000c0, 0xc0c0]
def g_25 : Nat := 0x4040c0
def ep_25 : Nat := 0x40800000000000400080000000000000000000000000000000000000000000404000
theorem epk_25 : ep_25 = edgePack m_25 g_25 := by decide +kernel
def bds_25 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_25 : KnownBin bds_25 := by intro b hb; simp [bds_25] at hb
theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by intro b hb; simp [bds_25] at hb
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_25] at hb
def cur_25 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_25 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV4 m_25 g_25 ep_25 1 bds_25 (dagTraceF m_25 s_25 3 f_25) (cur_25 0) s_25 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25 : treeBlockF 0 1 (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 1 (dagTraceF m_25 s_25 3 f_25) cur_25) = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 1 (dagTraceF m_25 s_25 3 f_25) cur_25) i = true := fun _ h1 h2 => treeBlockF_at nb_25 h1 h2
theorem lb_25 : LowerBin m_25 s_25 g_25 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_25 kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0x888800008888
def s_26 : List Nat := [0x80800000808, 0x8800000088, 0x8888]
def g_26 : Nat := 0x800000888
def ep_26 : Nat := 0x88000000000000000000000000800000080000000080000080000000000000000000000000000000000
theorem epk_26 : ep_26 = edgePack m_26 g_26 := by decide +kernel
def bds_26 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_26 : KnownBin bds_26 := by intro b hb; simp [bds_26] at hb
theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by intro b hb; simp [bds_26] at hb
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_26] at hb
def cur_26 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_26 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV4 m_26 g_26 ep_26 1 bds_26 (dagTraceF m_26 s_26 3 f_26) (cur_26 0) s_26 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26 : treeBlockF 0 1 (dagCheckNodeV4 m_26 g_26 ep_26 bds_26 1 (dagTraceF m_26 s_26 3 f_26) cur_26) = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_26 g_26 ep_26 bds_26 1 (dagTraceF m_26 s_26 3 f_26) cur_26) i = true := fun _ h1 h2 => treeBlockF_at nb_26 h1 h2
theorem lb_26 : LowerBin m_26 s_26 g_26 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_26 kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0x88888888
def s_27 : List Nat := [0x8080808, 0x880088, 0x8888]
def g_27 : Nat := 0x80888
def ep_27 : Nat := 0x8800000000000080080000000000008080000000000000000000000000000000000
theorem epk_27 : ep_27 = edgePack m_27 g_27 := by decide +kernel
def bds_27 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_27 : KnownBin bds_27 := by intro b hb; simp [bds_27] at hb
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp [bds_27] at hb
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_27] at hb
def cur_27 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_27 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV4 m_27 g_27 ep_27 1 bds_27 (dagTraceF m_27 s_27 3 f_27) (cur_27 0) s_27 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27 : treeBlockF 0 1 (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 1 (dagTraceF m_27 s_27 3 f_27) cur_27) = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 1 (dagTraceF m_27 s_27 3 f_27) cur_27) i = true := fun _ h1 h2 => treeBlockF_at nb_27 h1 h2
theorem lb_27 : LowerBin m_27 s_27 g_27 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_27 kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xf0f000000000
def s_28 : List Nat := [0x505000000000, 0x303000000000, 0xf000000000]
def g_28 : Nat := 0x107000000000
def ep_28 : Nat := 0x6000000000000000000000000000001020000000000000104000000000
theorem epk_28 : ep_28 = edgePack m_28 g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_28 : KnownBin bds_28 := by intro b hb; simp [bds_28] at hb
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp [bds_28] at hb
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_28] at hb
def cur_28 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_28 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV4 m_28 g_28 ep_28 1 bds_28 (dagTraceF m_28 s_28 3 f_28) (cur_28 0) s_28 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28 : treeBlockF 0 1 (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 1 (dagTraceF m_28 s_28 3 f_28) cur_28) = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 1 (dagTraceF m_28 s_28 3 f_28) cur_28) i = true := fun _ h1 h2 => treeBlockF_at nb_28 h1 h2
theorem lb_28 : LowerBin m_28 s_28 g_28 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_28 kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xffff00000000
def s_29 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_29 : Nat := 0x177f00000000
def ep_29 : Nat := 0x6800000000000006080000000000001220000000000000144000000000
theorem epk_29 : ep_29 = edgePack m_29 g_29 := by decide +kernel
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18), (m_28, s_28, 4, g_28), (m_11, s_11, 4, g_11), (m_10, s_10, 4, g_10)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_18
  · exact lb_28
  · exact lb_11
  · exact lb_10
theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_29_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_29_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_29 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_29_1 (Nat.sub p 32)) (cc_29_0 p) (Nat.blt p 32)
def f_29 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV4 m_29 g_29 ep_29 43 bds_29 (dagTraceF m_29 s_29 6 f_29) (cur_29 0) s_29 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_0 : treeBlockF 0 32 (dagCheckNodeV4 m_29 g_29 ep_29 bds_29 43 (dagTraceF m_29 s_29 6 f_29) cur_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_1 : treeBlockF 32 43 (dagCheckNodeV4 m_29 g_29 ep_29 bds_29 43 (dagTraceF m_29 s_29 6 f_29) cur_29) = true := by decide +kernel
theorem nj_29_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_29 g_29 ep_29 bds_29 43 (dagTraceF m_29 s_29 6 f_29) cur_29) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_29_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_29_1 h1 h2)
theorem nc_29 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_29 g_29 ep_29 bds_29 43 (dagTraceF m_29 s_29 6 f_29) cur_29) i = true := nj_29_1
theorem lb_29 : LowerBin m_29 s_29 g_29 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_29 kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0xff00ff00000000
def s_30 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_30 : Nat := 0x1f007f00000000
def ep_30 : Nat := 0x60000000000000000000000000000e00080000000000100020000000000010004000000000
theorem epk_30 : ep_30 = edgePack m_30 g_30 := by decide +kernel
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_30 : Nat → List (Nat × Nat) := fun _ => []
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV4 m_30 g_30 ep_30 0 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_30 g_30 ep_30 bds_30 0 (dagTraceF m_30 s_30 4 f_30) cur_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_30 kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0x3333333300000000
def s_31 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_31 : Nat := 0x1113133300000000
def ep_31 : Nat := 0x220000000000002002000000000000202000000000000000000000000001110100000000000
theorem epk_31 : ep_31 = edgePack m_31 g_31 := by decide +kernel
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV4 m_31 g_31 ep_31 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_31 g_31 ep_31 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_31 kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0xc0c0c0c0c0c0c0c0
def s_32 : List Nat := [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0]
def g_32 : Nat := 0x40004040c0
def ep_32 : Nat := 0x40408000000040000040800000004000400080000000000000000000000000000000000000004000404000
theorem epk_32 : ep_32 = edgePack m_32 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13), (m_25, s_25, 4, g_25), (m_7, s_7, 4, g_7), (m_2, s_2, 4, g_2)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_13
  · exact lb_25
  · exact lb_7
  · exact lb_2
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_32_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_32_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_32 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_32_1 (Nat.sub p 32)) (cc_32_0 p) (Nat.blt p 32)
def f_32 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV4 m_32 g_32 ep_32 43 bds_32 (dagTraceF m_32 s_32 6 f_32) (cur_32 0) s_32 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_0 : treeBlockF 0 32 (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 43 (dagTraceF m_32 s_32 6 f_32) cur_32) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_1 : treeBlockF 32 43 (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 43 (dagTraceF m_32 s_32 6 f_32) cur_32) = true := by decide +kernel
theorem nj_32_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 43 (dagTraceF m_32 s_32 6 f_32) cur_32) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_32_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_32_1 h1 h2)
theorem nc_32 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 43 (dagTraceF m_32 s_32 6 f_32) cur_32) i = true := nj_32_1
theorem lb_32 : LowerBin m_32 s_32 g_32 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_32 kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xcccc0000cccc0000
def s_33 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_33 : Nat := 0xc0000044c0000
def ep_33 : Nat := 0x44000000000000000000000000c000000480000000c00000408000000000000000000000000000004400000
theorem epk_33 : ep_33 = edgePack m_33 g_33 := by decide +kernel
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV4 m_33 g_33 ep_33 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_33 g_33 ep_33 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_33 kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0x5555000055550000
def s_34 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_34 : Nat := 0x1115000015550000
def ep_34 : Nat := 0x440000000000000000000000004000000400000000400000400000011100000100000000000000000000000
theorem epk_34 : ep_34 = edgePack m_34 g_34 := by decide +kernel
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_17
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV4 m_34 g_34 ep_34 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_34 g_34 ep_34 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_34 kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xaa00aa00aa00aa00
def s_35 : List Nat := [0x2200220022002200, 0xa000a000a000a00, 0xaa000000aa00, 0xaa00aa00]
def g_35 : Nat := 0x20002002a00
def ep_35 : Nat := 0x200280000000200000028000000000000000000000002000200080000000200020020000000000000000000
theorem epk_35 : ep_35 = edgePack m_35 g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 4, g_20), (m_21, s_21, 4, g_21), (m_3, s_3, 4, g_3), (m_19, s_19, 4, g_19)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_20
  · exact lb_21
  · exact lb_3
  · exact lb_19
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_35_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_35_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_35 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_35_1 (Nat.sub p 32)) (cc_35_0 p) (Nat.blt p 32)
def f_35 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV4 m_35 g_35 ep_35 43 bds_35 (dagTraceF m_35 s_35 6 f_35) (cur_35 0) s_35 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_0 : treeBlockF 0 32 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) cur_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_1 : treeBlockF 32 43 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) cur_35) = true := by decide +kernel
theorem nj_35_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) cur_35) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_35_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_35_1 h1 h2)
theorem nc_35 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) cur_35) i = true := nj_35_1
theorem lb_35 : LowerBin m_35 s_35 g_35 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_35 kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0xff000000ff00
def s_36 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_36 : Nat := 0x170000007f00
def ep_36 : Nat := 0x680000000000000000000000000000000000000006000000080000001200000020000000140000004000
theorem epk_36 : ep_36 = edgePack m_36 g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18), (m_23, s_23, 4, g_23), (m_16, s_16, 4, g_16), (m_20, s_20, 4, g_20)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_18
  · exact lb_23
  · exact lb_16
  · exact lb_20
theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_36_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_36_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_36 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_36_1 (Nat.sub p 32)) (cc_36_0 p) (Nat.blt p 32)
def f_36 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV4 m_36 g_36 ep_36 43 bds_36 (dagTraceF m_36 s_36 6 f_36) (cur_36 0) s_36 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_0 : treeBlockF 0 32 (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 43 (dagTraceF m_36 s_36 6 f_36) cur_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_1 : treeBlockF 32 43 (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 43 (dagTraceF m_36 s_36 6 f_36) cur_36) = true := by decide +kernel
theorem nj_36_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 43 (dagTraceF m_36 s_36 6 f_36) cur_36) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_36_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_36_1 h1 h2)
theorem nc_36 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 43 (dagTraceF m_36 s_36 6 f_36) cur_36) i = true := nj_36_1
theorem lb_36 : LowerBin m_36 s_36 g_36 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_36 kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0xf0f00000f0f0
def s_37 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_37 : Nat := 0x1070000070f0
def ep_37 : Nat := 0x608000000000000000000000006000000080000000000000000000001020000020000000104000004000
theorem epk_37 : ep_37 = edgePack m_37 g_37 := by decide +kernel
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 4, g_23), (m_28, s_28, 4, g_28), (m_13, s_13, 4, g_13), (m_15, s_15, 4, g_15)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_23
  · exact lb_28
  · exact lb_13
  · exact lb_15
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_37_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_37_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_37 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_37_1 (Nat.sub p 32)) (cc_37_0 p) (Nat.blt p 32)
def f_37 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV4 m_37 g_37 ep_37 43 bds_37 (dagTraceF m_37 s_37 6 f_37) (cur_37 0) s_37 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_0 : treeBlockF 0 32 (dagCheckNodeV4 m_37 g_37 ep_37 bds_37 43 (dagTraceF m_37 s_37 6 f_37) cur_37) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_1 : treeBlockF 32 43 (dagCheckNodeV4 m_37 g_37 ep_37 bds_37 43 (dagTraceF m_37 s_37 6 f_37) cur_37) = true := by decide +kernel
theorem nj_37_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_37 g_37 ep_37 bds_37 43 (dagTraceF m_37 s_37 6 f_37) cur_37) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_37_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_37_1 h1 h2)
theorem nc_37 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_37 g_37 ep_37 bds_37 43 (dagTraceF m_37 s_37 6 f_37) cur_37) i = true := nj_37_1
theorem lb_37 : LowerBin m_37 s_37 g_37 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_37 kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xf0f00000f0f0000
def s_38 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_38 : Nat := 0x10f0000070f0000
def ep_38 : Nat := 0x60000000000000000000000000e000000080000000000000000000001000000020000000100000004000000
theorem epk_38 : ep_38 = edgePack m_38 g_38 := by decide +kernel
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_14
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV4 m_38 g_38 ep_38 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_38 g_38 ep_38 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_38 kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xcccc0000cccc
def s_39 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_39 : Nat := 0x44c00004ccc
def ep_39 : Nat := 0x488000000000000000000000004800000080000004080000080000000000000000000000044000004000
theorem epk_39 : ep_39 = edgePack m_39 g_39 := by decide +kernel
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11), (m_16, s_16, 4, g_16), (m_13, s_13, 4, g_13), (m_26, s_26, 4, g_26)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_11
  · exact lb_16
  · exact lb_13
  · exact lb_26
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_39_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_39_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_39 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_39_1 (Nat.sub p 32)) (cc_39_0 p) (Nat.blt p 32)
def f_39 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV4 m_39 g_39 ep_39 43 bds_39 (dagTraceF m_39 s_39 6 f_39) (cur_39 0) s_39 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_0 : treeBlockF 0 32 (dagCheckNodeV4 m_39 g_39 ep_39 bds_39 43 (dagTraceF m_39 s_39 6 f_39) cur_39) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_1 : treeBlockF 32 43 (dagCheckNodeV4 m_39 g_39 ep_39 bds_39 43 (dagTraceF m_39 s_39 6 f_39) cur_39) = true := by decide +kernel
theorem nj_39_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_39 g_39 ep_39 bds_39 43 (dagTraceF m_39 s_39 6 f_39) cur_39) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_39_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_39_1 h1 h2)
theorem nc_39 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_39 g_39 ep_39 bds_39 43 (dagTraceF m_39 s_39 6 f_39) cur_39) i = true := nj_39_1
theorem lb_39 : LowerBin m_39 s_39 g_39 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_39 kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0xaaaa0000aaaa
def s_40 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_40 : Nat := 0x22a00002aaa
def ep_40 : Nat := 0x288000000000000000000000002800000080000002080000080000000220000020000000000000000000
theorem epk_40 : ep_40 = edgePack m_40 g_40 := by decide +kernel
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10), (m_20, s_20, 4, g_20), (m_15, s_15, 4, g_15), (m_26, s_26, 4, g_26)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_10
  · exact lb_20
  · exact lb_15
  · exact lb_26
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_40_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_40_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_40 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_40_1 (Nat.sub p 32)) (cc_40_0 p) (Nat.blt p 32)
def f_40 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV4 m_40 g_40 ep_40 43 bds_40 (dagTraceF m_40 s_40 6 f_40) (cur_40 0) s_40 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_0 : treeBlockF 0 32 (dagCheckNodeV4 m_40 g_40 ep_40 bds_40 43 (dagTraceF m_40 s_40 6 f_40) cur_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_1 : treeBlockF 32 43 (dagCheckNodeV4 m_40 g_40 ep_40 bds_40 43 (dagTraceF m_40 s_40 6 f_40) cur_40) = true := by decide +kernel
theorem nj_40_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_40 g_40 ep_40 bds_40 43 (dagTraceF m_40 s_40 6 f_40) cur_40) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_40_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_40_1 h1 h2)
theorem nc_40 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_40 g_40 ep_40 bds_40 43 (dagTraceF m_40 s_40 6 f_40) cur_40) i = true := nj_40_1
theorem lb_40 : LowerBin m_40 s_40 g_40 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_40 kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0x3300330033003300
def s_41 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_41 : Nat := 0x1100130013003300
def ep_41 : Nat := 0x200200000000200000020000000000000000000000002000200000000000000000000001100100010000000
theorem epk_41 : ep_41 = edgePack m_41 g_41 := by decide +kernel
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV4 m_41 g_41 ep_41 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_41 g_41 ep_41 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_41 kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xf000f000f000f00
def s_42 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_42 : Nat := 0x100070007000f00
def ep_42 : Nat := 0x600080000000600000008000000000000000000000000000000000001000200020000000100040004000000
theorem epk_42 : ep_42 = edgePack m_42 g_42 := by decide +kernel
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_14, s_14, 4, g_14), (m_6, s_6, 4, g_6), (m_19, s_19, 4, g_19)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_5
  · exact lb_14
  · exact lb_6
  · exact lb_19
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_42_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_42_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_42 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_42_1 (Nat.sub p 32)) (cc_42_0 p) (Nat.blt p 32)
def f_42 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV4 m_42 g_42 ep_42 43 bds_42 (dagTraceF m_42 s_42 6 f_42) (cur_42 0) s_42 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_0 : treeBlockF 0 32 (dagCheckNodeV4 m_42 g_42 ep_42 bds_42 43 (dagTraceF m_42 s_42 6 f_42) cur_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_1 : treeBlockF 32 43 (dagCheckNodeV4 m_42 g_42 ep_42 bds_42 43 (dagTraceF m_42 s_42 6 f_42) cur_42) = true := by decide +kernel
theorem nj_42_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_42 g_42 ep_42 bds_42 43 (dagTraceF m_42 s_42 6 f_42) cur_42) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_42_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_42_1 h1 h2)
theorem nc_42 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_42 g_42 ep_42 bds_42 43 (dagTraceF m_42 s_42 6 f_42) cur_42) i = true := nj_42_1
theorem lb_42 : LowerBin m_42 s_42 g_42 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_42 kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xf000f000f000f000
def s_43 : List Nat := [0x5000500050005000, 0x3000300030003000, 0xf0000000f000, 0xf000f000]
def g_43 : Nat := 0x1000100010007000
def ep_43 : Nat := 0x600000000000000060000000000000000000000000000000000010001000100020001000100010004000
theorem epk_43 : ep_43 = edgePack m_43 g_43 := by decide +kernel
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 4, g_23)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_23
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV4 m_43 g_43 ep_43 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_43 g_43 ep_43 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_43 kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xcccccccc
def s_44 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_44 : Nat := 0x44c4ccc
def ep_44 : Nat := 0x48800000000000480080000000000408080000000000000000000000000004404000
theorem epk_44 : ep_44 = edgePack m_44 g_44 := by decide +kernel
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_22, s_22, 4, g_22), (m_25, s_25, 4, g_25), (m_27, s_27, 4, g_27)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_0
  · exact lb_22
  · exact lb_25
  · exact lb_27
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_44_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_44_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_44 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_44_1 (Nat.sub p 32)) (cc_44_0 p) (Nat.blt p 32)
def f_44 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV4 m_44 g_44 ep_44 43 bds_44 (dagTraceF m_44 s_44 6 f_44) (cur_44 0) s_44 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_0 : treeBlockF 0 32 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 43 (dagTraceF m_44 s_44 6 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_1 : treeBlockF 32 43 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 43 (dagTraceF m_44 s_44 6 f_44) cur_44) = true := by decide +kernel
theorem nj_44_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 43 (dagTraceF m_44 s_44 6 f_44) cur_44) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_44_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_44_1 h1 h2)
theorem nc_44 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 43 (dagTraceF m_44 s_44 6 f_44) cur_44) i = true := nj_44_1
theorem lb_44 : LowerBin m_44 s_44 g_44 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_44 kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0xcc00cc00cc00cc
def s_45 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_45 : Nat := 0xc004c004c00cc
def ep_45 : Nat := 0x40008000000040000000800000000000000000000c00080008000000000000000000000000004000400000
theorem epk_45 : ep_45 = edgePack m_45 g_45 := by decide +kernel
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV4 m_45 g_45 ep_45 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_45 g_45 ep_45 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_45 kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0xffff0000
def s_46 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_46 : Nat := 0x175f0000
def ep_46 : Nat := 0x48000000000000060a000000000000120000000000000014500000
theorem epk_46 : ep_46 = edgePack m_46 g_46 := by decide +kernel
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV4 m_46 g_46 ep_46 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_46 g_46 ep_46 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_46 kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xff00ff00
def s_47 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_47 : Nat := 0x17007f00
def ep_47 : Nat := 0x68000000000000000000000000000600080000000000120020000000000014004000
theorem epk_47 : ep_47 = edgePack m_47 g_47 := by decide +kernel
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12), (m_24, s_24, 4, g_24), (m_22, s_22, 4, g_22), (m_21, s_21, 4, g_21)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_12
  · exact lb_24
  · exact lb_22
  · exact lb_21
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_47_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_47_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_47 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_47_1 (Nat.sub p 32)) (cc_47_0 p) (Nat.blt p 32)
def f_47 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV4 m_47 g_47 ep_47 43 bds_47 (dagTraceF m_47 s_47 6 f_47) (cur_47 0) s_47 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_0 : treeBlockF 0 32 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 43 (dagTraceF m_47 s_47 6 f_47) cur_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_1 : treeBlockF 32 43 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 43 (dagTraceF m_47 s_47 6 f_47) cur_47) = true := by decide +kernel
theorem nj_47_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 43 (dagTraceF m_47 s_47 6 f_47) cur_47) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_47_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_47_1 h1 h2)
theorem nc_47 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 43 (dagTraceF m_47 s_47 6 f_47) cur_47) i = true := nj_47_1
theorem lb_47 : LowerBin m_47 s_47 g_47 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_47 kn_47 sub_47 gl_47 rc_47 nc_47

def m_48 : Nat := 0xff000000ff000000
def s_48 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_48 : Nat := 0x1100000017000000
def ep_48 : Nat := 0x600000000000000000000000000000000000000000000000600000011000000120000001100000014000000
theorem epk_48 : ep_48 = edgePack m_48 g_48 := by decide +kernel
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
theorem kn_48 : KnownBin bds_48 := by
  intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV4 m_48 g_48 ep_48 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_48 g_48 ep_48 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_48 kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0x4444444444444444
def s_49 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_49 : Nat := 0x4044404444444
def ep_49 : Nat := 0x440400000000440000040000004004000400000000404000400000000000000000000000000000000000000
theorem epk_49 : ep_49 = edgePack m_49 g_49 := by decide +kernel
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8), (m_17, s_17, 4, g_17), (m_4, s_4, 4, g_4), (m_7, s_7, 4, g_7)]
theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_8
  · exact lb_17
  · exact lb_4
  · exact lb_7
theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_49_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_49_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_49 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_49_1 (Nat.sub p 32)) (cc_49_0 p) (Nat.blt p 32)
def f_49 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV4 m_49 g_49 ep_49 43 bds_49 (dagTraceF m_49 s_49 6 f_49) (cur_49 0) s_49 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_0 : treeBlockF 0 32 (dagCheckNodeV4 m_49 g_49 ep_49 bds_49 43 (dagTraceF m_49 s_49 6 f_49) cur_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_1 : treeBlockF 32 43 (dagCheckNodeV4 m_49 g_49 ep_49 bds_49 43 (dagTraceF m_49 s_49 6 f_49) cur_49) = true := by decide +kernel
theorem nj_49_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_49 g_49 ep_49 bds_49 43 (dagTraceF m_49 s_49 6 f_49) cur_49) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_49_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_49_1 h1 h2)
theorem nc_49 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_49 g_49 ep_49 bds_49 43 (dagTraceF m_49 s_49 6 f_49) cur_49) i = true := nj_49_1
theorem lb_49 : LowerBin m_49 s_49 g_49 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_49 kn_49 sub_49 gl_49 rc_49 nc_49

def m_50 : Nat := 0x5555555555555555
def s_50 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_50 : Nat := 0x1115155515555555
def ep_50 : Nat := 0x440400000000440000040000004004000400000000404000400000011101000100000000000000000000000
theorem epk_50 : ep_50 = edgePack m_50 g_50 := by decide +kernel
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_49, s_49, 7, g_49)]
theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_49
theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV4 m_50 g_50 ep_50 0 bds_50 (dagTraceF m_50 s_50 7 f_50) (cur_50 0) s_50 7 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_50 g_50 ep_50 bds_50 0 (dagTraceF m_50 s_50 7 f_50) cur_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_50 kn_50 sub_50 gl_50 rc_50 nc_50

def m_51 : Nat := 0xf0f0f0f0f0f0f0f
def s_51 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_51 : Nat := 0x10f070f070f0f0f
def ep_51 : Nat := 0x60008000000060000000800000e000800080000000000000000000001000200020000000100040004000000
theorem epk_51 : ep_51 = edgePack m_51 g_51 := by decide +kernel
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_42, s_42, 7, g_42)]
theorem kn_51 : KnownBin bds_51 := by
  intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_42
theorem sub_51 : ∀ b ∈ bds_51, m_51 &&& b.1 = b.1 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_51 : ∀ b ∈ bds_51, canon b.1 g_51 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV4 m_51 g_51 ep_51 0 bds_51 (dagTraceF m_51 s_51 7 f_51) (cur_51 0) s_51 7 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_51 g_51 ep_51 bds_51 0 (dagTraceF m_51 s_51 7 f_51) cur_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_51 kn_51 sub_51 gl_51 rc_51 nc_51

def m_52 : Nat := 0xaaaaaaaaaaaaaaaa
def s_52 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_52 : Nat := 0xa022a020a2aaa
def ep_52 : Nat := 0x200288000000220000028a0000a002800080080000a0208020a080000000220020020000000000000000000
theorem epk_52 : ep_52 = edgePack m_52 g_52 := by decide +kernel
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_35, s_35, 7, g_35)]
theorem kn_52 : KnownBin bds_52 := by
  intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_35
theorem sub_52 : ∀ b ∈ bds_52, m_52 &&& b.1 = b.1 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_52 : ∀ b ∈ bds_52, canon b.1 g_52 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV4 m_52 g_52 ep_52 0 bds_52 (dagTraceF m_52 s_52 7 f_52) (cur_52 0) s_52 7 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_52 g_52 ep_52 bds_52 0 (dagTraceF m_52 s_52 7 f_52) cur_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_52 kn_52 sub_52 gl_52 rc_52 nc_52

def m_53 : Nat := 0xff00ff00ff00ff
def s_53 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_53 : Nat := 0x1f007f005f00ff
def ep_53 : Nat := 0x40008000000060000000a00000000000000000000e0008000a000000100020000000000010004000500000
theorem epk_53 : ep_53 = edgePack m_53 g_53 := by decide +kernel
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_30, s_30, 5, g_30)]
theorem kn_53 : KnownBin bds_53 := by
  intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_30
theorem sub_53 : ∀ b ∈ bds_53, m_53 &&& b.1 = b.1 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_53 : ∀ b ∈ bds_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV4 m_53 g_53 ep_53 0 bds_53 (dagTraceF m_53 s_53 5 f_53) (cur_53 0) s_53 5 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_53 g_53 ep_53 bds_53 0 (dagTraceF m_53 s_53 5 f_53) cur_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_53 kn_53 sub_53 gl_53 rc_53 nc_53

def m_54 : Nat := 0xffffffff00000000
def s_54 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_54 : Nat := 0x111f177f00000000
def ep_54 : Nat := 0x66000000000000e006800000000000e06080000000011101220000000001110144000000000
theorem epk_54 : ep_54 = edgePack m_54 g_54 := by decide +kernel
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_29, s_29, 7, g_29)]
theorem kn_54 : KnownBin bds_54 := by
  intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_29
theorem sub_54 : ∀ b ∈ bds_54, m_54 &&& b.1 = b.1 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_54 : ∀ b ∈ bds_54, canon b.1 g_54 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV4 m_54 g_54 ep_54 0 bds_54 (dagTraceF m_54 s_54 7 f_54) (cur_54 0) s_54 7 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_54 g_54 ep_54 bds_54 0 (dagTraceF m_54 s_54 7 f_54) cur_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_54 kn_54 sub_54 gl_54 rc_54 nc_54

def m_55 : Nat := 0xffffffff
def s_55 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_55 : Nat := 0x175f7fff
def ep_55 : Nat := 0x68a0000000000048008000000000060a080000000000120020000000000014504000
theorem epk_55 : ep_55 = edgePack m_55 g_55 := by decide +kernel
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_44, s_44, 7, g_44)]
theorem kn_55 : KnownBin bds_55 := by
  intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_44
theorem sub_55 : ∀ b ∈ bds_55, m_55 &&& b.1 = b.1 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_55 : ∀ b ∈ bds_55, canon b.1 g_55 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_55 : Nat → List (Nat × Nat) := fun _ => []
def f_55 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV4 m_55 g_55 ep_55 0 bds_55 (dagTraceF m_55 s_55 7 f_55) (cur_55 0) s_55 7 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_55 g_55 ep_55 bds_55 0 (dagTraceF m_55 s_55 7 f_55) cur_55 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_55 : LowerBin m_55 s_55 g_55 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_55 kn_55 sub_55 gl_55 rc_55 nc_55

def g_56 : Nat := 0x111f177f175f7fff
def ep_56 : Nat := 0x640688000000660000068a0000e006800480080000e0608060a080011101220120020001110144014504000
theorem epk_56 : ep_56 = edgePack fullMask g_56 := by decide +kernel
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_47, s_47, 7, g_47), (m_32, s_32, 7, g_32), (m_36, s_36, 7, g_36), (m_51, s_51, 8, g_51), (m_54, s_54, 8, g_54), (m_50, s_50, 8, g_50), (m_37, s_37, 7, g_37), (m_42, s_42, 7, g_42), (m_52, s_52, 8, g_52), (m_29, s_29, 7, g_29), (m_35, s_35, 7, g_35), (m_49, s_49, 7, g_49), (m_39, s_39, 7, g_39), (m_53, s_53, 6, g_53), (m_44, s_44, 7, g_44), (m_40, s_40, 7, g_40), (m_41, s_41, 5, g_41), (m_48, s_48, 5, g_48), (m_45, s_45, 5, g_45), (m_43, s_43, 5, g_43), (m_31, s_31, 5, g_31), (m_33, s_33, 5, g_33), (m_38, s_38, 5, g_38), (m_34, s_34, 5, g_34), (m_46, s_46, 5, g_46), (m_26, s_26, 4, g_26), (m_30, s_30, 5, g_30)]
theorem kn_56 : KnownBin bds_56 := by
  intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_47
  · exact lb_32
  · exact lb_36
  · exact lb_51
  · exact lb_54
  · exact lb_50
  · exact lb_37
  · exact lb_42
  · exact lb_52
  · exact lb_29
  · exact lb_35
  · exact lb_49
  · exact lb_39
  · exact lb_53
  · exact lb_44
  · exact lb_40
  · exact lb_41
  · exact lb_48
  · exact lb_45
  · exact lb_43
  · exact lb_31
  · exact lb_33
  · exact lb_38
  · exact lb_34
  · exact lb_46
  · exact lb_26
  · exact lb_30
theorem sub_56 : ∀ b ∈ bds_56, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_56 : ∀ b ∈ bds_56, canon b.1 g_56 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_56_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x7ef207a6497594d6d188680515f8885738550e654e02e47b654740745b194312a42a073ff2b39768347502f84f2c92f29c2d26d2f21b521ec2f1bf2d18f3014847101470ba470853503d480013c00001 0xcd6f0cd6b0cd670cd6306c6f06c6b06c6706c6306c5f06c5b06c5706c5305a6a08a620ca5a01a5203a4a01a420296f0296b02967029630295f0295b02957029530294f0294b02947029430292d0281205d6f01d6b04d6701d6305c6f01c6b05c6701c6301c5f01c5b01c5701c5305b6f05b6701b5f0bb5701b4f11b4702a6f01a6b05a6705a6301a5f08a5b09a5701a5301a4f11a4b11a4701a4311a3b11a370496b049630495b019530494b019430492b0492a0e926049230486f0486d0486b0486a04867058660486505864048630185f0485d0485b0485a048570b85604855018530184f0484b04847018430483b048370482b0482a0482705826048230281f0281e0281d01d6f01d6d04d6b04d6904d6701d6504d6304d6108c6f08c6d01c6b01c6904c6704c6501c6301c6105c5f01c5b04c5701c5314b6f03b6d01b6b01b6914b6703b6501b6301b6105b5f01b5b05b5701b5301b4f01b4b01b4701b4314a6f0da6d14a670da6505a5f05a5701a4f0ba4701a3f142370296f0296d0596b02967029650295f0595b02957059530194f0994b02947019430193f0693b02937019330292b029270486b0286902863028610485b048530484b018430483b018330281b0481301e7f01e7e01e7d05d7f05d7e08d7d05d6f05d6e01d6b01d6901d6305d6201d6105c7f03c7d01c7b01c7905c7703c7501c7301c7105c6f01c6b05c6701c6301c5f01c5b01c5701c5305b7f1ab7d05b7705b7505b6f05b6701b5f0bb5701b4f1334702a7f05a7e02a7d02a7c05a7b05a7902a7702a7505a7305a7209a711d27002a6f05a6b02a6705a6301a5f09a5b02a5701a5301a4f06a4b02a4701a4302a3b02a370597e0497b04979049730497204971049700496b049630495b019530494b019430292b0292a029260487f0587e0487d1c07c0487b0487a048790487804877058760487505874048730487204871048700486f0586e0486d0886c0486b0486a0486705866048650586404863048620185f0185e0485d0185c0485b0485a048570b856048550e05401853018520184f0184e0484b0384a048470384601843018420483b0483a04837080360281f0281e0281d01d6f01d6d04d6b04d6904d6701d6504d6304d610bc6f0bc6d01c6b01c690bc670bc6501c6301c6105c5f01c5b05c5701c5303b6f03b6d01b6b01b6903b6703b6501b6301b6103b5f01b5b03b5701b5301b4f01b4b06b4a01b4703b4601b4307a6f07a6d07a6707a6505a5f07a5d05a5705a5501a4f07a4701a3f03a370296f0296d0396b02967029650295f0595b02957059530194f0694b02947019430193f0393b02937019330292b029270386b0286902863028610485b048530484b018430383b018330281b0381301e7f01e7e01e7d03d7f0bd7d01d7b01d7903d7703d7501d7301d7105d6f01d6b05d6701d6303c7f03c7e03c7d03c6f03c6e01c6b01c6901c6305c6201c6101c5f01c5b06c5a01c5703c5601c5303b7f07b7d03b7703b7505b6f07b6d05b6705b6501b5f07b5701b4f03b4702a7f02a7d03a7b03a7902a7702a7503a7306a7102a6f05a6b02a6705a6301a5f06a5b02a5701a5301a4f03a4b02a4701a4302a3b02a370397e0397b03979039730397204971049700496b049630495b019530394b019430292b0292a029260387f0387e0487d1a07c0387b0387a038790387803877038760387503874038730387204871048700486f0586e0486d0886c0486b0486a0486705866048650586404863048620185f0185e0485b0485a048570b85601853018520184f0184e0484d0184c0384b0384a0384703846038450384401843018420483b0483a04837078360281f0281e0281d01e7f03e7e01e7b01e7a01e7703e7601e7301e7201d7f01d7b01d7701d7301d6f01d6e01d6d01c7f01c7b01c7a01c7703c7601c7301c6f01c6e01c6d01c5f01c5e01c5b01c5901c5301c5201c5107b7f07b7701b6f01b6d01b6703b6501b5f01b5d01b5707b5501b4f01b4702a7f06a7b02a7706a7301a6f01a6d01a6b03a6901a6702a6501a6301a6101a5f01a5b01a5701a5301a4f01a4b01a4701a4302a3b02a370497b049730196b0396901963019610195b019530194b019430292b0292a029260487f0887e0487b0487a048770587604873048720186f0186e0186d0186c0186b0186a038690386801867018660386503864018630186201861018600185f0185e0185d0185c0185b0185a0185701856048550d05401853018520184f0184e0184d0184c0184b0184a0184701846038450384401843018420483b0483a04837078360281f0281e0281d05d7f0ad7d05d7b01d7905d7705d7505d7301d7105d6f05d6b05d6705d6305c7f03c7d05c7b01c7905c7703c7505c7301c7105c6f07c6d05c6b05c6705c6505c6307c5f06c5b07c5706c5305b7e05b6e0bb5602a7f02a7d02a7b02a7902a7702a7502a7302a7102a6f02a6b02a6702a6302a5f02a5b02a5702a5302a4f02a4b02a4702a430292a0487f0587e0487d0a87c0487b0487a048790487804877058760487505874048730487204871048700486f0586e0486d0886c0486b0486a0486705866048650586404863048620485f0185e0485b0485a048570b85604853018520484f0184e0484b0384a0484703846048430184204835050340281d0ad6f08d6e0bd6b05d6a0bd6705d660ad6308d620ac6f01c6b0bc6701c6301c5b01c5907b6f01b6b07b6701b6307b5f03b5d01b5b01b5907b5703b5501b5301b5101b4f07b4d01b4b01b4707b4501b430ba660296f0296b029670296302957029550294b02947019430193f0293b02937019330ae7f08e7e0be7b05e7a0be7705e760ae7308e720ad7f01d7b0bd7701d7307c7f01c7b07c7701c7307c6f03c6d01c6b01c6907c6703c6501c6301c6101c5f07c5d01c5b01c5707c5501c530bb7601b6e01b5e02a7f02a7b02a7702a7302a6f02a6d02a6b02a6902a6702a6502a6302a6101a5f02a5b02a5701a5301a4f02a4b02a4701a430292a0487f0887e0487b0487a048770587604873048720486f1486e0486d1606c0486b0486a0486904868048670d8660486506064048630486204861048600185f0185e0485d0185c0485b0485a048570c856048550b05401853018520184f0184e0484b0384a0484703846018430184204835040340281d03c7c13c7803c7413c700294c159400484003d8c05d8803d8419d8002a8c11a8002a5c15a5004980049501408c0488805884048800887c058740186c108641105c0385803854048500184c03844128340ad6f01d6b15d6701d6303c6f01c6b03c6701c6301c5f01c5b01c5701c530aa6f11a6b11a670aa6301a5f11a5b11a5701a5301a4f0492a0486f0486b04867048630185f0485b04857018530184f0484d0384b0384a03847038460384503844048350382b0382a0281d16c7c05c7805c7413c700297c11970048700ad6f01d6b1156701d630ac6f08c6e13c6b05c6a13c6705c660ac6308c6201c5f01c5e13c5b10c5a13c5710c5601c5301c5203b6f01b6b03b6701b6301b5f01b5b01b5701b5301b4b01b490296f0296b02967029630195f0295b029570195302947029450293b02937019330ae7f01e7b1367701e7303d7f03d7e03d7b05d7a03d7703d7603d7308d7201d6f01d6e03d6b14d6a03d6703d6601d6301d6203c7f01c7b03c7701c7301c6f01c6b01c6701c6301b5e01b4e02a7f02a7b02a7702a7301a6f02a6b02a6701a6302a5f02a5e02a5d02a5c02a5b02a5902a5702a5502a5303a5202a511225001a4f02a4b02a4701a4303952049500292a0487f0887e0487b0487a048770587604873048720186f0186e0486b0486a048670a06601863018620385f0385e0485d1005c0385b0385a038590385803857038560385503854038530385204851048500184f0184e0484d0184c0384b0384a03847038460384503844018430184204835030340281d01d6f01d6e01d6d05c6f05c6e04c6b04c6904c6704c6304c6204c6104c6005c5f05c5e05c5b05c5904c5705c5305c520fc5105b6f03b6d01b6b05b6703b6501b6305b5f01b5b05b5701b5310b4f01b4b10b4701b4305a6f10a6d05a6705a6505a5f05a5710a4f10a4701a3f10a370296f0596e0596b05969029670596305962099610295f0595b02957059530194f02947099430193f0693b02937019330292b029270586e0486b04869048630486204861048600485b048530284b048430483b018330281b0481301d6f01d6b01d6a01d6703d6601d630fc6f0bc6b0bc670fc6301c5f01c5e01c5b03c5901c5701c5301c5201c5101c5001b6f01b6b01b6a01b6703b6601b6301b5f01b5e01b5d01b4f03b4e01b4b01b4901b4701b4301b4201b4107a6f07a6701a5f01a5d01a5703a5507a4f07a4d07a4707a4501a3f01a370296f0696b02967069630195f0195b039590195701953019510194f01947019430193f0193b01937019330292b029270486b048630185b0385901853018510284b018430183b018330281b018130ad6f01d6b0bd6701d630ac6f08c6e0bc6b05c6a0bc6705c660ac6308c6204c5b04c5a07b6f01b6b07b6701b6301b5f07b5d01b5b01b5707b5501b5307b4f03b4d01b4b01b4907b4703b4501b4301b410ca560da460296f0296b02967029630195f0295b019530194f0194d0193f0293b02937019330ad6f0bd6b05d6a0bd6705d660ad630ac6f0bc6b0bc670ac6304c5b04c5907b6f01b6b07b6701b6307b5f03b5d01b5b07b5703b5501b5307b4f03b4d01b4b07b4703b4501b430ba6601a5e10a4e0296f0296b02967029630295f0295b0295902953029510194f0193f0293b029370193308e7e05e7a05e7608e7201d7a10d7604d6e01d6d03c7e05c7a03c7608c7203c6e03c6d03c6c10c6a03c6910c6803c6603c6503c6410c6203c6113c6001c5e01c5d01c5c01c5a01c5603c5503c5401c5201b6d01b6901b6501b6101b5d01b5501a4e01a3e0196d02959019510294d0294902945029410fd6f08d6e0bd6b05d6a0bd6705d660fd6308d620bc6f01c6b0cc6a0bc670e46601c6304c5f04c5e04c5d0fb6f01b6b0bb6701b6315b5f03b5d01b5b01b5910b5703b5501b5301b5101b4f0cb4d01b4b01b470d34501b430fa6f0ba6710a5f0c25d10a570625501a4f0ca4d0ca470b24501a3f0a2370296f0996b02967099630195f0195d0295701955099530194f0994b099490294701943099410193f0693b02937019330292b029270486b048630285b0285904853028510484b0484901843048410483b018330281b0481301e7e01e7d05d7e08d7d05d6e01d6905d6201d6103c7d01c7903c7501c7105b7e0db7d0db7c05b7a05b7905b7805b7605b7505b7405b7211b7111b7005b6e05b6a05b6605b6201b5e0bb5a0bb5601b5201b4e03b4a03b4601b4205a7605a7405a660ba5612a4604a3e0297d029790297502971029290ad6f01d6b0bd6701d6307c6f01c6b07c6701c6301c5f01c5b01c5701c530bb660aa6f08a6e0ba6b05a6a0ba6705a660aa6308a620ca570ca560da5501a4f01a4e07a4b03a4a07a4703a4601a4301a420296f0296b02967029630195f02957019530194f0294b02947019430292b029290ad6f08d6e0bd6b05d6a0bd6705d660ad6308d620ac6f01c6b0bc6701c630cc5f0dc5e0cc5d07b6f01b6b07b6701b6307b5f03b5d01b5b01b5907b5703b5501b5301b5101b4f07b4d01b4b01b4707b4501b430ba660da5e0296f0296b02967029630295f0295d0194f0294b019430193f0293b029370193305c6f0ac6d05c6b05c6705c6505c6305c5f05c5b05c5705c5305b6f03b6d05b6b05b6703b6505b6305b5f07b5d05b5b05b5705b5505b5307b4f06b4b07b4706b4305a6f05a6e04a6b04a6904a6704a6304a6204a6104a6005a5f05a5e05a5b05a5904a5705a5305a520aa510ba4f0ba4b0ba4a0ba470ba460ba4306a3f07a3b07a3706a330296f0296b029690296702963029610295f0295b02957029530294f0294b02947029430293f0293b02937029330ad6f0bd6b05d6a0bd6705d660ad630ac6f01c6b0bc6701c6307b6f01b6b07b6701b6307b5f03b5d01b5b07b5703b5501b5301b4f07b4d01b4b01b4707b4501b430aa6f0ba6b05a6a0ba6705a660aa6301a5f01a5e04a5b04a5904a5704a5301a5204a5101a5001a4f01a4e0ca4b0da4904a4701a4301a420ca4101a3f07a3b07a3701a330296f0296b02967029630295f0295b029590295702953029510194f0294b02947019430193f0293b02937019330ad6f01d6b12d6701d6303c6f03c6b05c6a03c6703c6603c6301c5f03c5b12c5a03c5703c5601c5303b6f01b6b03b6701b6301b5f01b5b01b5701b530aa6f0da6b0da670aa6301a5f0da5b0da5701a5301a4f01a4e03a4b03a4903a4703a4301a4204a4101a4001a3f01a3e03a3b03a3903a3701a3301a3206a310296f0296b02967029630195f0295b02957019530294f0294e0294b02949029470294303942029410193f0293b029370193303842048400ad6f0cd6b085670ad6307c6f06c6b07c6706c6307c5f06c5b07c5706c530ab6f08b6e11b6b05b6a0db6705b660ab6308b620cb5f01b5e11b5b0735a0db57063560cb5301b5206b4f01b4e07b4b03b4a07b4703b4606b4301b4205266042560324604a3e0296f0296b02967029630295f0295b02957029530294f0294b0294702943029290fd6f0cd6b1b5670cd630fc6f06c6b1946706c630cc5f06c5b1845706c530fb6f173670cb5f1535706b4f0f34702a6f09a6b02a6709a6302a5f09a5b02a5709a5302a4f06a4b02a4706a4302a3b02a370496b049630495b049530494b049430292b0292a029260486f0886e0486b0486a048670586604863048620485f0185e0485b0485a048570905604853018520484f0184e0484b0384a048470384604843018420483b0483a04837020360281f0281e0281dd045fce45bc9457c0453be35fbc35bba357b9353b834fb634bb5347b3343ad25fac25bab257a9253a824fa624ba02479d2439c23f9a23b932378a2338915f8715b86157821538114f7e14b7d1477b1437a13f7813b77137731337212f6d12b6c1276a1236905f6305b5e057580535704f5304b4a047460434503f3f03b3a037340333302f2f02b26027220232001f1f01b1e017010130003f 20 1048575 8 255 11 2047 20 1048575
def cc_56_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xd18ff30abc3d0ef632b9882d02ca7d8a6ce5923222db682721f921766fdb84365b0d85a25c0ad4e444b50916ad3fcbcdb48318a8ad3226e8c8f981c6f06598152883441090800048 0x5e7f079ec5e77079cc5d7a175c8bd6a075883c7f071ec3c77071cc1c6f071ac1c670718c3c5d0a9fc5a7e0a9f42a770a9d45a73169c81a6f1a9acba6a0a99c6a660698c2a5d1a9441a4f0e92c2a470690c29770a5d82975065bc196e165ac596a1659cb9660658c196216574f95c1654459500653c194e0e52c394a0e51c39460650c1942164bc692e164b41842235bc1d6b1759c1d630f1bc1c6b0f19c1c630717c1c5b0715c1c530ad8c2b6206d7c1b5e3ad6ceb5a3ad5ceb5606d4c1b5206d3c1b4e0ed2c3b4a0ed1c3b4606d0c1b420a5bc596b0a59c195f1a56c29570654c194f0e52c29470650c5933164c48e7f079ec5e77079cc5d7a235c8ed6a075883c7f071ec3c77071cc1c6f071ac1c670718c3c5d0a9fc2a7d169ec5a7a0a9dc5a760a9d41a6f1a9ac2a670698c2a5d1a9441a4f0e92c2a470690c297f0a5f8297d065bc196e225ac896a2259ce9660658c196222577d15c2254489500653c194e1a534194c0e52c394a0e51c39460e51439440650c1942164bc592e164b418422206848183b5bc1d6b3b59c1d630f1bc1c6b0f19c1c630717c1c5b0715c1c530a9bc6a6b0a99c6a630697c6a5b0a95c1a530693c3a4b0e9282a470e9181a433e5bc896e465ac596a5e59c59663e58c89620657c195e3a56ce95a3a55ce9560654c19520653c194e0e52c394a0e51c39460650c19423b5bc1d6b3b59c1d63171a88c623b1681c520edbc1b6b0ed9c1b6306d7c1b5b06d5c1b530ed34696ff85ac6967f058c195f3a56c69570654c294dec504193f0e4ec3937064cc1832075ac1d6a071bc1c6b0719c1c630717c1c5d0716c1c590715c1c550714c1c5106dbc1b6b06d8c1b5f06d741b4f06d2c1b4706d0c5a660a5bc596b0a59c69630a57c295d1a56c69590a55c29551a54c69510653c194b0651c1943064fc193b064dc1933075fc1d7b075dc1d73075bc1d6d075ac1d690759c1d650758c1d61071fc1c7d071ec1c77071d41c73071bc1c6d071ac1c690719c1c650718c1c610717c1c5b0715c1c5316dd85b660a9fc5a7b0a9dc6a730a9bc2a6d1a9ac6a690a99c2a651a98c6a610697c1a5b0695c1a530693c1a4b0691c1a4306528187f221f8187d221f0187b061e81877161d81875161d01873061c8186f221b8186d221b0186b061a81869061a01867221981865e4190186306188186106180185f06178185b06168185706158185306148182f1a0b8182b060a818270a098182306088181d075fc1d7d075ec1d79075dc1d75075cc1d71075bc1d6b0759c1d63071fc1c7d071ec1c79071dc1c75071cc1c71071bc1c6d071ac1c67071941c630717c1c5b0715c1c5316df85b6e06d582a7f0a9f45a7b169e42a770a9d45a731a9c42a6f169ac2a671698c1a5f0696c1a570694c1a4f0692c1a470690c194a061fc587e061f4a87c061ec187a061e41878061dc5876061d45874061cc1872061c41870061bc586e061b4886c061ac186a0619c58660619458640618c18620617c185e0616c185a0615c18560614c1852060d76034060bc682e060ac182a0609c28260608c1822060741c6f071b41c6b0719c1c650718c1c5f0716c1c570714c1b6f06dac1b6906d9c1b6306d841b5f06d741b5b06d5c1b5506d4c1b4f06d2c1b4706d0c5a6f169b81a6b069a41a670698c1a62069841a601697c5a5e1696c5a590695c5a5316948aa510693c1a4b069281a47069181a430a5bc296d165ac29670a59459630a57c595b0a55c59530653c194b0651c1943064fc193b064dc19330a4bc692b0a49c6923060e81d6f075ac1d670758c1c6f071ac1c670718c1c5f0716c1c570714cab6f22db93b6b16da8db6716d98ab6322d881b5f06d781b5b06d681b5706d581b5306d4b6266069581a4e068f8296f1a5ac29671a58c195f0656c19570654c194f0652c19470650c293f0a4f4693b1a4e429370a4d469331a4c46925061281d6f075ac1d670758c1c6f071ac1c670718c1c5f0716c1c570714f836fdcd9c1b5f06d5c1b4f06d1c6a6f1a9ac6a671a98c1a5f0696c1a570694c1a4f0692c1a470690c6a3b1a8dc496b1258c195b0654c194b065281946124ac4923061bc886e061ac186a0619c58660618c18620617c185e0616c185a0615c18560614c1852060ec183a060df5036060bc682e060ac182a0609c28260608c18220607c381e06074ad6f2b5acad672b58c7c6f1f1ac7c671f18c7c5f1f16c7c571f14ceb56229b85a6606978ea56069383a460a5bc296b0a59c29630a57c295b0a55c29530a53c294b0a51c29430a4a42925079fc1e7e079f45d7f175f88d7d175bc5d6e075ac1d690758c5d62075845c7f0f1f41c7b071e45c770f1d41c73071c45c6f071ac5c670718c1c5f0716c1c570714c2a7f0a9f45a7b169e42a770a9d45a73269c42a6f169ac2a671698c1a5f2696c2a570694c1a4f1e92c2a470690c495a12528487a121e04872121c0486a12188485a06148384a06108282a120881e7f079ec1e77079cc1d7f175f81d7d075dc1d75075cc1d72075bc1d6b075a81d67075981d63071dc3c76071d41c6f071b81c6b071a81c67071981c63071881c5f071781c5d0a9fc5a7b0a9dc5a73069bc1a6b0699c1a630697c1a5b0695c1a530693c1a4d0692c6a490691c2a450690c1a41065a8195a065284948121e84872061a818620616818520612848480610818400a0a84822079fc1e7b079dc1e73075fc1d7b075e81d771f5d81d73075bc1d6e075b41d67075941d63075881c7f231f81c7b071e81c77171d81c73071c81c67071981c650717c1c5e071742a7f1a9ec2a771a9cc1a6f069ac1a670698c1a5f0696c1a570694c1a4f069341a4b1a9241a470a9141a4306904196a06568194a12520487a121c8186a06188185a06148184a12120184206100282a12088ad6f3b5af25672b58c7c6fc51ac7c672b18c7c5fc116c7c573b14c2a6f269ac2a672698c2a5f2696c2a572694c2a4f1e92c2a472690c495a12528486a12188485a06148384a06108282a120881d6f075ac1d670758c1c6f0719c1c630717c1c5b0715c1c530e9ac3a6a0697c1a5e0696c1a5a0695c1a560694c1a520690c1a420a5bc596b0a59c59630657c195b0655c19530653c194b0651c19430a4bc292d1a4ac69290a49c29251a48c6921079fc1e7b079dc1e73075fc5d7e075f41d77075d41d73075c81d6f075ac1d6a0759c1d660758c1c770f1d81c75071bc1c6e071ac1c6a0719c1c660718c1c620717c1c5e071745b7a16dc81b6a06d881b5a06d481b4ab8d201b4206d001a660a5fc597b0a5dc5973065bc196b0659c19630657c195b0655c19530653c194d0652c69490651c29450650c19410a4f46931061a8185a061284848179fc5e7b179dc5e73175fc5d7b175dc5d731f5bc6d6b1f59c6d63171e85c722f1a81c620f1681c522ed982a7f0a9f82a7d0a9dc2a750a9cc5a720a9bc2a6b2e9a82a670a9982a630a97c2a5b0a95c2a530a9342a410a5dc29760a5d4596f065b8596b165a859672e598596306588595f06578595b0e56859570e558595306548594d3e530594116500292f0a4b8592d261a8785a075bc1d6b0759c1d63071bc1c6b0719c1c630717c1c5b0715c1c5306d58aa6f229b98a6b169a98a6716998aa63229881a5f069781a5b069681a57069581a53069481a4306908296f0a5ac29670a58c195f0656c19570654c194f0652c19470a48c2921061681d6f075ac1d670758c1c6f071ac1c670718c1c5f0716c1c570714cab6f36dacdb672ad8c1b5f06d6c1b5a06d5c1b5606d4c1b4f169a81a5a069081a40068c81a300a5bc296b0a59c29630657c195b0655c19530653c194b06528194706518293b0a484185a061289832079fc1e7b079dc1e73075fc1d7b075dc1d73075bc1d6b0759c1d63171e88c72071a81c62071683c58071481c5006d982a7f0a9ec2a770a9cc1a6f069ac1a670698c1a5f069741a5b069681a57069582a550a9342a4c0a9068240065fc897e065ec197a065dc5976065cc1972065bc196e065ac196a0659c19660658c19620657c195e06574194dac5301941065001935a84d0192f0a4b8192d061a8185a060684818075bc1d6b0759c1d63071bc1c6b0719c1c630717c1c5b0715c1c53069bc1a6b0699c1a630697c1a5b0695c1a530693c1a4e069341a352a5bd196b4659ca9630657c195b0655c19530653c194d0652c194a0651c19461e514192b064a8182a2b5bccd6b3b59cad631f1bc6c6b1f19c6c631f17c6c5b1f15c6c530a9bc2a6b0a99c2a630a97c2a5b0a95c2a530a93c2a4e0a92c2a470a90e82422a5bc896e465ac596a5e59c59662a58c89623257c195e3a56ce95a3a55ce9563254c19521a53c194e1e52c394a1e51c39461a50c19422b5bced6b3b59cad631f1bed46b1f19cac631f17cec5b1f15cec5316da88b623ad681b520ed281b423a958296fb05ac29672a58c295f3a56c29573a54c294f1e52c2947a450c293d9c4c4e85a1e1281c5f0716c1c570714c1b5f06d6c1b5706d4c1b4f06d2c1b4706d0c295f0a56c29570a54c194f0652c19470650c193f064ec1937064ccad6f235b8ad6b175a8ad6717598ad6323588ac6f2b1b81c6b2b1a8ac672b1981c632b1887b6f06dac7b6706d8c7b5f0ed741b5b06d647b570ed541b5306d441b4f1ed341b4b1ed241b471ed141b431ed04296f0a5ac29670a58c295f0a574295b0a56429570a55429530a544194f0a534294b0a52429470a51419430a504193f0a4ec2937064ccac5f2b16cac572b14c7b5f1ed6c7b571ed4c7b4f1ed2c7b471ed0c295f0a56c29570a54c294f0a52c29470a50c293f0a4ec29370a4ccad6f2b5acad672b58c7c6f1f1ac7c671f18c7c5f1f16c7c571f14c2a6f0a9ac2a670a98c2a5f0a96c2a570a94c2a4f0a92c2a470a90c886e16198185e9417240568c150184e0e118282e0a0981e7f079f81e7d0f5fcbd7d075ec1d790f5dc3d75075cc1d71175bc1d6b1759c1d630f1fc3c7e0f1f43c6f0f1b81c6b071a41c63171881c610717c1c5b1b1681c570f1581c530a9fc2a7d0e9ec3a790a9dc2a750e9cc6a710a9bc5a6b0a99c5a630697c6a5b0a95c1a530693c3a4b0a91c1a430e5f8997c0e5d83974165b85966065789956065383946124b83872121c0282a3b5bccd6b3b59ccd633f1bc6c6b8519c6c633317c6c5b3b15c6c530a9bc9a6b0a99c9a630a97c9a5b0a95c9a530a93c6a4b0a91c6a43225b85966065789956065383946124b8282a335bccd6b3359ccd631b1bc6c6b1b19c6c631b17c6c5b1b15c6c530adbc2b670ad7c2b570ad3c2b470a9bc2a6b0a99c2a630a97c2a5b0a95c2a530a93c2a4b0a91c2a430a8ec2a37125ac49631256c49531252c49430a4b829230a488286f221b8286b0a1a828671619828630a188285f06178285b0a168285732158285306148284f06138284b0a12828470e118284306108283b0a0e828370a0d8281f12078281d 18 262143 7 127 11 2047 18 262143
def cc_56_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x8b2218634f7e47f75f8570e516ba5467248652205d08256f615125d4c64c49b2b45b404302b40f213c74839a2d366343283e307212ef182b53a283322374c2172019c7b14f4d0d47b09a3a04a500004a 0x135b45e3681c610b8be1716c2e2b85c53076da06d842daf85b5b0b6ae16d4c5da78bb4b1768e2ed0c14b6e21610b2be1656c2cab859531329e2e52c4ca38b9431327f844ec4c9bdf1330b0a42e1280eb781d6b03ace0758c0e3781c6b038ce0718c0e2f81c5d038b60715c0e2a81c53036d606da80db381b66036c606d7c0daf01b5b036b406d5c0dab01b53036a406d3c0da701b4b0369406d1c0da301b4303684229bc2d3381a5f034ae0693c0d238aa3f1547a2a8dc551a8696f0b2d61659c34b18195f032b60655c0ca98194f032960651c0ca18693f0527a1a4ec349c869370526a1a4cc34988692b0d24e121ac0c318185b030a60612c0c218483b09072060cc0c188481b09026079fc0f3d81e7703ce6075fc0ebd81d7a03aee175d80eb981d6f03adc075b40eb381d6503ac6075880e3f88c7e038f6071e80e3b85c76038e6071c80e3381c66038ca0717c0e2f01c5d116fe16ddc0db781b67036be06d5c0da781b4d0368e2ad14353f85a7b0b4ee1a9cc0d3781a6b034ce0698c0d2f81a5b034ae0694c0d2781a4d034961a9240d2382a450348606904351d86a37092f6125e82cbb0196b032c60656c0ca98194b092920650c0ca08492b09246061bc0c370186b030d40619c0c3301863030c40617c0c2f0185d030b80616c0c2d01857030ac121541c2a01853030a40613c0c270184d030980612c0c2504849090900611c0c2304845ba0880610c0c210184103080120ec241d048371506c120bc34170482b050541209c141304823090441207c240f0481d03cfe0f9f80f3d81e7a03cee0f9d80f3981e7203afe075ec0ebb81d7303ade075b80eb681c7f038f6071e80e3b83c76038e6071bc0e3701c6d038be071780e2d81c59038a6071480e2887b7f0b6ee06dbc0db681b67076ca06d7c0dae81b570f6aa06d3c0da386a7f0b4f6169dc453981a6f034da069ac1d3481a67054ca0698c0d3081a5f034b60695c0d2981a4f034960691c0d2187a3b0d46e125ec24bd05976032d60e5a40cb181961032b60654c0ca581943092561248c0c378186e030da061b00c358186a070d20e1a00c3381866070ca0e1900c3181862030c2061800c2f8185e030ba061700c2d8185a030ae06158242ada054030a6061480c278184e0309a061300c258184a0308e061181c22838440308606108241d8483a0906e1e0d824178982e090560a0a82413828260904612088240f8481e0903a075bc1eb701d6b03ace0758c0eb101c6b038ce0718c0e2f81c5e038b60f1640e2b81c53038a4071440e2801b6f036d606da80db383b66036c606d7c0daf01b5d0369e0ed380da581b490368e06d0c0da101b410f4de1699c0d2f81a5d034ae0e9543d2787a4d0f48e1e9140d1f81a370d2de165ac2cb388963032be065740cad81957052aa0654c34a78994b0d28e2650c0c9f8193b0326e064cc3c9586927090d6121a82c3301863030b60e1640c2981851090960610c0c1d81833090361204c0eb581d6a0bace0759846b188c6f118dc071ac2e3381c63118c41317c262f04c5d116de06dac2db381b63336be0ed740dad81b59216ae0ed540da981b510369e2ed340da581b47b468a06d0c453785a67154be2a974552b8aa550349e2a93455238aa450347e2a8dc44b78596b0b2ce2258c4caf8295d132b6265644cab82955132a6265440ca78994d132962651c4ca2819430327e264ec4c9b81933132562649c24358486a0b0cc1218c242d84859090a6121442425848490308612104241d81833090361204c46b785d6b0bace2358c463785c6b0b8ce2318c5e2fdc45bb68ae2f14c45b785b67156be2ad5c55a78ab47114de169ac2d3388a63134be2696c4d2b89a531349e2692c4d2389a4313476268dc24b58496a0b2cc1256c24a98494b09286124ac24918485f030bc1216c242d04857b20ac1214c0c290484f0309c1212c1c25048470708c1210c0c210483b09074120dc541b0482f1305c120ac1415048270504c1208c24110481f0903c120740eb781d6b03ace0758c463705c66038bc06dbc0db581b67036c606d7c0dad81b57036a606d240da28996f172d62659c5cb18195f032b60655c0ca98c9490528a064fc0c9d8193703266061680f3f81e7e03cfa075fc0ebd81d7703ae6075bc0eb681d6b03ad20759c0eb281d6303ac2071ec0e3d01c79038ee0f1d80e3981c71038ce0f1980e3281c5f038b60715c0e2987b7f0f6fa16ddc3dba83b6f076da0ed9c3db281b5f036ae06d3c0da386a7f0b4f6169dc453983a6f054da0e9ac4d3483a67054ca0e98c1d3081a5f034b60695c0d2981a4f034960691c0d2187a3b0d46e125ec24bd05976092e60e5ac1cb504969092d00e5981cb183961032bc0654c0ca90194b03286124e83c9b0492b09246121fc443f0487b090f4121dc2c3b04873090e40e1bc1c370386d070d80e1ac1c3504869090d00e19c1c33048651d0c80e18c1c3103861070c00613c0c270184b030940611c0c230184303084120ec241d048370f06c120bc4c170482b050541209c141304823090440607c0c0f0181d11afe075ec2ebb81d7311ade235b40eb581d6911ace2f5940eb181d610f8fe1f1f40e3d85c770f8ea071cc3e3783c6d038d6071a43e3383c65038c6071840e2f81c5b038ae0714c2dbb05b66054fe169ec153b88a73054de0a9b4453589a69054ce0a994453188a61034be2696c152b81a530349e1e92c152381a43092f4125a824b401952090fe221f8243d8487a090ee161d8243984872090de221b824368886c090d6121a8243484868090ce2219824328e864090c6121882430848600309e0613824258384a0908e0e1180c21818420905e260b814158282a0504e0a0982411848220303a079fc0f3d81e7703ce60f5fc1ebf03d7b0baf40f5dc1ebb03d7311ae4075bc0eb701d6b03ad40759c0eb301d6303ac4071fc0e3d81c77038e6071bc0e3581c67038c606d780da702a7f134f60a9dc4d3981a6f034d60699c0d3182a5f054ba0e96c1d2c82a57054aa0e94c4d2881a4f034960691c0d218497a032c4121fc443f0487b090f4121dc2c3b04873090e40e17c1c2f0485d1d0b80e16c1c2d03859070b00e15c1c2b03855070a80e14c1c2904851090a00613c0c270184b030940611c0c230184303084120bc4c170282b050540a09c14130482309044060745eb781d6b17ace0758eb23781c6b178ce0718c0e2f81c5b038ae0714ea9b78bb67036be3ad5c0da7d4347134de269ac4d3389a63034be2696c4d2b81a530349e2692c4d2381a4313476268dc24b58496a172cc1258c0caf01953032a41252c0ca18493a1d26c124ac24918486f110dc121ac2435048670b0cc1218c24310184f0309c1212c1c25048470708c0610c0c210483b09074120dc741b0482f1305c120ac1415048270504c1208c24110181f0303c060740eb781d6b03ace0758c0e3181c62038be071780e2d81c5a038ae071580e2981c52036d606d9c0db181b5f036b606d5c0da981b4f0369a1a5bc2cb585967112c60657c0cad81957032a61a53c14a68f94b1f2921a51c14a28f9431f282064fc0c9d8193703266079fc0f3f01e7d0baf4235c81eb55256807ac40f5800e3f81c7b038ee071cc0e3781c6d038d6071a40e3381c65038c6071840e2e81b7b036f406de40dbb83b76036e606dc40db383b66036ca06d740da881b4f0369606d1c0da18697f0b2f6165dc44b98396f052da0e5ac7cb483967052ca0e58c1cb08295d1f2a20653c0ca58194703286064fc0c9d8193703266161e81c350486803084235bc0eb585d6703ac60b18c163101c5f038bc1316c262d08c57098ac0714c0e2908b6f036d616d9c0db181b5f036b606d5c0da998b4f0769a06d2c0da498b470768a06d0c0da08296f0b2d60a59c0caf8995b052ae0654c2ca1859410327e1a4ec149b8193305ade075ac2eb388d63118c423180462904c50116de06dac2db381b63216be06d6c85ab81b530769a0a5bc2cb58596a052ce165980caf8595b052ae2654c4ca08193f0d2760a4dc0c998586a130a4179e82f3c08e7211ce0235fc0ebd85d7703ae6135b4463f81c7b0b8ee071cc1e3681c61038be0716c0e2b81c53054fe0a9f42d3d85a7a054ee169d8153a82a6d054d826986693001a5f134b60a95c0d2981a4f0d4960a91c0d218297f052fc0a5f444b6d016c112c2225800caf8195e112ba0657044ad8895a112ae2e55844aacf154032a6065480ca78194e112960e52844a38394603286065082c978592e0b25a161e80c290881a09030235bc0eb585d6703ac6231bc0e3585c67038c60717c0e2d81c57038a60a9bc153702a6d034be22974452d88a5a114ae2e958452a81a530349e2292c452381a43112de225b42cb58596a0b2ce165985cb28195f092b62655c0ca98194f232964651c0ca18592b0b254220a85eb781d6b17ace0758c7e3781c6b178ce0718c0e2f81c5b038ae0714c153789a6e134d60a99c4d31cd262034be2696c652d02a57134ac0694c0d2786a4b0548e0690c7cb78896e172d6165a85cb3859661f2c6225880caf8195e092b6125684cab84956032a6065480ca78194e232960e528b4a38394603286065082f3d08e7203afe075ec0ebb81d7303ada071fc0e3d81c77038e6071b40e3081c5f038b60715c0e2982a7f0d4f60a9dc353982a6d0d4c20697c0d2d81a57034a60693c0d2701a4d0348e0a9140d2181a42072fe1a5f81cbd8397a072ee165d81cb983972072da1a5b01cb083960032be065780cad8195a032ae065580ca9819520328e0651814a28192f0325c064b44c3d018520bad4235885e3781c6b178ce0718c262ed136f036d62ed9c0db183b5d036a206d3c0da581b4703686265bc5cb5899679c2c60a57660a88194f192962651c0ca18193f96276264dc0c998b86a030840717c0e2d81c57038a606d7c0dad81b57036a606d3c0da581b47036860a57c14ad82957052a60653c0ca58194703286064fc0c9d8193703266075bc0eb581d6703ac6071bc0e3581c67038c60717c0e2d81c57038a62adbc45b70bb6b0b6d42ed9c2db30ab63116c406d3c0da701b4b0369406d1c0da301b43036842e9b85d3301a5e034ac069380d2301a3e052de265ac14b389963032be0656c0cab819530329e0652c0ca3819430527e0a4f44c9d899390526e0a4d44c998993113252264940c2d01c5f038b60715c0e2981b5f036b606d5c0da981b4f0369606d1c0da18ba5f174b62e95c5d2981a4703486068fc0d1d81a37034662657c4cad89957132a60653c0ca58194703286064fc0c9d8193703266264bc4c9589927132461216c24298184b03094061180c218183b03066120ac24118481b09026075bc0eb581d6703ac6071bc0e3581c67038c60717c0e2d81c57038a62edbc5db381b5f036ae06d3c0da389a6f134d62699c4d3181a5f034b60695c0d2981a4f034960691c0d2189a3b1346e125ac24b18195b032b4065580ca581943092561248c0c378886e030d6061a80c3385866030c6061880c278184e03096061280c238184603086061080c1ec903c03076060e80c1bc80360306b1c0d00c178982e03056060a80c138282603046060880c0f8481e0303a075bc0eb581d6703ac6071bc0e3581c67038c60717c0e2d81c57038a622db82db301b5e036ac06d3834b78696b0d2ce1a58c0caf8195b032ae0654c0ca78194b0328e0650c349c8293503094079fc0f3f01e7d03af6075e80ebc81d770baec075cc0eb881d670bacc075940e3f81c7b038ee071cc0e3781c6d038d6071a40e3381c65038c6071840e2f81c5b038ae0714c3dbf85b770f6de1edb43db387b65036be06d5c0da781b470d4fe169ec2d3b88a730d4de0a9b4453589a690d4ce0a994453188a61034be0696c0d2b81a530349e0692c0d2381a430f4761a8dc24bd84973092d6125a424b184961032b60654c0ca70194303284124e83c9b0492b092460e1fc443f0387b070f40e1dc2c3b03873070e40e1bc44370386d110d80e1ac1c3503869070d00e19c443303865170c80e18c1c3103861070c00617c0c2f0185b030b40615c0c2b01853030a40e0ec1c1d038370f06c0e0bc4c170382b050540e09c141303823070440607c0c0f0181d03ade075b41eb583d6903ace075940eb181d61038de071b40e3581c69038ce071940e3181c61038be0716c0e2b81c53036d606da40db381b63036c206d7c0dad81b57036a606d3c0da581b47036861e9bc3d3687a670f4ca1697c2d2b81a4f0348e068fc0d1b8696f052da265ac4cb486967052ca2658c4cb08595f0b2b61655c2ca98194f032960651c0ca18193f03276064dc0c998792b0d24e061ac0c3481863030c21216c24298184b03086060ec0c198481b09026079fc0f3f01e7d03afe175f80ebe81d6f0badc075ac0eb481d6303ac4075840e3f81c7d038f6071e40e3b81c75038e6071c40e3781c6b038ce0718c0e2f81c5b038ae0714c2dbf87b7d0b6ee16dd42db785b67036be06d5c0da781b470b4fe0a9f42d3d85a790b4ee0a9d42d3989a710b4de169ac2d3385a63034be0696c0d2b81a530349e0692c0d2381a430f4761a8dc24bd84979092e6125c424b584963032b60654c0ca70194303284124e83c9b0492b092460e1fc2c3f0387d860f80e1ec1c3d03879070f00e1dc2c3b038750b0e80e1cc1c3903871070e00e1bc2c370386b070d40e19c2c3303863070c40617c0c2f0185b030b40615c0c2b01853030a40e0ec1c1d038370f06c0e0bc4c170382b050540e09c141303823070440607c0c0f0181d11cfc239f4473e05e7a0bcec2f9d45f3a01d7d03aea0f5b80eb688c7e118fa171b82e3685c6c038bc071680e2b01c52036da06da40db081b5d036aa06d340da501b49036900ed180da283b44036821e9b43d3281a5d0f4aa1e9343d228696d132d21a5944cb08294d132920a51444a081869030c2121640c288484a09092121200c2301841090541e09886b788d6e17ad6175a85eb385d6682ac6235880e3781c6b038ce0718c0e2f83c5e038ba06dbc0db581b67036c606d7c0dad81b59036a606d440da781b4d0369606d1c0da281b430f4de1e99c3d2f87a5d0f4ae1e9540d2781a4d0348e1e9140d1f81a370d2de265ac34b3899630d2be0a5744cad899590d2ae0a5544ca9899510329e0652c0ca3819430327e064ec0c9b819330f2561a49c243584863030b6061640c298185103096121240c218184103076060cc241507826090361204e22b781d6b84ace0758c1e3781c6b078ce0718c0e2f81c5b038ae0714c3db787b67036be1ed5c0da783b470d4de269ac353389a63034be2696c352b81a530349e0e92c1d2381a430f4761a8dc24b584963092b60654c0ca70194303284124e83c9b0492b092460e1bc44370386b070d40e19c2c3303863070c40617c0c2f0385b070b40e15e002b01853030a40e0ec1c1d038370f06c0e0bc4c170382b050540e09c141303823070440607c0c0f0181d 20 1048575 8 255 11 2047 19 524287
def cc_56_3 : Nat → List (Nat × Nat) := unpackCursorV4 0x93e638db6388853827617c66172e986cb63668635e48458d57538554d7614b72046d4a3f27b3b9393744532a4a2e04a2aa3628a2026a2020d5d1e22b1855d1602512c340e24a0ae340703e0442c00044 0xbd6f03ad62f59c0eb18fc6f038d62f19c0e3181c5f038b60715c0e298fb6f056d62ed9c15b181b5f056b632d5c0da981b4f05697fcd1c0da182a6f174d62e9a815338ba66194c60697c0d2f02a5d054ae0a9540d2981a520349e1a92c152381a430547e0a8ec151b82a33192de225b85cb58596a172ce1659864b188962052ae0a55814aa8194f0329c3252c1ca50c9470728c0650c0ca10293f19277b84e8649b8c93605266064bc0c970192d1d0de261ac5c3389863030be2616c642b818530309e2612c7423818430507e260ec741b828331305e0a0ac1413898231903e2606c240c8c817130261204416b782d6e05ad6175a816b382d6605ac6235885e3781c6b178ce0718c162f82c5e198ba1adbc0db586b67036c60ad7c1dae81b5b036b20ad5c15aa81b53036a206d3c0da581b47036860a9bc153582a67054c60a97c152e82a5b054ae0a954152981a4f054960a91c0d2181a3f054760a8dc0d198296f052d62e5a814b382966052c60657c0caf0195d0329e0653814a582949032860650814a08193f052760a4dc0c998292f052560a49c14918986f130d62619c4c318285f050b60a164142b82853090a20613c4c258984703086060fc341d86837030660a0bc141582827050460a07c140d8281705026075bc0eb581d6703ac6071bc0e3581c67038c60717c0e2d81c57038a62adbc45b70bb6b0b6d42ed9c2db30ab63116c406d7c0daf01b57036a606d480da781b4e0369606d280da381b460368606d08153782a6a054ce2e9980d2f81a5e034ae069480d2781a4a0348e069180d1f81a3e0347a0a5bc14b582967052c60657c0cad81957032a60653c0ca581947032860a4ec149c82937052660a4c41495829290524e0a4844c3589863030b60614c0c258184313076120e44c19848310505a3a094140d8281303ade075ac0eb381d63038de071ac0e3381c63038be0716c0e2b81c53176de0adac5db382b63036be06d6c0dab81b530369e06d2c0da381b43054de2e9ac15338ba63034be069740d2d81a5a034ae06958152a81a4f034960691c0d2182a3f054760a8dc15198196f112dc065ac0cb5019670b2cc0658c0cb10195f032bc065740ca78194e03296065280ca38194603286065080c9f8193b03274064dfe09b019330325e324b80c968b86f130d62e19c4c318185f030b60615c0c298184f030960611c0c218283f130763a0dc14198982f050560a09c4c118181f03036120640c0b8181303022075bc0eb581d6703ac6071bc0e3581c67038c60717c0e2d81c57038a606dbc45b701b6b036d406d9c2db301b63036c406d7c0daf01b5b036b406d5c0dab01b53036a406d3c0da701b4d054de0a9ac153382a63034be0696c0d2b81a530349e0692c0d2381a430347e068f40d1d81a370546a068cc14b78296b052ce0a58c0caf8195b032ae0654c0ca58194a052920651c0ca30194303282064dc0c9b029350525e0a4ac149382923130de261ac4c3389863030be0616c0c2b818530309e0612c0c23818430307e060ec241c8183703066060c414178282b0504e0a08c140f8281b0502e0a04c0f3f81e7e03cfa075fc2ebf01d7d03ade175b80eb581d6903ac6075880eb081c7f038fa071ec0e3c81c77038ea071cc0e3881c6f038d60719c0e3181c5f038b60715c0e2985b7f0f6fa0adec2dbb85b75056e616dbc15b585b67056c606d7c0dad81b57036a606d3c0da581b47036860a9fc153e85a7b0b4f20a9dc153a85a730d4e20a9bc2d3582a670b4c60697c0d2d81a57034a60693c0d2701a4d0348e0a9140d2181a420547e0a8ec3d1d02a370d46c0a8cc1cbf8597e072fa1a5f01cbd8397a072f20e5e01cbb85976072ea165d01cb983972072e20e5c01cb78596e072d60e5a81cb385966072c60e5880caf8195e032b6065680cab81956032a6065480ca3819460528a0a4fc1c9d8393a0726e1a4d814998192f0325c064b42c3f8587b090f2161dc2c39848710b0de161ac2c3385863030be0616c0c2b818530309e0612c0c23818430507e1e0ec3c1b828330d05e0a0ac1413868230703e0e06c240c83817070260e0447eb781d6bf2ace0758c1e3781c6b078ce0718c0e2f81c5b038ae0714c3db782b6b0f6ce0ad8c0daf82b5b0f6ae06d4c0da782b4b0768e06d0c153786a6b054ce1a98c0d2f86a5b054ae0694c0d2781a4e0549a0a91c152281a43034840a8fc151d87a3a0546e1a8d815198396f0d2dc0e5ac1cb5039670b2cc0e58c1cb10195f032bc0e56c1cad039570d2ac0654c0ca9029470528c0a514149f8393b072740e4dc349b029330325e064b80c968f86f130d78419c4c318185f130b72c15c0c298184f070960e11c0c218283f0f0761e0dc14198682f050560a09c34118381f07036120641c0b8381307022335bc0eb58cd6703ac60b1bc163702c6b0b8d40b19c163302c63118c40717c0e2f02c5b198b40b15c162b01c53038a40edbc0db583b67036c606d7c0dad81b57036a60ad3c15a703b4d054de0a9ac153382a63034be0a96c152b81a530549e0a934152582a470548a0a90c0d1f82a3b0546e068cc14b78296b052ce0a58c0caf8295b052ae0654c0ca78194e0329a064fc0c9f0293b05272064cc0c99029310525e0a4ac1495029270524c0a48c4c378986b130ce2618c0c2f8985b130ae0614c14278284b050920a11c1421848410307e0e0ec1c1b818330505e0a0ac1413828230503e0a06c140b8281303afe075f40ebd81d7903aee075d40eb981d7103ade075ac0eb381d63038fe071f40e3d81c79038ee071d40e3981c71038de071b40e3581c67038ca0718c0e2f81c5b038ae0714c15bf85b7e056fa0adbc2db702b62036be06d680dab81b560369e06d1c153f82a7d054f60a9e4153b82a75054e60a9c4153782a6b054ce0a98c0d2f81a5b034ae0694c0d2781a4d03496069280d2381a460548a0a8ec151b8197f0b2fc065f454be0197b032f4065e40cbc019770b2ec065d42cba01973032e4065c40cb80196f0b2dc065b444b60196b032d40659c2cb3019650b2c80658c0cb10195f032bc0656c0cad01957032ac0654c0ca90194f0329c065340c9e8193b03274064dc149b01935ea268064bc14970192d0b0f6121e42c39848710b0d61618c0c2d81853030960610c14158282303036120640c0981811038de071b40e3581c67038ca0718c0e2f81c5b038ae0714c0db781b6b036d206d9c0db181b61036be06d740dad81b57036aa06d4c0da781b4b0368e06d0c2d3785a6e034d6069a40d3381a63034c4069840d3005a5f0b4bc1696c2d2c81a570b4a616948552881a4f03496069280d2381a4603486068fc0d1b81a33052de0a5ac14b482967052c60a58414af8295b052ae0a54c0ca78194b0328e0650c0c9f8193b03274064dc0c9b01933052560a49c14918586b0b0c61616c2c298184b03086060ec0c198982b130460a06c140981d6f03ad60759c0eb181c6f038d60719c0e3181c5f038b60715c0e298ab6f116dc46dac2db50db670b6cc2ad8c45b101b5f036bc06d6c0dad01b57036ac06d4c0da901b4f0369c06d1c0da181b42054de0a9a81533f5266034be069680d2b81a560349e069380d2381a420347e068f80d1e8296f052d60a59c14b18195f032b60655c0ca98194f03296065280ca381946032860a4ec149c82937052660a4c41495829290524e0a4844c3589863030b60614c0c258184313076120e44c19848310505aa8094140d8281303ade075ac0eb381d63038de071ac0e3381c63038be0716c0e2b81c531f6de0adafb1b382b63036be06d6c0dab81b530369e06d2c0da381b43054de1a9ac153386a63034be0696c0d2b81a530349e069340d2581a4a0348e06918152282a3f054760a8dc15198196f112dc065ac0cb5019670b2cc0658c0cb10195f032bc0656c0cad01957032ac0654c0ca90194f0329c065340c9f8193b03274064dfa09b019330325e0e4b80c968f86f130d77c19c4c318185f030b60615c0c298184f030960611c0c218283f13076a40dc14198682f050560a09c34118181f03036120640c0b81813030222b5bc56b58ad6715ac61b1bc363586c670d8c61b17c362d86c570d8a6229b82d3301a5e194ac069381d230296f052d60a59c14b18295f052b60a55c14a98294f052960a51c14a1829390524a175bc0eb582d6703ac6171bc0e3585c67038c60717c0e2d81c57038a60adbc15b381b5f056ae06d3c15a382a6f054d60a99c153181a5f054b60a95c0d2981a4f054960a91c0d2182a3b0546e0a5bc14b70196b032d40a59c0cb302963052c40657c0caf0895b112b40a55c14ab01953032a40653c0ca70794b072941e51c1ca301943032840a4dc149b0d9350525e0a4b86c968586b0b0c62616c0c298784b030860a0ac14118981b090322604c240881e7f03cfc079f42ebf85d7e11afa175bc2eb701d6b03ad20758c2eb101d610b8fe0f1f40e3d81c790b8ee0f1d40e3981c710b8de071ac2e3381c63038be0716c0e2b81c53056fe0adf415bb82b75056de0ad9c0daf82b570369e0ad1c153f82a7d054f60a9e4153b82a75054e60a9c4153782a6b054ce0a98c0d2f82a5b054ae0694c0d2782a4b0f4940a91c152301a430547a0a8dc151a8297f052fc0a5f414be0297b0b2f40a5e42cbc02977052ec0a5d414ba029730b2e40a5c788b80296f052dc0a5ac2cb502967052cc0a58c2cb10195f032bc0a56c5cad02957052ac0654c0ca90194f0329c0a52c1ca5029470528c0650c0ca1029370526c0a4d42c3d848790b0e6121c42c3585863130b60614c3c2581843050560a08c140d82819050261204456b781d6b17ace0758c3e3781c6b0f8ce0718c0e2f81c5b038ae0714c15b782b67036be0ad5c0da782b47154de2e9ac5d338aa63054ae0a958152a81a4f0f4961e91c0d2182a370546c328d454b78b96b172ce2a58c0caf82957032a60653c3ca58794703286064ec149b829270524a261ac4c318985b030a61e12c0c218982b130462606c4c098ad6f03ad62f59c0eb187c6f038d61f19c0e3181c5f038b60715c0e2982b6f056ce06d7c15ab81b4f0568e0a9bc153582a67054c60697c152d82a57034a60693c152582a47034860a8ec151b8a96f112dc2e5ac2cb50b9670b2cc2a58c44b102957052ac0a5540ca78194e0f2960e5283ca3839460328606508149b829361926a0a4bc14976f12d130d62618c4c2d818530f0960610c14158282313036120644c098481115ade335af82b38ad630f8de1b1ac3e3386c630f8be1b16c3e2b86c53056de0ad9c15af82b570569e0ad1c153782a6b054ce0a98c152f82a5b054ae0a94c152782a4b0f4940a91c152302a430547a0a8dc151a8296f052dc0a5ac2cb502967052cc0a58c44b10295f032bc0a56f70ad02957052ac0a54c0ca90294f0329c0a52c1ca5029470528c0a50c0ca1029370526c0a4d44c3589863130b62614c3c2586843050560a08c140d82819050261204456b78cd6b19ace2b58c363786c6b0d8ce1b18c362f86c5b0d8ae1b14c15b782b6e056d616da815b382b66056c622d8815af81b5e056b632d6815ab82b56056a606d4815a781b4e056960ed2815a382b460568606d08153782a67054be0a95c152782a470547e0a8f8151e8296f052d60a59c14b18295f052b60a55c14a98294f052961a52814a382946052860a4ac149482921130d62618c4c2d898530d0961a10c141d8283905066120c4140d8281315ade235b856b585d6a15ace1759856b188d62158de071ac56350ac67158cc0718c3db781b6b0f6ce06d8c3daf83b5d036b606d643dab83b55036a606d440da787b4d0369606d1c3da281b43052de0a5ac14b382963032be0657414ad82959052ae0655414a9829510329e0a52c14a482947032860a5040c9f8293b0526e064cc56b78ad6b15ace2b58c3e3786c6b0f8ce1b18c3e2f86c5b0f8ae1b14c153782a6b054ce0a98c152f82a5b054ae0a94c152782a4b0548e0a90c151a8896e0b2cc0657b58ab0194e0728c0a4b826b708c6f0b8d61719c463181c591d8aa22dbc2db585b67116c606d641daa8bb4f1d6963ad1c5da18896f0b2d61659c44b18f959052aa2653c74a58994717286264fc7c9d899371f266161a80f3f81e7b03cee079cc0ebf81d7b03aee075cc0eb781d6b03ace0758c0e3f85c7e038f6071e80e3b85c76038e6071c80e3781c6e038d6071a80e3381c66038c6071880dab01b46054fe169ec153b85a73034de069ac0d3381a63034be0696c0d2b81a530349e069340d2586a490348e0a9140d2181a41092e4065a80c378186e030d6061a80c3381866030c6061880c2f8185e030b6061680c2b81856030a6061480c278184e0309a061300c258184a09092121200c23818460908a1e1100c2181842030820610024178682e050560a0a81413828260904612088240e85d6f03ad61759c0eb183c6f078dc0717c0e2f0bc5b178b42f15c5e2b01c53038a40edbc0db583b67036be06d6c0dab81b530369606d2414b78596b052ce1658c0caf8995b052ae0654c14a78294d132962652414a38294513286265040c9f8393b0526e064cc2f3f81e7b0bcee079cc1ebf83d7e07af6175e81ebb83d7607ae6175c80eb781d6e07ad62f5a81eb383d6603ac6075881e3f81c7b078ee071cc0e3781c6b038ce0718c0daf01b4e054fe169ec153b85a73034de269ac153381a63054be0a9741d2d83a59054ae0a9541d2989a510349e0e92c152381a43092e4125a80c378186e090d6121a824338b866030c6061881c2f8385e090bb9c1701c2d8385a070b20e1601c2b83856070aa0e1501c2983852090a2121400c278184e070960e1281c2383846030860610824178982e050560a0a81413828260904612088240e81c6e038d4071980e3101c5e038ba071700e2d01c560f8aa1f1502dbb01b660969c169d80d3a85a74034dc069a80d3301a62034bc069741d2701a4d074980a53434a4829450d282064b434948292503242061a80c15048280bade175ac2eb385d630b8de171ac2e3385c630f8be2f16c3e2b8bc53176be06d785dad8bb5a176ae2ed585da981b521b69e06d383da583b4a0f68e0ed1b29a181b420b4cc2e958251f0296f0b2d60a59c2cb18295f132b60a55c4ca98294f0f2960a51c4ca18293f0527a264ec4c9c829370526a264cc4c988485a0bade175ac2eb385d630b8de171ac2e3385c63178be2f16c5e2b8bc530b6de16d9c5daf8bb57d069f98d1c2d3785a6b0b4ce1698c4d2f89a5b134ae2694c4d2789a4b1348e2690c4d1d89a370b2dc1258c24b10495b092b42e55824a98494b09286124ac24918485f030bc1216c242d04857170ac1214c0c290484f0309c1212c1c25048470708c1210c0c210483b09074120df201b0482f1305c120ac1415048270504c1208c24110481f0903c120742eb785d6b0bace1758c2e3785c6b0b8ce1718c5e2f86c5b178ae1b14c153785a6b0b4d40a99c2d3305a63054be269784d2d82a57134a62e948152786a4b0548e1a90c14b78296e092d6125a82cb3849660b2c60a5885caf8195e172b62e5685cab8b956172a60654834a78194e232960e528b4a3839460d28606508273e8bd7d03ae2175bc0eb585d6703ac60f1f40e3883c6f038d60f19c0e3181c5f038b60715c0e2982a7d0d4e20a9bc2d3582a670b4c60697c352d82a57034a60693c0d2702a4d0548e0a9140d2181a42072fa1a5f01cb883970072de165b81cb58396a072ce165981cb183962032be065781cad8395a072ae1a5580ca9819520528e0a51814a28192f0325c064b42c310985a03ade075b826b584d6a03ace075980eb181d62038de071ac0e3381c63038be071740e2d81c59038ae071540e2981c51036de06dac0db381b63036a606d440da781b4b0368e06d0c14b78596b052ce1658c1ca9839510329e0652c0ca3819430327e064ec0c9b8184a09cfa075f40eb881d6f03ad60759c0eb181c7d038e2071bc0e3581c67038c60717c0e2d81c57038a60a9f4353882a6f0b4d60a99c2d3181a5f034b60695c0d2981a4f0349a0692c0d2501a470348c0a9140cbee017c032e2065c00cb78596e032da225b00cb58196a032ce165980cb285964032c6065880caf8195e032b6065680cab81956032a6065480ca78194e0329a064bc1c970192d0b0c4061680c0d04818 20 1048575 8 255 11 2047 19 524287
def cc_56_4 : Nat → List (Nat × Nat) := unpackCursorV4 0x8831986122819487e7327c72077a4d701796b44d6684c6194f5cb4e5834856b185531853b185231850b184f3184db184c31849b2843a613bf7b35c632f963257a21ef681806f11f610be6107b430007b 0x1c5f01c5b01c5701c5301b5f01b5b01b5701b5301b4f01b4b01b4701b4301a460285f0285b02857028530184f0184b01847018430183f0183b018370183301d6f01d6b01d6701d6301c6f01c6b01c6701c6301c5f01c5b01c5701c5301b5608a6e05a6601a5e01a4e01a460296f0296b02967029630195f0195b01957019530194f0194b019470194302929029259f0289e02401d6f01d6b01d6701d6301c6f01c6b01c6701c6301c5f01c5b01c5701c5301b6f07b6e01b6b01b6a01b6705b6601b6301b6201b5f01b5e01b5b01b5a01b5701b5601b5301b5207a6f07a6701a5f01a5701a4a01a4701a4601a3701a3603a350296f0696b02967069630195f0195b01957019530194f0194b01947019430193f0193d0193b06939019370293501933019310292b029276806b0a8630185b018530184b018430183b0483901833018310281b068130ad6f08d6e0ad6b05d6a0ad6705d660ad6308d6201c6f01c6b01c6701c6301b6f01b6b01b6701b6301b5f01b5d01b5b01b5901b5701b5501b5301b5101b4f01b4d01b4b01b4701b4501b430296f0296b02967029630295f0295d0295b02959029570295502953029510194f0194b01947019430193f0193b01937019330ad6f01d6b0ad6701d6303c6f01c6b03c6701c6301c5f01c5b01c5701c5301b4e08a6e05a6601a5e9b25603a460296f0296b02967029630195f0295b02957019530194f0294b0294701943029290292501d6f01d6b01d6701d6301c6f01c6b01c6701c6301c5f01c5b01c5701c5303b6f03b6e01b6b01b6a01b6701b6601b6301b6201b5f01b5e01b5b01b5a01b5701b5601b5301b5201b4f01b4e01b4701b4301b4205a6f05a6701a5f01a5701a4f01a4701a3f01a3d01a3701a350296f0596b02967059630195f0195b01957019530194f0194b01947019430293f0293d1393b11939029370293513933119310292b029270586b058630185b018530184b018431383b0483913833048310281b1981301e7f01e7e01e7d01d7f05d7e01d7d01d6f05d6e01d6b01d6901d6301d6201d6103c7f03c7e03c7d03c7c03c7b05c7a03c7905c7803c7703c7603c7503c7403c7305c7203c719947003c6f03c6e03c6b05c6a03c6703c6603c6305c6201c5f01c5e01c5b01c5a01c5701c5601c5301c5201b7f01b7d01b7b01b7901b7701b7501b7301b7101b6f01b6b01b6701b6301b5f01b5b01b5701b5305a7f07a7d05a7705a7505a6f05a6701a5f01a5701a4f01a4e01a4d01a3f01a3e01a320297f0297d0597b05979029770297505973169710296f0596b02967059630195f0195b01957019530294f0294d0394b03949029470294503943179410193f0193b01937019330292b029270587b0487905873048710586b058630185b018530384b0384903843048410183b018330281b1301301d6f01d6b01d6701d6301c6f01c6b01c6701c6301c5f01c5b01c5701c5302b6f02b6701b5f01b5701b4f01b4702a6f02a6b02a6702a6301a5f01a5b01a5a01a5701a5601a5301a4f01a4b01a4701a4301a3b02a370a96f0896e0b96b0596a0b967059660a963089620195f0195e0195b0195a019570195601953019520194f0194e0194b0194a019470194601943019420193b0193a02937029360292f0292e1092d0986b098630185b018530184b018430282b028230981b04819098130481101d6f01d6b01d6701d6301c6f01c6b01c6701c6301c5f01c5d01c5b01c5701c5501c530ab6f08b6e0bb6b05b6a0bb6705b660ab6308b6201b5701b5603b5501b4f01b4e01b4701b4301b4207a6f07a6701a5f01a5d01a5707a5501a4f01a4701a3f01a3d01a3701a350296f0b96b029670a9630195f0195b01957019530194f0194b01947019430293f0293d1293b97139029370293510933801310292b029270b86b0a8630185b018530184b018431283b0483910833048310281b148130ad6f08d6e0bd6b05d6a0bd6705d660ad6308d6201c6f01c6b01c6a01c6710c6601c6301c5f10c5e01c5d01b6f01b6b01b6701b6301b5f01b5d01b5b01b5901b5701b5501b5301b5101b4f01b4b01b4701b4302a6f02a6701a5f01a5d01a5701a5501a4f01a4701a3f01a370296f0296b02967029630195f0195d0295b02959019570195501953019510194f0194b029490194701943019410193f0193b01937019330292b029270986b098630985b0485909853048510184b018430183b018330281b028130ad6f01d6b17d6701d6303c6f01c6b03c6701c6301c5f01c5b01c5701c5302b6f02b6701b5f02b5701b4f02b4702a6f02a6b02a6702a6301a5f02a5b02a5701a5301a4f02a4b03a4a02a4702a4601a4302a3b02a3a02a3702a360a96f0896e1196b0596a17967059660a963089620195f0195e1195b8015a159579515601953019520194f0194e0294701943019420193b0193a02937019360292f0292e0392d0986b098630985b018530384b018430282b0282902823120210981b0481909813048110ad6f01d6b9856701d6303c6f03c6e03c6b05c6a03c6703c6603c6308c6201c5f01c5e03c5b9645a03c5703c5601c5301c5203b6f01b6b03b6701b6301b5f01b5b01b5701b5307a6f07a6701a5f07a5701a4f01a4e01a4d01a3f01a3e01a320296f8816b029670a9630195f7f15b02957019530294f0294d0394b03949029470294503943941410193f0393b02937019330292b029276606b0a8635405b018530384b0384903843048410383b018330281b0f01301c5f01c5b01c5701c5301b5f01b5b01b5701b5301b4f01b4b01b4701b430295f0295b02957029530194f0194b01947019430193f0193b019370193301c5f01c5b01c5701c5301b5f01b5b01b5701b5301b4f01b4b01b4701b430295f0295b02957029530194f0194b01947019430193f0193b019370193301c5f01c5b01c5701c5301b5f01b5b01b5701b5301b4f01b4b01b4701b430295f0295b02957029530194f0194b01947019430193f0193b019370193301c5f01c5b01c5701c5301b5f01b5b01b5701b5301b4f01b4b01b4701b430295f0295b02957029530194f0194b01947019430193f0193b019370193301c5f01c5b01c5701c5301b5f01b5b01b5701b5301b4f01b4b01b4701b430295f0295b02957029530194f0194b01947019430193f0193b019370193301c5f01c5b01c5701c5301b5f01b5b01b5701b5301b4f01b4b01b4701b430295f0295b02957029530194f0194b01947019430193f0193b019370193301c5f01c5b01c5701c5301b5f01b5b01b5701b5301b4f01b4b01b4701b430295f0295b02957029530194f0194b01947019430193f0193b019370193301c5f01c5b01c5701c5301b5f01b5b01b5701b5301b4f01b4b01b4701b430285f0285b02857028530184f0184b01847018430183f0183b018370183301d6f01d6b01d6701d6301c6f01c6b01c6701c6301c5f01c5b01c5701c5301b4608a6e9226c05a669126401a5e9025c01a568f25401a4e0296f0296b02967029630195f0195b01957019530194f0194b0194701943029298e128029258d1248c0288b02402d6f08d6e02d6d08c6f05c6b05c6708c6302c5f02c5d02c5b01c5902c570cc5502c5301c5106b6f05b6b05b6706b6302b5f02b5d02b5b01b5902b5703b5502b5301b5106b4f06b4b06b4706b4302a6f02a6b02a6702a6302a5f02a5d02a5b02a5702a5502a5302a4f02a4b02a4702a4302a3f02a3b02a3702a330296b0596a02969029670296602963029610295702956029550294f0294b02947029430293f0293b02937029330292f0292b02927029230886f0586b05867088630285f0285b048590285702853028510984f0984b09847098430683f0683b06837068330282f0282b02827028230281f0281b028170281305e7f01e7b05e7701e7303d7f03d7e03d7b05d7a03d7703d7603d7305d7201d6f01d6e03d6b0bd6a03d6703d6601d6301d6203c7f01c7b03c7701c7301c6f01c6b01c6701c6302b7f02b7701b6f02b6701b5f01b5e01b5d01b4f01b4e01b4202a7f02a7e02a7d02a7702a7502a7305a7201a6f02a6b0ba6a02a6702a6601a6302a5f02a5d02a5b02a5902a5702a5502a5302a5101a4f02a4b02a4701a4302a3b02a370297702976029750196f0196e0596b0596a059670b96601963019620395f0395e0595d0f95c0395b0395a039590395803957039560395503954039530395205951059500194f0194e0394b0394a039470394601943019420293b0293a02937029360292f0292e0592d0587b058730986b018630385b0385903853048510384b018430282b028230581b04819058130481105d6f05d6b05d6705d6305c6f05c6b05c6705c630bc5f06c5b0bc5706c5305b6f02b6b05b6702b630bb5f02b5b0bb5702b5306b4f02b4b8834702b4302a6f05a6e02a6d02a6702a6505a6305a6202a5f0ba5b0ba5a02a570ba560ba5302a4f06a4b02a4706a4302a3f02a3b02a3702a330296702966029650595f0195e0595b0595a059570b95605953019520594f0194e0594b0394a059470394605943019420293f0593b0593a059370f936029330592f0892e0592d0586f0586b05867058630b85f0985b0b857098530684f0984b3e047068430283f0983b2c037028330982f0282b02827098230581f0581b0481905817058130481102d6f02d6e05d6d02c6f0bc6d02c6b01c6902c6702c6502c6301c6105c5f05c5b05c5705c5302b6f03b6d02b6b01b6902b6702b6502b6301b6105b5f05b5b05b5705b5306b4f06b4b06b4706b4302a6f02a6d02a6b02a6702a6502a6302a5f02a5b02a5702a5302a4f02a4b02a4702a4302a3f02a3b02a3702a330296f0296e0296d0295f0295e0295b029590295305952029510294f0294b0b94a0294702946029430293f0293b02937029330292f0292b02927029230286f0286b028690286702863048610585f0585b05857058530984f0984b09847098430683f0683b06837068330282f0282b02827028230281f0281b028170281301e7f03e7e01e7b01e7a01e7703e7601e7301e7201d7f01d7b01d7701d7301d6f01d6e01d6d01c7f01c7b01c7a01c7703c7601c7301c6f01c6e01c6d01c5f01c5e01c5b01c5901c5301c5201c5107b7f02b7b05b7702b7301b6f01b6d01b6b01b6703b6501b6301b5f01b5d01b5b01b5707b5501b5301b4f01b4b01b4701b4302a7f02a7d05a7b05a7a02a7705a7602a7501a6f01a6d01a6b03a6901a6702a6501a6301a6101a5f01a5b01a5701a5301a4f01a4b01a4701a4302a3f02a3b02a3702a330297f0297e0297d0196f0196e0196d0196c0196b0196a039690396801967019660396503964019630196201961019600195f0195e0195d0195c0195b0195a0195701956089558415401953019520194f0194e0194d0194c0194b0194a0194701946039450394401943019420293f0793b0793a0793707936029330592f0592e0592d0887f0587b05877088730186f0186b038690186701863018610185f0185b01857018530184f0184b01847018430283f0783b07837028330682f0282b02827068230881f0881b0481908817088130481101d6f03d6e01d6b01d6701d6301d6202c6f01c6b01c6701c6301c5f01c5e01c5b03c5901c5701c5301c5201c5101c5001b6f01b6b01b6a01b6703b6601b6301b5f01b5e01b5d01b4f03b4e01b4b01b4901b4701b4301b4201b4107a6f02a6b05a6702a6301a5f01a5d01a5b01a5703a5501a5307a4f07a4d02a4b07a4707a4502a4301a3f01a3b01a3701a330296f0596b0596a0296705966019630195f0195b039590195701953019510194f0594b01947019430193f0193b01937019330292f0292b02927029230886f0586b05867088630185f0185b01857018530e84f0984b0e847098430183f0183b01837018330282f0782b07827028230681f0281b028170681302d6f02d6e01d6b01d6a05d6701d6608d6302d6208c6f08c6e01c6b05c6701c6308c6208c5f08c5e08c5d08b6f01b6b05b6701b6315b5f03b5d01b5b01b5910b5703b5501b5301b5101b4f0bb4d01b4b01b478434501b4308a6f02a6b05a6702a630aa5f0aa5d02a5b0aa570aa5502a5301a4f0aa4d02a4b0aa470aa4501a4301a3f02a3b0aa3701a330296f0596b0596a0296705966089630195f0195d0595b0595902957019550b953059510194f0b94b0c94902947019430b9410193f0693b02937019330292f0292b02927029230886f0586b05867088630e85f0985b048590e85709853048510184f0b84d0984b0b8474f045018430183f0983b0e837018330282f0982b0a827028230981f0281b028170981308d6f05d6b05d6708d6308c6f05c6b05c6706c630bc5f06c5b8545706c5308b6f02b6b05b6702b630ab5f02b5b0ab5702b5306b4f02b4b0ab4702b4302a6f02a6d05a6b05a6a02a6705a6602a6502a5f0ca5b02a570ba5302a4f06a4b02a4706a4302a3f02a3b02a3702a330296f0296e0296d0895f0195e0895b0895a089578315608953019520694f0194e0894b0394a089470394606943019420293f0893b0893a089370a936029330592f0592e0592d0886f0586b05867088630b85f0985b4e057098530684f0984b3c047068430283f0983b0a837028330982f0282b02827098230881f0881b0481908817088130481101d6f01d6b01d6701d6301c6f08c6e01c6b01c6a01c6705c6601c6301c6201c5f01c5e01c5d01b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4d01b4b01b4901b4701b4501b4301b4102a6f02a6b02a6702a6301a5f01a5b01a5701a5301a4f01a4d01a4b01a4702a4501a4301a3f01a3b01a3701a330296f0296b02967029630195b0195a02959019570195601953019510194701946029450193f0193b01937019330292f0292b02927029230986f0986b09867098630185f0185b01857018530184f0184b048490184701843018410183f0183b01837018330282f0282b02827028230281f0281b028170281301d6f01d6b01d6701d6301c6f01c6b01c6701c6301c5f01c5b01c5701c5302b6f02b6701b5f01b5701b4f01b4702a6f02a6b02a6702a6301a5f01a5b01a5701a5301a4f01a4b01a4701a4302a3b02a370a96f0896e0b96b0596a0b967059660a963089620195701956109550194f0194e0194701943019420193b0193a01937019360292f0292e1092d0986b098630185b018530184b018430282b028230981b04819098130481101e7f01e7b01e7701e7303d7f03d7e03d7b05d7a03d7703d7603d7308d7201d6f01d6e01d6b01d6a01d6701d6601d6301d6201c7f01c7b01c7701c7301c6f01c6b01c6701c6302b7f02b7701b6f01b6701b5f01b5e01b5d01b4f01b4e01b4202a7f02a7b0ba7a02a7702a7602a7301a6f01a6e01a6d01a6702a6501a6301a6202a5f02a5d02a5b02a5902a5702a5502a5302a5101a4f01a4b01a4701a4302a3b02a370a97f0897e0b97b0597a0b977059760a973089720196701966029650395f0395e0c95d0c95c0395b0395a03959039580395703956039550395403953039520c951801500194f0194e0194b0194a019470194601943019420293b0293a02937029360192f0192e0192d0987b098730186b018630385b0385903853048510184b018430282b028230981b048190981304811 20 1048575 8 255 11 2047 20 1048575
def cc_56_5 : Nat → List (Nat × Nat) := unpackCursorV4 0x923638d44f8716380a677a565744616e1636924f62f635ca6557555514614c64e4c5014c4014774d3f1863a74a3862133a4c303372e3202994a26435243211d0731587810c4c0ba52066540184e00018 0x1d6f01d6e01d6d08c6f01c6b05c6701c6303c5f03c5d01c5b01c5903c57bf45501c5301c5101b6b05b6a01b6903b6703b6601b6301b6103b5703b5603b5501b4f01b4b01b4701b4307a6f07a6d05a6b05a6707a6507a6303a5f03a5d03a5b03a5707a5503a5301a4f07a4b07a4701a4301a3f03a3b03a3701a330696f0596b05967089630395f0295d0395b0f959039570295503953039510194f0f94b06947019430193f0393b03937019330692f0792b06927079230886f0586b05867088630385f0385b048590385703853038510184f5604b51047018430183f0383b03837018330782f0782b07827078230f81f0681b068170f81301d6f01d6b01d6701d6301c6f01c6d01c6b01c6701c6501c6301c5f01c5b01c5701c5305b6f05b6b03b6a03b6703b6601b5f01b5e01b5b01b5a01b5701b5601b5301b5201b4f01b4e01b4701b4301b4205a6f05a6a05a6705a6601a5f01a5701a4f01a4e01a4701a4201a3f01a3e01a3d0296f0596b02967059630195f0195b01957019530194f0194b01947019430293f0293d0693b06939029370293506933069310292b029270586b058630185b018530184b018430d83b0483913833048310281b0681301d6f01d6b01d6701d6301c6f05c6e01c6d01c6701c6501c6301c6201c5f01c5b01c5a01c5701c5601c5301b6703b6601b6501b5f01b5e01b5b01b5a01b5701b5601b5301b5201b4f01b4e01b4d05a6f05a6b05a6705a6301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3d01a3b01a37bd23501a330596f0596b05967059630195f0195b01957019530194f0194b01947019430193f0193d0193b06939019370293501933019310692f0692b06927069230586f0586b05867058630185f0185b01857018530184f0184b01847018430183f0183b048390183701833018310782f3102b2d027078230681f0681b068170681305d6f01d6b05d6701d6303c6f01c6b03c6701c6301c5f01c5b01c5701c5305b6f02b6b05b6702b6301b5f02b5b07b5701b5301b4f02b4b03b4701b4302a6f05a6b05a6a02a6705a6605a6301a5f06a5b02a5701a5301a4f03a4b03a4a02a4703a4601a4302a3f02a3b02a3702a330296f0296e0196b0196a059670196605963029620195f0195e0b95b0b95a0b9570b95601953019520194f0194e0394b0394a039470394601943019420293f0793b0793a0793707936029330392f0392e0392d0586f0586b05867058630185f0985b0b857018530184f0384b03847018430283f0783b07837028330682f0282b02827068231181f0981b0481918817098130481101d6f01d6e01d6d03c6f0bc6d01c6b01c6903c6703c6501c6301c6105c5f01c5b05c5701c5303b6f03b6e03b6d03b5f03b5e01b5b01b5901b5305b5201b5101b4f01b4b0bb4a01b4703b4601b4303a6f07a6d03a6b03a6703a6503a6305a5f07a5d05a5b05a5705a5505a5301a4f07a4b07a4701a4301a3f03a3b03a3701a330396f0296d0396b03969039670296503963bb1610595f0595b05957059530194f0b94b06947019430193f0393b03937019330692f0792b06927079230386f0386b038690386703863048610585f0585b05857058530184f0b84b0b847018430183f0383b03837018330782f0782b07827078232101f0681b068171901301d6f01d6b01d6701d6301c6f01c6d01c6b01c6a01c6705c6601c6501c5f01c5b01c5701c5301b6f03b6e01b6d01b5f01b5e01b5b01b5a01b5701b5601b5301b5201b4f01b4e01b4d08a6f05a6b05a6707a6301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3d01a3b01a370aa3501a330696f0596b05967069630195f0195b01957019530194f0194b01947019430193f0193d0193b06939019370293501933019310692f0692b06927069230886f0586b05867088630185f0185b01857018530184f0184b01847018430183f0183b048390183701833018310782f0a82b0a827078230681f0681b068170681301d6f01d6b01d6701d6301c6f08c6e01c6b01c6a01c6705c6601c6301c6201c5f01c5e01c5d01b6f01b6b01b6701b6301b5b01b5a01b5901b5701b5601b5301b5101b4701b4601b4507a6f07a6b07a6707a6301a5f01a5d01a5b01a5707a5501a5301a4f01a4d01a4b01a4707a4501a4301a3f01a3b01a3701a330696f0b96b069670b9630195f0195b01957019530194f0194d0194b0c949019470294501943019410193f0193b01937019330692f0792b06927079230b86f0b86b0b8670b8630185f0185b01857018530184f0184b048490184701843018410183f0183b01837018330782f0782b07827078230c81f0681b068170c81301d6f01d6b01d6701d6301c6f01c6b01c6701c6301c5f01c5d01c5b01c5701c5501c530ab6f08b6e0bb6b05b6a0bb6705b660ab6308b6201b5f01b5b01b5a01b5701b5601b4f01b4e01b4701b4301b4207a6f07a6701a5f01a5a01a5701a5601a4f01a4e01a4701a4201a3f01a3e01a3d0296f0696b02967069630195f0195b01957019530194f0194b01947019430293f0293d0693b06939029370293506933069310292b029270b86b0a8630185b018530184b018430d83b0483910833048310281b0681301d6f01d6b01d6701d6301c6f01c6b01c6a01c670bc6601c6301c5f01c5e01c5d01c5701c5501c5301c5201b6f08b6e01b6b01b6a01b6705b6601b6301b6201b5701b5601b5501b4f01b4e01b4dae26f07a6b0ba6707a6301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3d01a3b01a37b723501a330696f0696b06967069630195f0195b01957019530194f0194b01947019430193f0193d0193b06939019370293501933019310692f0692b06927069230e86f0b86b0b8675c0630185f0185b01857018530184f0184b01847018430183f0183b048390183701833018310782f3002b0e827078230681f0681b068170681301d6f03d6e01d6b01d6a01d6703d6601d6301d6201c6f01c6b01c6701c6301c5f01c5e01c5d01b6f01b6b01b6a01b6703b6601b6301b5f01b5e01b5d01b4f01b4e01b4b01b4901b4301b4201b4107a6f07a6b07a6707a6301a5f01a5d01a5b01a5703a5501a5301a4f01a4d01a4b01a4707a4501a4301a3f01a3b01a3701a330696f0b96b06967851630195f0195d0195b03959019570295501953019510194f0194b01947019430193f0193b01937019330692f0792b06927079230e86f0b86b0b8675b0630185f0185b038590185701853018510184f0184b01847018430183f0183b01837018330782f0782b07827078230e81f0681b068171801301d6f01d6b01d6701d6301c6f01c6b01c6701c6301c5f01c5d01c5b01c5701c5501c530ab6f08b6e0bb6b05b6a0bb6705b660ab6308b6201b5f01b5e01b5701b5301b5201b4f01b4e01b4701b4301b4207a6f07a6a07a670ba6601a5f01a5e01a5701a5201a4f01a4e01a4701a4201a3f01a3e01a3d0296f0696b02967069630195f0195b01957019530194f0194b01947019430293f0293d0693b06939029370293506933069310692d0292b02927069250b86b0a8630185b018530184b018430d83b048390e833048310782d0e8250281b0681301d6f01d6b01d6701d6301c6f01c6b01c6701c6301c5f01c5d01c5b01c5a01c5701c5601c5501b6f08b6e01b6b01b6a01b6705b6601b6301b6201b5f01b5e01b5d01b4f01b4e01b4d0ba6f07a6b0ba6707a6301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3d01a3b01a37b423501a330696f0696b06967069630195f0195b01957019530194f0194b01947019430193f0193d0193b06939019370293501933019310692f0692b06927069230b86f0b86b0b8670b8630185f0185b01857018530184f0184b01847018430183f0183b048390183701833018310782f0e82b0e827078230681f0681b068170681301d6f01d6d05d6701d6508d6308c6f08c6e08c6d08c5f08c5e01c5b05c5701c5308c5207b6f03b6d01b6b01b6907b6703b6501b6301b6107b5f01b5b05b5701b5301b4f01b4b01b4701b430aa6f05a6d05a6705a6508a5f05a5a05a5705a5601a4f0aa4d0aa470aa4501a3f07a370296f0296d0f96b0f96902967029650f9630f9610295f0595b02957089530194f0b94b02947019430193f0793b02937019330292b029271086b0486912863048610585b088530b84b018430783b018330281b0f813049700497801d6f01d6d01d6701d6501d6301c6f01c6d01c6b01c6901c6701c6501c6301c6101c5f01c5b01c5701c5301b6f01b6d01b6b01b6901b6701b6501b6301b6101b5f01b5b01b5701b5301b4f01b4b01b4701b4301a6f01a6d05a6705a6501a5f05a5701a4f01a4701a3f01a370296f0296d0696b06969029670296506963069610295f0595b02957069530194f0194b01947019430193f0193b01937019330292b02927b106b04869b0063048610585b088530184b018430183b018330281b0681301d7f01d7b01d7701d7301d6f01d6d01d6b01d6901d6701d6501d6301d6101c7f01c7d01c7b01c7a01c7705c7601c7507c7401c7301c6f01c6d01c6b01c6a01c6901c6801c6707c6601c6503c6401c6301c6101c5f01c5e01c5d01c5701c5501c5301c5201b7f08b7e01b7d08b7c01b7b01b7a01b7705b7601b7505b7401b7301b7201b6f08b6e01b6d08b6c01b6b01b6a01b6901b6801b6708b6601b65af36401b6301b6201b6101b6001b5701b5601b5501b4f01b4e01b4d05a7a05a7705a7605a6705a6605a6501a5f01a5701a4f01a4701a3f01a3d01a3707a350297f0597b02977069730296f0296d0696b06969029670296506963069610195f0195b01957019530194f0194b01947019430193f0193d0193b06939019370293501933019310292b029270587b088730886b0486908863048610185b018530184b018430183b0483901833018310281b0681308c6f05c6b05c6708c6308c5f08c5d08c5b01c5908c57b245508c5301c5107b6f07b6d05b6b05b6707b6508b6307b5f03b5d08b5b01b5907b5703b5508b5301b5107b4fae34b07b470bb4305a6a05a6705a6605a5705a5605a550aa4f0aa4707a3f07a370296f0596b02967089630295f0295d0895b0f959029570295508953089510294f0f94b029470b9430293f0793b029370f9330292b029270586b088630885b0485908853048515504b0b8430783b380330281b0f81305d6f05d6b05d6705d6305c6f05c6b05c6705c6307c5f07c5b07c5707c5305b6e0bb5605a6601a5e0ba5601a4e03a460296f0296b02967029630295f0295b02957029530294f0294b0294702943029290292505c6f0ac6d05c6b01c6905c6705c6505c6301c6105c5f05c5b05c5705c5305b6f03b6d05b6b01b6905b6703b6505b6301b6105b5f07b5d05b5b05b5705b5505b5307b4f0bb4b07b470bb4305a6f05a6e08a6d05a5f05a5e05a520aa4f0aa4a0aa470ba4607a3f07a370296f0296d0596b059690296702965059630a9610295f0595b02957059530294f0b94b029470b9430293f0793b02937761330292b029270586b0486905863048610585b058530b84b0b8430783b370330281b1701308d6f08d6e01d6b01d6a05d6701d6608d6308d6208c6f08c6e01c6b05c6701c6308c6207b6f01b6b05b6701b6307b5f03b5d01b5b01b5907b5703b5501b5301b5101b4f07b4d01b4b01b4707b4501b4305a660296f0296b02967029630295f0295d0295b02959029570295502953029510194f0294d0294b0294702945019430193f0293b029370193308d6f05d6b05d6708d6307c6f05c6b05c6707c6307c5f07c5b07c5707c5305b6608a6e01a5eaa25601a4e03a460296f0296b02967029630295f0295b02957029530294f0294b0294702943029290292501d6f01d6b01d6701d6301c6f08c6e01c6b01c6a01c6705c6601c6301c6201b6f01b6b01b6701b6301b5f01b5d01b5b01b5701b5501b5301b4f01b4d01b4b01b4901b4701b4501b4301b410aa6f0aa6701a5a01a5701a5601a4701a46a724501a3f01a370296f0b96b029670a9630195f0195b01957019530194f0194d0194b0c949019470294501943019410193f0193b01937019330292b029270b86b0a8630185b018530184b0484901843018410183b018330281b0c8130ad6f08d6e0ad6b05d6a0ad6705d660ad6308d6201c6f01c6b01c6701c6301b6f01b6b01b6701b6301b5f01b5d01b5b01b5901b5701b5501b5301b5101b4f01b4d01b4b01b4701b4501b430aa6601a5e01a4e0296f0296b02967029630295f0295d0295b02959029570295502953029510194f0194b01947019430193f0193b01937019330ad6f01d6b0ad6701d6307c6f01c6b07c6701c6301c5f01c5b01c5701c530ab6601b5e08a6e05a66a725601a4e03a460296f0296b02967029630195f0295b02957019530194f0294b029470194302929029250ae7f0ae7e0be7b0be7a0be770be760ae730ae720ad7f01d7b0bd7701d7307c7f01c7b07c7701c7307c6f07c6d01c6b01c6907c6707c6501c6301c6101c5f07c5d01c5b01c5707c5501c5302b7f02b7a02b770bb7601b6f01b6e01b6d01b5f01b5e01b5201b4f02b4702a7f02a7b02a7702a7302a6f02a6e02a6d02a6c02a6702a6502a630da6202a616f26001a5f02a5b02a5701a5301a4f02a4b02a4701a4302a3b02a370a97f0897e0b97b0597a0b977059760a9730897202967029660296502964029570295602955029540194f0194e0794b0394a0794703946019430194202937029360c9350c9340292f0292e0d92d0987b098730986b0986909863098610985b018530784b018430283d0d8350282b028230981b0481909813048110ae7f0ae7e0be7b0be7a0be770be760ae730ae720ad7f01d7b0bd7701d7307c7f01c7b07c7701c7307c6f07c6d01c6b01c6907c6707c6501c6301c6101c5f07c5d01c5b01c5707c5501c5302b7f02b7a02b770bb7601b6f01b6e01b6d01b5f01b5e01b5201b4f02b4702a7f02a7b02a7702a7302a6f02a6d02a6b0da6a02a696f26802a6702a6602a6502a6401a5f02a5b0ca5a02a5702a5601a5301a4f02a4b02a4701a4302a3b02a3a02a3702a360a97f0897e0b97b0597a0b977059760a973089720296f0296e0296d0296c0195f0195e0295701953019520194f0194e0794b0394a079470394601943019420193b0193a02937019360292f0292e0d92d0987b098730986b0986909863098610985b018530784b018430283d0e8350282b028230981b0481909813048110ad6f01d6b0bd6701d6307c6f01c6b07c6701c6301c5f01c5b01c5701c5302b6f02b6701b5f02b5701b4f02b4702a6f02a6b02a6702a6301a5f02a5b0ca5a02a5702a5601a5301a4f02a4b02a4701a4302a3b02a3a02a3702a360a96f0896e0b96b0596a0b967059660a963089620195f0195e0295701953019520194f0194e0794b0394a079470394601943019420193b0193a02937019360292f0292e6f12d0986b098630985b018530784b018430282b028230981b0481909813048110ae7f0ae7e0be7b0be7a0be770be760ae730ae720ad7f01d7b0bd7701d7307c7f01c7b07c7701c7307c6f07c6d01c6b01c6907c6707c6501c6301c6101c5f07c5d01c5b01c5707c5501c530bb7601b6e01b5e02a7f09a7b02a7709a7302a6f02a6d09a6b09a6902a6702a6509a6309a6101a5f09a5b02a5701a5301a4f07a4b02a4701a4304962049600487f0887e0487b0487a048770587604873048720184f0184e0484b0384a04847038460184301842048350e8340482f0982e0282b0282a028270282604823048220481d0ae7f0ae7e0be7b0be7a0be770be760ae730ae720ad7f01d7b0bd7701d7307c7f01c7b07c7701c7307c6f07c6d01c6b01c6907c6707c6501c6301c6101c5f07c5d01c5b01c5707c5501c530bb7601b6e01b5e02a7f09a7b02a7709a7302a6f02a6d09a6b09a6902a6702a6509a6309a6101a5f09a5b02a5701a5301a4f07a4b02a4701a430496a049680495a0e9340487f0887e0487b0487a048770587604873048720184f0184e0484b0384a0484703846018430184204835018340482f0982e0282b0282a028270282604823048220481d0ad6f08d6e0bd6b05d6a0bd6705d660ad6308d620ac6f01c6b0bc6701c6307b6f01b6b07b6701b6307b5f03b5d01b5b01b5907b5703b5501b5301b5101b4f07b4d01b4b01b4707b4501b430aa6f0ba6a0aa670ba6601a5f01a5e01a5d01a4f01a4e01a4201a3f07a370296f0b96b029670a9630295f0295da515b6e1590295702955a4153a31510194f0c94b02947019430193f0793b02937019330292b029270b86b0a863a205b04859a1053048510e84b018430783b018330e82d0e8250281b1501301c5f01c5b01c5701c5301b5f01b5b01b5701b5301b4f01b4b01b4701b430295f0295b02957029530194f0194b01947019430193f0193b0193701933 20 1048575 8 255 11 2047 20 1048575
def cc_56_6 : Nat → List (Nat × Nat) := unpackCursorV4 0x9a58641cf84585edc771d359e525a7a5396146cf0fd3c3c460d33c2d4f0973c1e4f06d180d3c40069 0x1d6f01d6e01d6d01c6b05c6a01c6905c6705c6601c6301c6105c5705c5605c5508b6f01b6b05b6701b6308b5f03b5d01b5b01b5908b5703b5501b5301b5101b4f01b4b01b4701b4308a6f05a6b05a6708a6308a5f08a5d08a5b08a570aa5508a5301a4f0aa4b0aa4701a4301a3f0aa3b0aa3701a330896f0596b05967089630895f0295d0895b0b959089570295508953089510194f0b94b0b947019430193f0f93b0c937019330a92f0a92b0a9270a9230886f0586b05867088630885f0885b048590885708853048510184f0b84b0b847018430183f4403b0e837018330a82f0a82b0a8270a8230e81f0c81b0c8170f81301d6f01d6b01d6701d6305c6f05c6b05c6a05c6705c6601c5f01c5e01c5701c5301c5201b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4d01b4b01b4901b4701b4501b4301b4105a6f05a6a05a6705a6601a5f01a5e01a5701a5201a4f01a4e01a4d01a3f01a370296f0596b02967059630195f0195b01957019530294f0294d0c94b0c94902947029450c9430c9410193f0193b01937019330292b029270586b058630185b018530d84b048490e843048410183b018330a82d0e8250281b0c81301d6f05d6e01d6d01d6701d6501d6301d6201c6705c6601c6501c5f01c5e01c5d01b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4d01b4b01b4901b4701b4501b4301b4105a6f05a6b05a6705a6301a5f01a5b01a5701a5301a4f01a4d01a4b01a47cf24501a4301a3f01a3b01a3701a330596f0596b05967059630195f0195b01957019530194f0194d0194b0c949019470294501943019410193f0193b01937019330a92f0c92b0c9270a9230586f0586b05867058630185f0185b01857018530184f0184b048490184701843018410183f0183b01837018330a82f0e82b0e8270a8230c81f0c81b0c8170c81305d6f01d6b02d6701d6305c6f01c6b05c6701c6301c5f01c5b01c5701c5302b6f02b6701b5f02b5701b4f02b4702a6f02a6b02a6702a6301a5f02a5b02a5701a5301a4f02a4b02a4701a4302a3b02a3a02a3702a360296f0296b0296a05967059660195f0295b0295a0b9570b9560194f0194e0794b0394a079470394601943019420293b0293a02937029360292f0292e0d92d0586b058630985b018530784b018430282b028230981b04819098130481101d6f01d6d05d6701d6505d6308c6f08c6d0ac6708c6501c6305c5f01c5b05c5701c5307b6f03b6d01b6b01b6907b6703b6501b6301b6105b5f01b5b05b5701b5301b4f01b4b01b4701b4305a6705a6605a6505a5f05a5a05a5705a5601a4f0aa4a0aa470ba4601a3f07a370296f0296d1096bcd16902967029650d963711610295f0595b02957059530194f0b94b02947019430193f0793b02937019330292b029271086b048690d863048610585b058530b84b018430783b018330281b1a81305d6f01d6b02d6701d6305c6f01c6b05c6701c6301c5f01c5b01c5701c5302b6f02b6e05b6b05b6a02b6702b6602b6302b6201b5f01b5e0ab5b0ab5a02b5702b5601b5301b5201b4f01b4e07b4b03b4a07b4703b4601b4301b4202a6f02a6701a5f02a5701a4f02a4a02a470da4602a3f0da3e02a3d0296f0296b02967029630195f0295b02957019530194f0294b02947019430293b029390293702933029310292b0292902927029210586b058630985b018530784b018430983b0483909833048310282d0d8250281b0281305d6f01d6b05d6701d6305c6f01c6b05c6701c6301c5f01c5b01c5701c5305b6f02b6b05b6702b6301b5f02b5b0bb5701b5301b4f02b4b16b4701b4302a6f05a6b05a6a02a6705a6605a6301a5f0ba5b0ba5a02a570ba5601a5301a4f06a4b02a4701a4302a3f02a3b02a3702a330296f0296e0196b0196a059670196605963029620195f0195e0895b0895a0b9570895601953019520194f0194e1194b0394a169470394601943019420293f1193b7113a11937cb136029330592f0592e0592d0586f0586b05867058630185f0985b0b857018530184f0984b0e847018430283f0983b0e837028330982f0282b0c82902827098231d0210e81f0981b048190e817098130481101d6f01d6e01d6d05c6f05c6e08c6d05c5f05c5e01c5b01c5901c5305c5201c5105b6f03b6d01b6b01b6905b6703b6501b6301b6105b5f01b5b05b5701b5301b4f01b4b01b4701b4305a6fcc26d05a6b05a6705a6505a6305a5f05a5b05a5705a5301a4f0aa4b0ba4701a4301a3f0aa3b9823701a330596f0296d0596b05969059670296505963ca1610595f0595b05957059530194f0b94b0b947019430193f7913b0c937019330a92f7012b0c9270a9230586f0586b048690586705863048610585f0585b05857058530184f0b84b0b847018430183f4203b0e837018330a82f3202b0e8270a8230e81f0c81b0c8171b01301c5f01c5b01c5701c5301b5f01b5b01b5701b5301b4f01b4b01b4701b4308a5f05a5b05a5708a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330695f0595b05957069530194f0194b01947019430193f0193b01937019330692f0692b06927069230885f0585b05857088530184f0184b01847018430183f0183b01837018330a82f0a82b0a8270a8230681f0681b068170681301c5f01c5b01c5701c5301b5f01b5b01b5701b5301b4f01b4b01b4701b4307a5f05a5b05a5707a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330895f0595b05957089530194f0194b01947019430193f0193b01937019330792f0792b07927079230885f0585b05857088530184f0184b01847018430183f0183b01837018330782f0782b07827078230c81f0c81b0c8170c81301c5f01c5b01c5701c5301b5f01b5b01b5701b5301b4f01b4b01b4701b430295f0295b02957029530194f0194b01947019430193f0193b019370193301c5f01c5b01c5701c5308b5f05b5b05b5708b5301b4f01b4b01b4701b4301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330895f0595b05957089530194f0194b01947019430a93f0a93b0a9370a9330192f0192b01927019230885f0585b05857088530184f0184b01847018430a83f0a83b0a8370a8330182f0182b01827018230c81f0c81b0c8170c81301c5f01c5b01c5701c5301b5f01b5b01b5701b5301b4f01b4b01b4701b4308a5f05a5b05a5708a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330895f0595b05957089530194f0194b01947019430193f0193b01937019330a92f0a92b0a9270a9230885f0585b05857088530184f0184b01847018430183f0183b01837018330a82f0a82b0a8270a8230c81f0c81b0c8170c81301c5f01c5b01c5701c5302b5f02b5b02b5702b5301b4f01b4b01b4701b4301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330295f0295b02957029530194f0194b01947019430293f0293b02937029330192f0192b01927019230885f0585b05857088530184f0184b01847018430283f0283b02837028330182f0182b01827018230281f0281b028170281301c5f01c5b01c5701c5301b5f01b5b01b5701b5301b4f01b4b01b4701b4308a5f05a5b05a5708a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330895f0595b05957089530194f0194b01947019430193f0193b01937019330992f0992b09927099230485f0485b04857048530184f0184b01847018430183f0183b01837018330482f0482b04827048230481f0481b048170481301c5f01c5b01c5701c5301a5f01a5b01a5701a5301a4f01a4b01a4701a430885f0585b05857088530184f0184b01847018430182f0182b018270182301d6f01d6d01d6b01d6a01d6705d6601d6501c6f08c6e01c6d01c5f01c5e01c5d01b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4d01b4b01b4a01b49c834801b4701b4601b45c734401b4301b4108a6f05a6b05a6708a6301a5f01a5b01a5701a5301a4f01a4d01a4b01a4ac624801a4701a460aa45c524401a4301a3f01a3b01a3701a330896f0596b05967089630195f0195b01957019530194f0194d0194b0194a0c949c4148019470194602945c314401943019410193f0193b01937019330a92f0a92b0a9270a9230886f0586b05867088630185f0185b01857018530184f0184b0184a04849c20480184701846c104401843018410183f0183b01837018330a82f0a82b0a8270a8230c81f0c81b0c8170c81301d6f01d6d01d6b01d6901d6701d6501d6301d6101c6f03c6e01c6d01c5f08c5e01c5b01c5701c5301c5201b6f01b6d01b6b01b6901b6701b6501b6301b6101b5f01b5b01b5a01b5703b5601b5301b4f01b4d01b4b01b4701b4501b4307a6f07a6d07a6b07a6707a6507a6307a5f05a5b05a5707a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330696f0296d0f96b0f96906967029650f9630f9610695f0595b05957089530194f0194b01947019430193f0193b01937019330692f0792b06927079230e86f1086b048690e86714863048610885f0585b05857088530184f0184b01847018430183f0183b01837018330782f0782b07827078230e81f0681b068170f813 18 262143 7 127 11 2047 20 1048575
def cur_56 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_56_6 (Nat.sub p 192)) (cc_56_5 (Nat.sub p 160)) (Nat.blt p 192)) (Bool.rec (cc_56_4 (Nat.sub p 128)) (cc_56_3 (Nat.sub p 96)) (Nat.blt p 128)) (Nat.blt p 160)) (Bool.rec (Bool.rec (cc_56_2 (Nat.sub p 64)) (cc_56_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_56_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_56 : Nat → Nat × Nat := unpackForestF 0xc5fcf48a0316f34b4e526dcb26d94584062be0b48c168982923052260948c128982123042200c53bf8aa02d7ef51a80b5bbb2c202d5c05a980b4fb746a02d2c05a3da235016875d156c035d8063af6c95cd2c052f80a5b014af54958052980a4fa74ac0292e84add0953a12a34216e842980a479e0513c090052180a3f9b4ac028ee66384a567972732916a54ab4a1410146f169b22d3245a5c8b4a9164a22c92458288b048028cc04afc4347012b60255e0e2bc2345832ac0254c04a7c01507f68e0252c04a3be13601286024fde6b38093b0126ee8d9dd5333a13601266024bdc4b8375676f25adc5680495809276b2ac0248c042fb234f670b8c8d1d95a1b2036010b6be5857c9db017c5f2660215d74222cc5b598aeb4d15642b008530109ea91bd51b7aa34701096a55a12db7a796c4f2a89658d3531259514b2760211d1c1e23836470680210c041fa056f430f88159d06b1a005601076765acf4ae1d9633b282020dce4321ab6f356ce6c998d41b008330105e6159cc2359845b010565cd209e359396b2a298544d09ca194242272620209c8c2e11856230a80208c86338081f010360205c71380e07c02ace341f00a3381457026ce2c1b009ab8a08c10cee2094046b38805c0268e1519829a28525d0a48a148dc082b01d67036b406d580d3301a560348c040d804098003f 8 11
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV4 fullMask g_56 ep_56 209 bds_56 (dagTraceF fullMask rootStock 11 f_56) (cur_56 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_0 : treeBlockF 0 32 (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 209 (dagTraceF fullMask rootStock 11 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_1 : treeBlockF 32 64 (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 209 (dagTraceF fullMask rootStock 11 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_2 : treeBlockF 64 96 (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 209 (dagTraceF fullMask rootStock 11 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_3 : treeBlockF 96 128 (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 209 (dagTraceF fullMask rootStock 11 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_4 : treeBlockF 128 160 (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 209 (dagTraceF fullMask rootStock 11 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_5 : treeBlockF 160 192 (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 209 (dagTraceF fullMask rootStock 11 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_6 : treeBlockF 192 209 (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 209 (dagTraceF fullMask rootStock 11 f_56) cur_56) = true := by decide +kernel
theorem nj_56_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 209 (dagTraceF fullMask rootStock 11 f_56) cur_56) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_56_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_56_1 h1 h2)
theorem nj_56_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 209 (dagTraceF fullMask rootStock 11 f_56) cur_56) i = true := block_join nj_56_1 (fun _ h1 h2 => treeBlockF_at nb_56_2 h1 h2)
theorem nj_56_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 209 (dagTraceF fullMask rootStock 11 f_56) cur_56) i = true := block_join nj_56_2 (fun _ h1 h2 => treeBlockF_at nb_56_3 h1 h2)
theorem nj_56_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 209 (dagTraceF fullMask rootStock 11 f_56) cur_56) i = true := block_join nj_56_3 (fun _ h1 h2 => treeBlockF_at nb_56_4 h1 h2)
theorem nj_56_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 209 (dagTraceF fullMask rootStock 11 f_56) cur_56) i = true := block_join nj_56_4 (fun _ h1 h2 => treeBlockF_at nb_56_5 h1 h2)
theorem nj_56_6 : ∀ i, 0 ≤ i → i < 209 → (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 209 (dagTraceF fullMask rootStock 11 f_56) cur_56) i = true := block_join nj_56_5 (fun _ h1 h2 => treeBlockF_at nb_56_6 h1 h2)
theorem nc_56 : ∀ i, 0 ≤ i → i < 209 → (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 209 (dagTraceF fullMask rootStock 11 f_56) cur_56) i = true := nj_56_6
theorem lb_56 : LowerBin fullMask rootStock g_56 12 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_56 kn_56 sub_56 gl_56 rc_56 nc_56

def wg : List Gate := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [4, 10]⟩, ⟨GateOp.and, [2, 11]⟩, ⟨GateOp.or, [2, 11]⟩, ⟨GateOp.and, [3, 13]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [14, 15]⟩, ⟨GateOp.or, [12, 16]⟩, ⟨GateOp.and, [9, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4007716992 * 2 ^ 32 + 3902832640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4007716992 * 2 ^ 32 + 3902832640)) (13 - 1) := by
  rw [show canon fullMask (4007716992 * 2 ^ 32 + 3902832640) = g_56 by decide]
  exact lb_56

end PEqualNP.Outside.L_meta_49265

theorem PEqualNP.Outside.L_meta_49265 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4007716992 * 2 ^ 32 + 3902832640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4007716992 * 2 ^ 32 + 3902832640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_49265.table2_from_lowerBin (4007716992 * 2 ^ 32 + 3902832640) 13 PEqualNP.Outside.L_meta_49265.root_lb PEqualNP.Outside.L_meta_49265.wg 18 rfl PEqualNP.Outside.L_meta_49265.wfits PEqualNP.Outside.L_meta_49265.weval

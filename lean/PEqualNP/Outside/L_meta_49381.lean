import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49381

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

def m_0 : Nat := 0xf000f0000000000
def s_0 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_0 : Nat := 0x100070000000000
def ep_0 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
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

def m_1 : Nat := 0xf0f00000
def s_1 : List Nat := [0x50500000, 0x30300000, 0xf00000]
def g_1 : Nat := 0x10700000
def ep_1 : Nat := 0x600000000000000000000000000000102000000000000010400000
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

def m_2 : Nat := 0x3300330000000000
def s_2 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_2 : Nat := 0x100130000000000
def ep_2 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
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

def m_3 : Nat := 0x5500550000000000
def s_3 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_3 : Nat := 0x100150000000000
def ep_3 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
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

def m_4 : Nat := 0x5050505000000000
def s_4 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_4 : Nat := 0x10105000000000
def ep_4 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
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

def m_5 : Nat := 0x4444444400000000
def s_5 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_5 : Nat := 0x4044400000000
def ep_5 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_6 : Nat := 0x5000500050005000
def s_6 : List Nat := [0x1000100010001000, 0x500000005000, 0x50005000]
def g_6 : Nat := 0x100010005000
def ep_6 : Nat := 0x1000400000001000000040000000000000000000000000000000000000001000100000000000000000000000
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

def m_7 : Nat := 0x3333000000000000
def s_7 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_7 : Nat := 0x113000000000000
def ep_7 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
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

def m_8 : Nat := 0x5555000000000000
def s_8 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_8 : Nat := 0x115000000000000
def ep_8 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
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

def m_9 : Nat := 0xc0c00000c0c0
def s_9 : List Nat := [0x404000004040, 0xc0000000c0, 0xc0c0]
def g_9 : Nat := 0x40000040c0
def ep_9 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000
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

def m_10 : Nat := 0x4040404040404040
def s_10 : List Nat := [0x40004000400040, 0x404000004040, 0x40404040]
def g_10 : Nat := 0x4000404040
def ep_10 : Nat := 0x40400000000040000040000000004000400000000000000000000000000000000000000000000000000000
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

def m_11 : Nat := 0xff000000000000
def s_11 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_11 : Nat := 0x17000000000000
def ep_11 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_12 : Nat := 0xc000c000c000c0
def s_12 : List Nat := [0x40004000400040, 0xc0000000c0, 0xc000c0]
def g_12 : Nat := 0x40004000c0
def ep_12 : Nat := 0x40008000000040000000800000000000000000000000000000000000000000000000000000004000400000
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

def m_13 : Nat := 0xf0f000000000000
def s_13 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_13 : Nat := 0x107000000000000
def ep_13 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_14 : Nat := 0xf0000000f00000
def s_14 : List Nat := [0x50000000500000, 0x30000000300000, 0xf00000]
def g_14 : Nat := 0x10000000700000
def ep_14 : Nat := 0x60000000000000000000000000000000000000000000000000000000100000002000000010000000400000
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

def m_15 : Nat := 0x3300000033000000
def s_15 : List Nat := [0x1100000011000000, 0x300000003000000, 0x33000000]
def g_15 : Nat := 0x100000013000000
def ep_15 : Nat := 0x1200000000000000000000000000000000000000010000000200000000000000000000000100000010000000
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

def m_16 : Nat := 0xc0c0c0c
def s_16 : List Nat := [0x4040404, 0xc000c, 0xc0c]
def g_16 : Nat := 0x4040c
def ep_16 : Nat := 0x4080000000000040008000000000000000000000000000000000000000000040400
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

def m_17 : Nat := 0xc0c0c0c0
def s_17 : List Nat := [0x40404040, 0xc000c0, 0xc0c0]
def g_17 : Nat := 0x4040c0
def ep_17 : Nat := 0x40800000000000400080000000000000000000000000000000000000000000404000
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

def m_19 : Nat := 0x2222000022220000
def s_19 : List Nat := [0x202000002020000, 0x22000000220000, 0x22220000]
def g_19 : Nat := 0x2000002220000
def ep_19 : Nat := 0x220000000000000000000000002000000200000000200000200000000000000000000000000000000000000
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

def m_20 : Nat := 0x5050000050500000
def s_20 : List Nat := [0x1010000010100000, 0x50000000500000, 0x50500000]
def g_20 : Nat := 0x10000010500000
def ep_20 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000000000000000000
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

def m_21 : Nat := 0x3030000030300000
def s_21 : List Nat := [0x1010000010100000, 0x30000000300000, 0x30300000]
def g_21 : Nat := 0x10000010300000
def ep_21 : Nat := 0x1020000000000000000000000010000000200000000000000000000000000000000000000010000010000000
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

def m_22 : Nat := 0x3030c0c03030c0c
def s_22 : List Nat := [0x101040401010404, 0xc0c00000c0c, 0x3000c0003000c, 0x3030c0c]
def g_22 : Nat := 0x10304040303040c
def ep_22 : Nat := 0x200000800000000000000000002000000000008000000000000000000000000000000000100040400000400
theorem epk_22 : ep_22 = edgePack m_22 g_22 := by decide +kernel
def bds_22 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_22 : KnownBin bds_22 := by intro b hb; simp [bds_22] at hb
theorem sub_22 : ∀ b ∈ bds_22, m_22 &&& b.1 = b.1 := by intro b hb; simp [bds_22] at hb
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_22] at hb
def cur_22 : Nat → List (Nat × Nat) := unpackCursorV4 0x1a2d58952244890e8701 0x39283048e8d081a1924205128ea11b313a526c80e841b000f 7 127 3 7 10 1023 15 32767
def f_22 : Nat → Nat × Nat := unpackForestF 0xc74636f1a14e8a6c43a49220a086c00f 3 10
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV4 m_22 g_22 ep_22 10 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) s_22 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22 : treeBlockF 0 10 (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 10 (dagTraceF m_22 s_22 4 f_22) cur_22) = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 10 (dagTraceF m_22 s_22 4 f_22) cur_22) i = true := fun _ h1 h2 => treeBlockF_at nb_22 h1 h2
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_22 kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0xff00ff0000000000
def s_23 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_23 : Nat := 0x100170000000000
def ep_23 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
theorem epk_23 : ep_23 = edgePack m_23 g_23 := by decide +kernel
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_18, s_18, 4, g_18), (m_3, s_3, 4, g_3), (m_2, s_2, 4, g_2)]
theorem kn_23 : KnownBin bds_23 := by
  intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_0
  · exact lb_18
  · exact lb_3
  · exact lb_2
theorem sub_23 : ∀ b ∈ bds_23, m_23 &&& b.1 = b.1 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_23_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_23_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_23 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_23_1 (Nat.sub p 32)) (cc_23_0 p) (Nat.blt p 32)
def f_23 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV4 m_23 g_23 ep_23 43 bds_23 (dagTraceF m_23 s_23 6 f_23) (cur_23 0) s_23 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23_0 : treeBlockF 0 32 (dagCheckNodeV4 m_23 g_23 ep_23 bds_23 43 (dagTraceF m_23 s_23 6 f_23) cur_23) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23_1 : treeBlockF 32 43 (dagCheckNodeV4 m_23 g_23 ep_23 bds_23 43 (dagTraceF m_23 s_23 6 f_23) cur_23) = true := by decide +kernel
theorem nj_23_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_23 g_23 ep_23 bds_23 43 (dagTraceF m_23 s_23 6 f_23) cur_23) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_23_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_23_1 h1 h2)
theorem nc_23 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_23 g_23 ep_23 bds_23 43 (dagTraceF m_23 s_23 6 f_23) cur_23) i = true := nj_23_1
theorem lb_23 : LowerBin m_23 s_23 g_23 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_23 kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0xffff000000000000
def s_24 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_24 : Nat := 0x117000000000000
def ep_24 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
theorem epk_24 : ep_24 = edgePack m_24 g_24 := by decide +kernel
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13), (m_11, s_11, 4, g_11), (m_8, s_8, 4, g_8), (m_7, s_7, 4, g_7)]
theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_13
  · exact lb_11
  · exact lb_8
  · exact lb_7
theorem sub_24 : ∀ b ∈ bds_24, m_24 &&& b.1 = b.1 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_24_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_24_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_24 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_24_1 (Nat.sub p 32)) (cc_24_0 p) (Nat.blt p 32)
def f_24 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV4 m_24 g_24 ep_24 43 bds_24 (dagTraceF m_24 s_24 6 f_24) (cur_24 0) s_24 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24_0 : treeBlockF 0 32 (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 43 (dagTraceF m_24 s_24 6 f_24) cur_24) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24_1 : treeBlockF 32 43 (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 43 (dagTraceF m_24 s_24 6 f_24) cur_24) = true := by decide +kernel
theorem nj_24_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 43 (dagTraceF m_24 s_24 6 f_24) cur_24) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_24_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_24_1 h1 h2)
theorem nc_24 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 43 (dagTraceF m_24 s_24 6 f_24) cur_24) i = true := nj_24_1
theorem lb_24 : LowerBin m_24 s_24 g_24 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_24 kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0xffff00000000
def s_25 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_25 : Nat := 0x175700000000
def ep_25 : Nat := 0x4000000000000006020000000000001202000000000000145400000000
theorem epk_25 : ep_25 = edgePack m_25 g_25 := by decide +kernel
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_18
theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV4 m_25 g_25 ep_25 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_25 g_25 ep_25 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_25 kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0xf0f0f0f000000000
def s_26 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_26 : Nat := 0x10105000000000
def ep_26 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000010105000000000
theorem epk_26 : ep_26 = edgePack m_26 g_26 := by decide +kernel
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV4 m_26 g_26 ep_26 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_26 g_26 ep_26 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_26 kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0xf0f0f0f00000000
def s_27 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_27 : Nat := 0x107070700000000
def ep_27 : Nat := 0x600000000000006000000000000000000000000000001020202000000000104040400000000
theorem epk_27 : ep_27 = edgePack m_27 g_27 := by decide +kernel
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV4 m_27 g_27 ep_27 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_27 g_27 ep_27 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_27 kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xcccccccc00000000
def s_28 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_28 : Nat := 0x4044400000000
def ep_28 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
theorem epk_28 : ep_28 = edgePack m_28 g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_28 : Nat → List (Nat × Nat) := fun _ => []
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV4 m_28 g_28 ep_28 0 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_28 g_28 ep_28 bds_28 0 (dagTraceF m_28 s_28 4 f_28) cur_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_28 kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0x3333333300000000
def s_29 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_29 : Nat := 0x113131300000000
def ep_29 : Nat := 0x1200000000000012000000000000010202020000000000000000000000000110101000000000
theorem epk_29 : ep_29 = edgePack m_29 g_29 := by decide +kernel
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_29 : Nat → List (Nat × Nat) := fun _ => []
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV4 m_29 g_29 ep_29 0 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_29 g_29 ep_29 bds_29 0 (dagTraceF m_29 s_29 4 f_29) cur_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_29 kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0x5050505050505050
def s_30 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_30 : Nat := 0x10105010505050
def ep_30 : Nat := 0x1040400000001040000040000010004000400000000000000000000000101000100000000000000000000000
theorem epk_30 : ep_30 = edgePack m_30 g_30 := by decide +kernel
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_20, s_20, 4, g_20), (m_6, s_6, 4, g_6), (m_10, s_10, 4, g_10)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_4
  · exact lb_20
  · exact lb_6
  · exact lb_10
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_30_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_30_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_30 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_30_1 (Nat.sub p 32)) (cc_30_0 p) (Nat.blt p 32)
def f_30 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV4 m_30 g_30 ep_30 43 bds_30 (dagTraceF m_30 s_30 6 f_30) (cur_30 0) s_30 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_0 : treeBlockF 0 32 (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 43 (dagTraceF m_30 s_30 6 f_30) cur_30) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_1 : treeBlockF 32 43 (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 43 (dagTraceF m_30 s_30 6 f_30) cur_30) = true := by decide +kernel
theorem nj_30_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 43 (dagTraceF m_30 s_30 6 f_30) cur_30) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_30_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_30_1 h1 h2)
theorem nc_30 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 43 (dagTraceF m_30 s_30 6 f_30) cur_30) i = true := nj_30_1
theorem lb_30 : LowerBin m_30 s_30 g_30 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_30 kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0x5555555500000000
def s_31 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_31 : Nat := 0x115155500000000
def ep_31 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
theorem epk_31 : ep_31 = edgePack m_31 g_31 := by decide +kernel
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_8, s_8, 4, g_8), (m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_3
  · exact lb_8
  · exact lb_4
  · exact lb_5
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_31_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_31_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_31 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_31_1 (Nat.sub p 32)) (cc_31_0 p) (Nat.blt p 32)
def f_31 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV4 m_31 g_31 ep_31 43 bds_31 (dagTraceF m_31 s_31 6 f_31) (cur_31 0) s_31 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_0 : treeBlockF 0 32 (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 43 (dagTraceF m_31 s_31 6 f_31) cur_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_1 : treeBlockF 32 43 (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 43 (dagTraceF m_31 s_31 6 f_31) cur_31) = true := by decide +kernel
theorem nj_31_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 43 (dagTraceF m_31 s_31 6 f_31) cur_31) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_31_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_31_1 h1 h2)
theorem nc_31 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 43 (dagTraceF m_31 s_31 6 f_31) cur_31) i = true := nj_31_1
theorem lb_31 : LowerBin m_31 s_31 g_31 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_31 kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0x666600006666
def s_32 : List Nat := [0x222200002222, 0x60600000606, 0x6600000066, 0x6666]
def g_32 : Nat := 0x64600004666
def ep_32 : Nat := 0x402000000000000000000000004000000020000006020000020000000000000000000000000000000000
theorem epk_32 : ep_32 = edgePack m_32 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_32 : KnownBin bds_32 := by intro b hb; simp [bds_32] at hb
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp [bds_32] at hb
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_32] at hb
def cur_32 : Nat → List (Nat × Nat) := unpackCursorV4 0x16ac58b12a44890e8701 0x31243048c4f080a193c202928f611ab92a524c80a8413000f 7 127 3 7 10 1023 15 32767
def f_32 : Nat → Nat × Nat := unpackForestF 0xc7a63529564f0a4c42a49e205084c00f 3 10
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV4 m_32 g_32 ep_32 10 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) s_32 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32 : treeBlockF 0 10 (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 10 (dagTraceF m_32 s_32 4 f_32) cur_32) = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 10 (dagTraceF m_32 s_32 4 f_32) cur_32) i = true := fun _ h1 h2 => treeBlockF_at nb_32 h1 h2
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_32 kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xc0c0c0c0c0c0c0c0
def s_33 : List Nat := [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0]
def g_33 : Nat := 0x40004040c0
def ep_33 : Nat := 0x40408000000040000040800000004000400080000000000000000000000000000000000000004000404000
theorem epk_33 : ep_33 = edgePack m_33 g_33 := by decide +kernel
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9), (m_17, s_17, 4, g_17), (m_10, s_10, 4, g_10), (m_12, s_12, 4, g_12)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_9
  · exact lb_17
  · exact lb_10
  · exact lb_12
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_33_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_33_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_33 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_33_1 (Nat.sub p 32)) (cc_33_0 p) (Nat.blt p 32)
def f_33 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV4 m_33 g_33 ep_33 43 bds_33 (dagTraceF m_33 s_33 6 f_33) (cur_33 0) s_33 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_0 : treeBlockF 0 32 (dagCheckNodeV4 m_33 g_33 ep_33 bds_33 43 (dagTraceF m_33 s_33 6 f_33) cur_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_1 : treeBlockF 32 43 (dagCheckNodeV4 m_33 g_33 ep_33 bds_33 43 (dagTraceF m_33 s_33 6 f_33) cur_33) = true := by decide +kernel
theorem nj_33_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_33 g_33 ep_33 bds_33 43 (dagTraceF m_33 s_33 6 f_33) cur_33) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_33_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_33_1 h1 h2)
theorem nc_33 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_33 g_33 ep_33 bds_33 43 (dagTraceF m_33 s_33 6 f_33) cur_33) i = true := nj_33_1
theorem lb_33 : LowerBin m_33 s_33 g_33 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_33 kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0x3333000033330000
def s_34 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_34 : Nat := 0x113000013330000
def ep_34 : Nat := 0x1220000000000000000000000012000000200000010200000200000000000000000000000110000010000000
theorem epk_34 : ep_34 = edgePack m_34 g_34 := by decide +kernel
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_15, s_15, 4, g_15), (m_21, s_21, 4, g_21), (m_19, s_19, 4, g_19)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_7
  · exact lb_15
  · exact lb_21
  · exact lb_19
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_34_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_34_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_34 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_34_1 (Nat.sub p 32)) (cc_34_0 p) (Nat.blt p 32)
def f_34 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV4 m_34 g_34 ep_34 43 bds_34 (dagTraceF m_34 s_34 6 f_34) (cur_34 0) s_34 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_0 : treeBlockF 0 32 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 43 (dagTraceF m_34 s_34 6 f_34) cur_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_1 : treeBlockF 32 43 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 43 (dagTraceF m_34 s_34 6 f_34) cur_34) = true := by decide +kernel
theorem nj_34_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 43 (dagTraceF m_34 s_34 6 f_34) cur_34) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_34_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_34_1 h1 h2)
theorem nc_34 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 43 (dagTraceF m_34 s_34 6 f_34) cur_34) i = true := nj_34_1
theorem lb_34 : LowerBin m_34 s_34 g_34 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_34 kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0x5555000055550000
def s_35 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_35 : Nat := 0x115000011550000
def ep_35 : Nat := 0x1040000000000000000000000014000000440000010400000000000001100000110000000000000000000000
theorem epk_35 : ep_35 = edgePack m_35 g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV4 m_35 g_35 ep_35 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_35 g_35 ep_35 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_35 kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0x5500550055005500
def s_36 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_36 : Nat := 0x100150011005500
def ep_36 : Nat := 0x1000400000001400000044000000000000000000010004000000000001001000110000000000000000000000
theorem epk_36 : ep_36 = edgePack m_36 g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV4 m_36 g_36 ep_36 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_36 g_36 ep_36 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_36 kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0xf0f00000f0f0
def s_37 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_37 : Nat := 0x1050000050f0
def ep_37 : Nat := 0x40a0000000000000000000000040000000a0000000000000000000001000000000000000105000005000
theorem epk_37 : ep_37 = edgePack m_37 g_37 := by decide +kernel
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV4 m_37 g_37 ep_37 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_37 g_37 ep_37 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_37 kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0x3300330033003300
def s_38 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_38 : Nat := 0x100130013001300
def ep_38 : Nat := 0x1200000000001200000000000000000000000000010002000200020000000000000000000100100010001000
theorem epk_38 : ep_38 = edgePack m_38 g_38 := by decide +kernel
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV4 m_38 g_38 ep_38 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_38 g_38 ep_38 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_38 kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xf000f000f000f00
def s_39 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_39 : Nat := 0x100070003000700
def ep_39 : Nat := 0x200000000000600000004000000000000000000000000000000000001000200030002000100040000000400
theorem epk_39 : ep_39 = edgePack m_39 g_39 := by decide +kernel
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV4 m_39 g_39 ep_39 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_39 g_39 ep_39 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_39 kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0xcc00cc00cc00cc
def s_40 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_40 : Nat := 0x40044004400cc
def ep_40 : Nat := 0x40008800000040000000880000000000000000000400000000000000000000000000000004004400440000
theorem epk_40 : ep_40 = edgePack m_40 g_40 := by decide +kernel
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV4 m_40 g_40 ep_40 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_40 g_40 ep_40 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_40 kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0xffff0000
def s_41 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_41 : Nat := 0x13770000
def ep_41 : Nat := 0x640000000000000200000000000000132200000000000010440000
theorem epk_41 : ep_41 = edgePack m_41 g_41 := by decide +kernel
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV4 m_41 g_41 ep_41 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_41 g_41 ep_41 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_41 kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xf0f0f0f
def s_42 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_42 : Nat := 0x307070f
def ep_42 : Nat := 0x4080000000000040008000000000000000000000000030202000000000000040400
theorem epk_42 : ep_42 = edgePack m_42 g_42 := by decide +kernel
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_16
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV4 m_42 g_42 ep_42 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_42 g_42 ep_42 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_42 kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xff000000ff000000
def s_43 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_43 : Nat := 0x100000013000000
def ep_43 : Nat := 0x1200000000000000000000000000000000000000010000000200000001000000130000000100000010000000
theorem epk_43 : ep_43 = edgePack m_43 g_43 := by decide +kernel
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_15
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV4 m_43 g_43 ep_43 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_43 g_43 ep_43 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_43 kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xf0f00000f0f00000
def s_44 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_44 : Nat := 0x10000010700000
def ep_44 : Nat := 0x1060000000000000000000000010000000600000000000000000000000100000102000000010000010400000
theorem epk_44 : ep_44 = edgePack m_44 g_44 := by decide +kernel
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14), (m_1, s_1, 4, g_1), (m_20, s_20, 4, g_20), (m_21, s_21, 4, g_21)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_14
  · exact lb_1
  · exact lb_20
  · exact lb_21
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_44_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_44_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_44 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_44_1 (Nat.sub p 32)) (cc_44_0 p) (Nat.blt p 32)
def f_44 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
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

def m_45 : Nat := 0xf0f00000f0f0000
def s_45 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_45 : Nat := 0x107000003070000
def ep_45 : Nat := 0x200000000000000000000000006000000040000000000000000000001020000030200000104000000040000
theorem epk_45 : ep_45 = edgePack m_45 g_45 := by decide +kernel
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_13
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV4 m_45 g_45 ep_45 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_45 g_45 ep_45 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_45 kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0x55550000aaaa
def s_46 : List Nat := [0xaaaa, 0x111100002222, 0x50500000a0a, 0x55000000aa]
def g_46 : Nat := 0x1555000002aa
def ep_46 : Nat := 0x40000000a8000004000000020000001000000002000000000000000000
theorem epk_46 : ep_46 = edgePack m_46 g_46 := by decide +kernel
def bds_46 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_46 : KnownBin bds_46 := by intro b hb; simp [bds_46] at hb
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp [bds_46] at hb
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_46] at hb
def cur_46 : Nat → List (Nat × Nat) := unpackCursorV4 0x1a2d58b12a44874e0701 0x192440619343061134349253d84d5d2d549481a105800f 7 127 3 7 9 511 14 16383
def f_46 : Nat → Nat × Nat := unpackForestF 0x33d33532dd3432573472421a21600f 3 9
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV4 m_46 g_46 ep_46 10 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) s_46 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46 : treeBlockF 0 10 (dagCheckNodeV4 m_46 g_46 ep_46 bds_46 10 (dagTraceF m_46 s_46 4 f_46) cur_46) = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_46 g_46 ep_46 bds_46 10 (dagTraceF m_46 s_46 4 f_46) cur_46) i = true := fun _ h1 h2 => treeBlockF_at nb_46 h1 h2
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_46 kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xa0a0a0a0a0a0a0a
def s_47 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_47 : Nat := 0x202020202020a
def ep_47 : Nat := 0x200000800000200000000080002000000000008000000000000000000020202020202000000000000000000
theorem epk_47 : ep_47 = edgePack m_47 g_47 := by decide +kernel
def bds_47 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_47 : KnownBin bds_47 := by intro b hb; simp [bds_47] at hb
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp [bds_47] at hb
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_47] at hb
def cc_47_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_47_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cur_47 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_47_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_47_0 p) (Nat.blt p 32)
def f_47 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV4 m_47 g_47 ep_47 64 bds_47 (dagTraceF m_47 s_47 5 f_47) (cur_47 0) s_47 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_0 : treeBlockF 0 32 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 64 (dagTraceF m_47 s_47 5 f_47) cur_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_1 : treeBlockF 32 64 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 64 (dagTraceF m_47 s_47 5 f_47) cur_47) = true := by decide +kernel
theorem nj_47_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 64 (dagTraceF m_47 s_47 5 f_47) cur_47) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_47_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_47_1 h1 h2)
theorem nc_47 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 64 (dagTraceF m_47 s_47 5 f_47) cur_47) i = true := nj_47_1
theorem lb_47 : LowerBin m_47 s_47 g_47 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_47 kn_47 sub_47 gl_47 rc_47 nc_47

def m_48 : Nat := 0x5a5a00005a5a
def s_48 : List Nat := [0xa0a00000a0a, 0x121200001212, 0x5a0000005a, 0x5a5a]
def g_48 : Nat := 0x12520000525a
def ep_48 : Nat := 0x400800000000000000000000004000000008000000000000000000001202000002000000000000000000
theorem epk_48 : ep_48 = edgePack m_48 g_48 := by decide +kernel
def bds_48 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_48 : KnownBin bds_48 := by intro b hb; simp [bds_48] at hb
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp [bds_48] at hb
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_48] at hb
def cur_48 : Nat → List (Nat × Nat) := unpackCursorV4 0x16ac58b12a44890e8701 0x31343068c4a08121928204928ea11b393a526c80e841b000f 7 127 3 7 10 1023 15 32767
def f_48 : Nat → Nat × Nat := unpackForestF 0xc7463629d64a0a6c43a494209086c00f 3 10
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV4 m_48 g_48 ep_48 10 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) s_48 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48 : treeBlockF 0 10 (dagCheckNodeV4 m_48 g_48 ep_48 bds_48 10 (dagTraceF m_48 s_48 4 f_48) cur_48) = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_48 g_48 ep_48 bds_48 10 (dagTraceF m_48 s_48 4 f_48) cur_48) i = true := fun _ h1 h2 => treeBlockF_at nb_48 h1 h2
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_48 kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0xc0c0c0c0c0c0c0c
def s_49 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_49 : Nat := 0x404040004040c
def ep_49 : Nat := 0x800000400000004080004000000040008000000000000000000000000000000000004040400040400
theorem epk_49 : ep_49 = edgePack m_49 g_49 := by decide +kernel
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_16
theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV4 m_49 g_49 ep_49 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_49 g_49 ep_49 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_49 kn_49 sub_49 gl_49 rc_49 nc_49

def m_50 : Nat := 0x55aa000055aa
def s_50 : List Nat := [0xaa000000aa, 0x112200001122, 0x50a0000050a, 0x55aa]
def g_50 : Nat := 0x1502000055aa
def ep_50 : Nat := 0x40a800000000000000000000000000000000000004020000000000001002000000000000000000000000
theorem epk_50 : ep_50 = edgePack m_50 g_50 := by decide +kernel
def bds_50 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_50 : KnownBin bds_50 := by intro b hb; simp [bds_50] at hb
theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by intro b hb; simp [bds_50] at hb
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_50] at hb
def cur_50 : Nat → List (Nat × Nat) := unpackCursorV4 0x1a2d58b12a44874e0701 0x324438cd0ce2343492f61abad54a4744a80f 7 127 3 7 6 63 11 2047
def f_50 : Nat → Nat × Nat := unpackForestF 0xfa7536ed0caf472174aa0f 3 6
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV4 m_50 g_50 ep_50 10 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) s_50 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50 : treeBlockF 0 10 (dagCheckNodeV4 m_50 g_50 ep_50 bds_50 10 (dagTraceF m_50 s_50 4 f_50) cur_50) = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_50 g_50 ep_50 bds_50 10 (dagTraceF m_50 s_50 4 f_50) cur_50) i = true := fun _ h1 h2 => treeBlockF_at nb_50 h1 h2
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_50 kn_50 sub_50 gl_50 rc_50 nc_50

def m_51 : Nat := 0x5555555555555555
def s_51 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_51 : Nat := 0x115155511555555
def ep_51 : Nat := 0x1040400000001440000044000014004000440000010404000000000001101000110000000000000000000000
theorem epk_51 : ep_51 = edgePack m_51 g_51 := by decide +kernel
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_30, s_30, 7, g_30)]
theorem kn_51 : KnownBin bds_51 := by
  intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_30
theorem sub_51 : ∀ b ∈ bds_51, m_51 &&& b.1 = b.1 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_51 : ∀ b ∈ bds_51, canon b.1 g_51 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV4 m_51 g_51 ep_51 0 bds_51 (dagTraceF m_51 s_51 7 f_51) (cur_51 0) s_51 7 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_51 g_51 ep_51 bds_51 0 (dagTraceF m_51 s_51 7 f_51) cur_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_51 kn_51 sub_51 gl_51 rc_51 nc_51

def m_52 : Nat := 0xf0f0f0f0f0f0f0f
def s_52 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_52 : Nat := 0x10707070307070f
def ep_52 : Nat := 0x200000800000600000004080006000000040008000000000000000001020202030202000104040400040400
theorem epk_52 : ep_52 = edgePack m_52 g_52 := by decide +kernel
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_47, s_47, 6, g_47), (m_39, s_39, 5, g_39), (m_27, s_27, 5, g_27), (m_45, s_45, 5, g_45), (m_42, s_42, 5, g_42), (m_49, s_49, 5, g_49), (m_22, s_22, 5, g_22), (m_0, s_0, 4, g_0), (m_16, s_16, 4, g_16)]
theorem kn_52 : KnownBin bds_52 := by
  intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_47
  · exact lb_39
  · exact lb_27
  · exact lb_45
  · exact lb_42
  · exact lb_49
  · exact lb_22
  · exact lb_0
  · exact lb_16
theorem sub_52 : ∀ b ∈ bds_52, m_52 &&& b.1 = b.1 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_52 : ∀ b ∈ bds_52, canon b.1 g_52 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_52 : Nat → List (Nat × Nat) := unpackCursorV4 0xd00a18a007187006a3643339038001 0x1e9c3d357270e4d5c7c38e47190e31829a7525aa29d411a5a6496227244d48985125222bc4228825100616a4253e9c7d359268e496c8a39056a71d4d5a7c74e4e991d313a544499a27244d48985125222b44228825100e0ea4153c807500a200e401a8051017a7234a6e8cbd087251a463c7c38f4ea511461a7c34f46971d291a443484690243d287290d4a18942918425064a08ae3f1c76e8dc719ad3f3a76a4dce998d2f3a56249c691a43f287690dca198c2f2856909c6119c1f2836905ca09801f 12 4095 5 31 10 1023 15 32767
def f_52 : Nat → Nat × Nat := unpackForestF 0x214d18dda4d14dcb4a2918946149c01f 4 10
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV4 m_52 g_52 ep_52 9 bds_52 (dagTraceF m_52 s_52 7 f_52) (cur_52 0) s_52 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52 : treeBlockF 0 9 (dagCheckNodeV4 m_52 g_52 ep_52 bds_52 9 (dagTraceF m_52 s_52 7 f_52) cur_52) = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 9 → (dagCheckNodeV4 m_52 g_52 ep_52 bds_52 9 (dagTraceF m_52 s_52 7 f_52) cur_52) i = true := fun _ h1 h2 => treeBlockF_at nb_52 h1 h2
theorem lb_52 : LowerBin m_52 s_52 g_52 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_52 kn_52 sub_52 gl_52 rc_52 nc_52

def m_53 : Nat := 0xffff0000ffff
def s_53 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_53 : Nat := 0x1757000057ff
def ep_53 : Nat := 0x40a8000000000000000000000040000000a8000006020000020000001202000002000000145400005400
theorem epk_53 : ep_53 = edgePack m_53 g_53 := by decide +kernel
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18), (m_9, s_9, 4, g_9), (m_46, s_46, 5, g_46), (m_48, s_48, 5, g_48), (m_32, s_32, 5, g_32), (m_50, s_50, 5, g_50)]
theorem kn_53 : KnownBin bds_53 := by
  intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_18
  · exact lb_9
  · exact lb_46
  · exact lb_48
  · exact lb_32
  · exact lb_50
theorem sub_53 : ∀ b ∈ bds_53, m_53 &&& b.1 = b.1 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_53 : ∀ b ∈ bds_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_53_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xee0e64e41e21c30c20be2be0ba2a6aa60a60a608ae8a08a08a08a08248017e15f05e05e05e05e0564541521330038001 0x6930f922019243c04806d400d282135e406b40ed58e9a901b4e0369406d180da101a5a384ac069380d211b1560328c064f80c971925c034a05cd700da81034d0369260d140da08824d03492589140d20828560508c50d740dac82b55036a24c9740d2c82a55034a20a57890ae0285e0509c280d8101301a381c468344d00c1a01a50036a0411787a2d02c56188a406d6859ab01a4d03492069140d2081a3903462281580c270183e0304c069303122051240304806d400d280835e0e6b40ad5821a901b4e0369406d180da101a5a064ac069380d21020560308c060f80c174034f03696f0d1c0da1b724f03496cc91c0d2181a3f03476068dc0d19ae14f5428e064fd109b8192f3424e5413c88238183f1206e060bc08138001f 12 4095 5 31 11 2047 19 524287
def cc_53_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x8004001938c80630b1818829d44e0270138065c3201808c005c224512009004801670b005802c016009104422010080000000000 0x71781c5d12d781b5d12d381b4906d081b41129781a5dfc9701a59069541a52069441a50069341a45068f41a35f85744955064f64135f41742855060f4b035ec133914c071781c5d06d741b5506d341b4906d141b41069681a590e9581a510e9181a45068f81a3284537a145201378045071781c5d0ed781b5dd8d701b5906d541b5206d441b5006d341b450e9781a5d0e9381a49069081a41068e81a36d45743955064b5c125d01742855060b43025c89701a50c0d701b50a4d341b49c4d141b41849341a49bc9141a41165585946b4d741b5912d541b51b09741a590e9541a5116578594e8c4d9b1261617ab05c068e27234064d26034069401b50a517a845a1315a545206d6a4356069341a49069141a41068e41a318c558194e064f81926 13 8191 5 31 11 2047 18 262143
def cc_53_2 : Nat → List (Nat × Nat) := unpackCursorV4 0xb02a1a828105000 0x220264214c038bc071740dad01b59096ac06d4425a301b45034ba069540d2681a490348a069040d1c81a315229b0c5148026c1045 10 1023 5 31 11 2047 19 524287
def cur_53 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_53_2 (Nat.sub p 64)) (cc_53_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_53_0 p) (Nat.blt p 32)
def f_53 : Nat → Nat × Nat := unpackForestF 0x2204c82516114c821140b4f7a971e95d7a1740b4776131c14572531c0450293da35c68575a05d0291d925c5ed15835c5e914094f56d755a5d561700947471791c5a4c8d13034471491b5646558093736d78db5a3c910f02436d48da5636558092732970b3452ed70b2450213c935d24974915c0211c545e151686a341a4d0545214d585056020dc135e04d682a440a49013520495810560209c001f 7 11
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV4 m_53 g_53 ep_53 69 bds_53 (dagTraceF m_53 s_53 7 f_53) (cur_53 0) s_53 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_0 : treeBlockF 0 32 (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 69 (dagTraceF m_53 s_53 7 f_53) cur_53) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_1 : treeBlockF 32 64 (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 69 (dagTraceF m_53 s_53 7 f_53) cur_53) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_2 : treeBlockF 64 69 (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 69 (dagTraceF m_53 s_53 7 f_53) cur_53) = true := by decide +kernel
theorem nj_53_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 69 (dagTraceF m_53 s_53 7 f_53) cur_53) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_53_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_53_1 h1 h2)
theorem nj_53_2 : ∀ i, 0 ≤ i → i < 69 → (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 69 (dagTraceF m_53 s_53 7 f_53) cur_53) i = true := block_join nj_53_1 (fun _ h1 h2 => treeBlockF_at nb_53_2 h1 h2)
theorem nc_53 : ∀ i, 0 ≤ i → i < 69 → (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 69 (dagTraceF m_53 s_53 7 f_53) cur_53) i = true := nj_53_2
theorem lb_53 : LowerBin m_53 s_53 g_53 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_53 kn_53 sub_53 gl_53 rc_53 nc_53

def g_54 : Nat := 0x1171757137757ff
def ep_54 : Nat := 0x126040a8000016400000448800160040006400a8010606020200020001121202132202000114145410445400
theorem epk_54 : ep_54 = edgePack fullMask g_54 := by decide +kernel
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 7, g_23), (m_34, s_34, 7, g_34), (m_53, s_53, 8, g_53), (m_33, s_33, 7, g_33), (m_51, s_51, 8, g_51), (m_47, s_47, 6, g_47), (m_31, s_31, 7, g_31), (m_52, s_52, 8, g_52), (m_16, s_16, 4, g_16), (m_11, s_11, 4, g_11), (m_44, s_44, 7, g_44), (m_24, s_24, 7, g_24), (m_30, s_30, 7, g_30), (m_19, s_19, 4, g_19), (m_43, s_43, 5, g_43), (m_26, s_26, 5, g_26), (m_38, s_38, 5, g_38), (m_40, s_40, 5, g_40), (m_29, s_29, 5, g_29), (m_41, s_41, 5, g_41), (m_15, s_15, 4, g_15), (m_22, s_22, 5, g_22), (m_36, s_36, 5, g_36), (m_39, s_39, 5, g_39), (m_28, s_28, 5, g_28), (m_35, s_35, 5, g_35), (m_46, s_46, 5, g_46)]
theorem kn_54 : KnownBin bds_54 := by
  intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_23
  · exact lb_34
  · exact lb_53
  · exact lb_33
  · exact lb_51
  · exact lb_47
  · exact lb_31
  · exact lb_52
  · exact lb_16
  · exact lb_11
  · exact lb_44
  · exact lb_24
  · exact lb_30
  · exact lb_19
  · exact lb_43
  · exact lb_26
  · exact lb_38
  · exact lb_40
  · exact lb_29
  · exact lb_41
  · exact lb_15
  · exact lb_22
  · exact lb_36
  · exact lb_39
  · exact lb_28
  · exact lb_35
  · exact lb_46
theorem sub_54 : ∀ b ∈ bds_54, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_54 : ∀ b ∈ bds_54, canon b.1 g_54 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_54_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x7c6417873f75730716416fe186e6186c4226992b6396060b2e5bf4c57a45543374f94a4ce2b48d4146d2041855396823197d2e336260832025e1d92919841134641052f0a75e05d4a03d200013c00001 0x79fc03cf601e7700f3980f5fc07af603d7701eb98075bc03adc03d6d00eb380759403ac601d6200e3f81b1f8038f601c7a00e3b8131d8038e601c7200e33807198038ca01c5f01e2f007174034fe01a7b00d3b8069cc034de01a6b00d3380698c034be01a5b00d2b80694c0349e01a4d00d258069240348e01a4500d218069040328c2014402c3f0121d8030dc0186601c2f00e170070ac0785400c270061300308c1f04400c1700609803cfe01e7e00f3d80f9e803cee01e7600f3980f9c803afe01d7b00ebb8075cc03ade01d6e00eb680f1fc078f603c7701e398071bc038dc03c6d00e2f807178038b601c5900e29807148078a201a7f00d3d8069dc034e601a6f00d368069ac034d201a6700d3280698c034c201a5f00d2d80695c034a601a4f00d2580691c034860587e0243b0061b8070d80186600c32006178030ac0384e01c2600e1180b0880182e00c130075bc07ad601d6701eb180f1bc0d8dc03c6b01e3380f18c078c403c5f00e2d807168038ae01c56035b7816db80d6d604b6a035b3812d980d6c605b6201daf80ed780369e01b4e00da681a5bc032d60696700cb180657c032b60195700ca980e53c032960394700ca182a4fc0527a0193b00c9c82a4dc0526a0193300c988079fc07cf601e7701f3980f5fc0dafc03d7b01ebb80f5cc07ae403d6f01eb68075ac03ad401d6700eb300f594078fe06c7e01e3d80f1e8078ee04c7601e3980f1c8078de03c6e01e3680717c038bc01c5d0353f8069ec0d4ee01a7300d378069ac034ce01a6301d2f80696c074ae01a5301d2780a9340349601a4901d2380a9140348601a4102c3f0121d8070dc0186601c2f00e170070ac0785401c2700e1300708c1c04400c1700a098078be03c5b01e2b80f14c076be03b5b01dab80ed4c0769e03b4b01da380ed0c0d2be0695b034ab81a54c0729e0394b01ca380e50c0727e0393b01c9b80e4cc0b8be06c5b0362b81714c0b6be05b5b02dab816d4c0b69e07b4b02da381ed0c0b2be0695b034ab81654c1729e0b94b05ca382e50c0f27e0593b02c9b81e4cc0dade06d6b036b381b58c0d8de06c6b0363381b18c428be1e45b0ea2b86d14c0d4de06a6b0353381a98c174be0ba5b05d2b82e94c1749e0ba4b05d2382e90c0d0dc0486601c2f0061580709c1a04c03c230641100305c0282600eb58075a8038de01c6b00e3380718c038be01c5d00e2d807164038ae01c5500e298071440b6de04b6b025b3816d8c0b6be05b5d04dad80ed640b6ae05b5504da980ed440369e01b4b00da3806d0c032de0196b00cb180657c032ba0194f00ca580651c032860193f00c9d8064dc0326601d7f00ebd8075dc03ae601d6f00eb68075ac03ad201d6700eb280758c03ac205c7f0263d8131dc0b8e605c6f03e368171ac078d205c6703e3281718c078c201c5f00e2d80715c038a604b76025b30069fc034f601a7700d398069bc034da01a6b00d3480699c034ca01a6300d3080697c034b601a5a00d2b806958034a601a4f00d2580691c034860197f02cbf0065ec032f401977024bb0065cc032e40196f02cb70065b40b2d80196b00cb50065a4032d00196704cb30065942e2c80196300cb1006584032c00195f00caf00656c032b40195700cab00654c032a40194f01ca700652c032940194702ca300650c03284019350989a0060980302c01d6b00eb48071bc038da01c6b00e3480719c038ca01c6300e3080717c038b601c5700e29816dbc0b6da05b6b01db4816d9c0b6ca05b6301db0816d7c096b604b5702da9806d3c0369601b4700da18169b80b4bc0196700cb280656c032ae0195300ca780652c0328e0194300c9f8064ec0326e0193300c928075bc03adc01d6d00e378071ac038ce01c6300e2f807174038b601c5900e2b807154038a601c5102db7812dac096ce05b6302daf816d740b6b603b5902dab816d540b6a603b5100da7806d2c0368e01b4302d3781299c0b4be05a5d02d2b8549540349e01a4702d1f8168dc032de0196b00cb480659c032c60196100caf806574032b60195700caa80653c032960194700ca18064fc032760193700c998064ac0324e0586f02c3681219c0d0ca0285f0142e81615c050aa0184f00c238160fc0b06e0181f00c0b8071bc038d601c6700e3180717c038ba01c5b00e2b807154038a605b6f025b5812d9c0b6c605b5f03dae816d6c0b6ae07b5502da9806d3c0369601b4700da18069bc094d604a6a0353481299c094cc05a6304d3080697c034b601a5a00d2c806960094ae04a5600d298069440349e01a4b00d2380690c1347e05a3b02d1b8268cc032de0196b00cb380658c032be0195b00cac80655c032a60195100ca780652c032940194700ca300650c0327e0193b00c9b8064cc03ade01d6b00eb380758c158de06c6b0363382b18c038be01c5b00e2b80714c136de05b6e035b5812da80d6ce04b66075b1816d88036be01b5e00dad806d68036ae01b5600da9806d481369e03b4e055a5816d281368e05b46055a180ed08264dc01a56055230068f8032de0196b00cb380658c032be0195b00cad00655c032ac0195300ca780652c0328e0194300c948075bc03ad601d6700eb182b1bc0d8d606c670563180717c038b601c5700e29858dbc0d6ce01b5f00dab82ad3c1568e01a6f00d3580699c034c601a5f00d2d806968034ae01a5600d2980693c0349601a4700d218068ec0346e0196f0a0b70065ac032d401967024b300658c032c40195f00caf00656c032b40195700cab00654c032a40194f01ca700652c032940194703ca300650c032840193b00c9d0064dc2426c0686f0343380617c030ae0a84f054238060a80304e0182600c0b8060580502a01d6f00eb580759c03ac605c6f02e3701b1ac098d406c670263301718c0b8c401c5f00e2f00edbc076d603b6701db1806d6c036ae01b5300da3806d14032de0196b00cb380658c032be0195b00cab80654c0329e0194d00ca58065240328e0194500ca18065040327e0193b00c9b8064cc03cfe01e7b00f3b8079cc07afe06d7e01ebd80f5e807aee04d7601eb980f5c803ade01d6e01eb680f1fc0d8fc03c7b01e3b80f1cc078e401c6b00e350071a4038ce01c6600e3180f184038ae01c5600e2a8069fc034f601a7700d398069bc034d601a6700d3180697c034ba01a5b00d2c80695c034aa01a5300d2880693c0349601a4700d218064b80b0fc0487600c37006198070bc0385c01c2b0401500709c0384c01c230161100304c01d6f036b580759c0dac606c6f0363581b19c0d8c60f45f00e2d80715c158a602a6f00d3580a99c034c601a5f00d2d80695c034a602a4f00d2580a91c034860192e03437012198070bc0185601c2701e1180504c01d6f00eb580759c03ac601c6f00e3380718c038be01c5700e2980edbc076d603b6701db1806d7c036b601b5700da980ed3c0769603b4701da18169bc094ce01a5f00d2b82293c1148e03a3f01d1b80a5bc052dc0296b00cb380a58c0b2c40195f00caf00656c032ae0195300ca900a53c0529c0194b00ca480651c032860194200ca08065000527e0293b01c9d00a4dc0526c029330149582e4a80524e0292600c378061ac030ce0186300c2f80616c030b40185700c2b00614c0309e0284e00c258061240308e0184300c210061040307e0183b00c1b8060cc030560182700f3f8079f403cf603e7a00f3b8079d803cea01d7f00ebf0075f403ade01d6e01eb680f1fc078f603c7701e398071bc038d601c6700e3180f17c078ba03c5b01e2c80f15c078aa03c5301e28816dfc096ee01b6f00db380ed7c076ba03b5704daa80ed3c0768e02a7f0153f00a9ec094f402a770153b00a9cc0b4e401a6f00d370069ac034d401a6700d3300698c034c402a5f0152f00a974054b802a5b01d2d00a964174b002a570152b00a954054a802a5301d2900a944074a002a4f0152700a92c0749402a470152300a90c0748402a3b05d1d00a8dc0546c0197f00cbd8065dc032e60196f00cb58065a8032ce0196600cb180657c032ba0195b00cad006564032b001957014ab006554052a80195300ca880653c032960194700ca18064ec0326e0587f0243b8061bc030ce0385f01c2e80e168070ae038560342a8341500709e0384700c178060b80305a0181f00c0f00604807cfe03e7e01f3e8075fc07af601d7701eb98075bc03ada03d6b01eb480759c03aca03d6301eb080f1ec098f403c790263b8131d8078e603c7102633813198098ca03c5f03e2f00716c038ae03c5304629016dfc096ee05b6f03db681ed9c136ca03b5f00dab80ed3c0b68e02a7f0153f00a9ec094f402a770153b00a9cc0b4e402a6f0153700a9b4054d802a6b03d3500a9a4174d002a670153300a994054c802a6302d3100a9840b4c002a5f0152f00696c034b401a5700d2b00a94c074a402a4f0152700a92c0b49402a470152300a90c0748402a3b05d1d00a8dc0546c0297f00cbd80a5dc032e60296f014b68065ac032d202967014b280658c032c20195f00cad822568032ae0295600ca980a53c032960294700ca18064ec0526e0587f0243b8161bc0d0da068670343280e17c030ae0384f02c238060bc0305c0182d00c0f8060780302403e7e01f3e8075e403ae201d6d00eb480759403ac203c7d01e3a8071b4078d201c6500e30816db4136ca02a7e0253d00a9d80b4e402a6e0153680a9b00b4d402a6904d3400a998054ca02a6402d3100a9840b4c001a5e00d2d006958034a402a4e01d2500a918074840ba3a0151b0065b4032d20196500cb0806568032ac0586d034328060b80305a0181e00c090079fc03cf601e7700f3980f5fc14afc03d7b01ebd00f5dc09aec03d7301eb90075bc03adc03d6d01e3f81f1f8078f603c7701e3980f1c8038d601c6a00e3480719c038cc01c6301e3080715c038ac01c5502dbf81addc036de01b6701daf80ed74076ae09b5501da780ed1c054fe02a7e0153d8129e8054ee02a76015398169c8034de01a6e00d358069a8034ce01a6600d31806988054be02a5e0152e80a970054b603a5a0152c82e960054ae02a560152a80a950054a603a520152880e9400549e02a4e0152580e9280548e02a460152180e908054760ba3a0151b80a8d8032fe0197b00cbb8065cc032de0196b00cb500659c032cc0196300caf806574032b60195a00cac806560032ae0295600caa80a550032a60195100ca780652c0328e0194300c9d8064dc0b0fe0687700c3780619c070be0385d01c2b8221540709e0384d01c2381e1140305e0182e00c1680607c0303c0181200ebf8135ec03aee05d7300eb78075b413ad603d6900eb38075940bac603d6102e3f8131ec098ee05c7302e3781f1b40b8d603c6902e3381f1940b8c603c6102e2f80716c038ae0ac53025bb012d98054fe02a7e0153d8129e8054ee02a76015398169c8054de02a6e0153680a9b0054d609a6a0153482e9a0054ce02a660153280a990054c605a6201530816980054be02a5e00d2d806968034ae01a560152980e9480549e02a4e015258169280548e02a460152180e908052fe0197b014bb8065cc052de0296d00cb58065a4052ce0296500cb1806584032be0195b04cad00655c052ac01953014a780652c0528e0194300c1700607807cfc03e7d00ebc8075c403aca03c6d01e3480f194078c202a7e0253d00a9d80b4e402a6e0153680a9b00b4d402a6904d3400a998054ca02a6402d3100a9840b4c001a5e00d2d006958034a402a4e01d2500a918074840196d00cb4806594032c20195a00cab0060b80303c01d6f00eb580759c03ac608c6f0363581b19c118c603b6f01db580ed9c076c601b5f00dad806d5c036a603b4f01da580ed1c076860296f014b580a59c052c60195f00caf00656c032ae0195300ca900a53c0529c0194b00ca480651c032860194200ca08065000527e0293b0149b80a4cc030de0186b00c3380618c030be0185b00c2d00615c030ac0185300c2780a138030960184900c2380610c030840184100c1f8060ec0306e0183300f3f8079ec03cee01e7301ebf81d5f807af603d7a01ebb8135d807ae603d7201e3f80f1ec078ee03c7300e378071ac038ce01c6301e2f80f174078b603c5901e2b80f154078a603c5100db3006d58054fe02a7e0153d8129e8054ee02a76015398269c8034de01a6e00d358069a8034ce01a6600d31806988054be02a5e0152e80a970054b603a5a0152c82e960054ae02a560152a80a950054a603a520152880e9400549e02a4e0152580e9280548e02a460152180e908032fe0197b00cbb8065cc032de0196b00cb500659c032cc0196300caf806574032b60195a00cac806560032ae0295600caa80a550032a60195100ca780652c0328e0194301c2b0181500305c0181e02ebe8175d40b8fc05c7d01e370071a8038cc03c6201e2f00a9f8094f402a790253c00a9d80b4e402a7102d3800a9b8034d401a6601d3100a9780b4b402a5601d2900a9380549a02a4c02d2500a9241349002a460152280a9100b48402a4102d200225a8052cc0294d00ca480a5140328205846044220060b80303c01e7f01f3d8079dc07ce605d7f03ebf0175ec09af405d77026bb0175cc08ae403d6f01eb70075ac03ad401d6700eb300f58c07ac405c7f01e3d8171dc078e603c6f00e3580719c078c603b5e01da700a9fc054fc02a7b0253d00a9dc054ec02a7302d3900a9bc054dc01a6b00d3500699c034cc02a6301d3100a97c054bc02a5d0152e00a96c0b4b402a5902d2c00a95c054ac02a550152a00a94c0f4a402a5105d2800a93c0549c02a4b02d2500a91c0548c02a4301d2100a5fc032f60297700cb98065bc032d60896a00cb380a598032c60295f014ae80656c032b202957014aa80654c032a20294f00ca580a51c032860182e00c0f0075bc0dad601d67062b182d1bc0d8d606c670563182517c038b601c5705629820dbc0d6ce0535f00dab82ad3c0668e02a6f0153700a9ac094d402a670153300a98c174c402a5f0152f00696c034b401a5700d2b00a94c074a402a4f0152700a92c0f49402a470152300a90c0748402a3b05d1d00a8dc0546c0296f00cb580a59c032c60195f00cad82e568032ae0295600ca980a53c032960294700ca18064ec0526e0686f0343382e17c030ae0a84f05c238060bc0305c0182d00c0f8060780302401d6f00eb580759c03ac606c6f0363581b19c0d8c601c5f00e2d80715c038a601a6f00d3580699c034c601a5f00d2d80695c034a601a4f00d2580691c034860192603437012198030bc0185601c2701e1180305db045fd722dea915f4a8a7a435fd11ade80d5f286a78c34fc39a5e18d1f026877a25fbc92dde095eec4a76f24fb5125d8091eb84875a23fac11dd4c8dea44674715fa28adcf455e762a73614f950a5c2051df4286f513f7889dbc04dddc266e112f6e095b0c49d82246b805f5b82da9c15d480a69404f48825a1811d060868003f3f81d9b00dcd60664c02f2181588c09c300461101f0700d80805c020260003f 20 1048575 8 255 11 2047 21 2097151
def cc_54_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc589ef5c1b58febfada9ec287419e07a61ad908fe2bad834f5eebd760b5c4a76c49d8fc35dac9602d506f5233d44888fbad370fcc5ad2c89c92bf1d0f46420130c02bc105ca4002e 0x75bc1eb581d67038de0f17c1db783b6b076ce0ed8c1daf81b5b036ae0ed4c1da783b4b0768e0ed0c2d3703a5e0749c0e8d844a70586f030d61219c0c318185f030b60615c0c298884f030962211c0c218383f030760e0dc0c198282503cfe079f41f3d83e7a03cee139d80f3a81d7f03afc075f41eb783d6e07ada0f1fc1e3d83c77078e60f1bc0e3581c67078c60f17c1e2e83c5b078b20f15c1e2a83c53078a216df825bb03b6e036cc0ed781dae03b56806a80ed381da303a567e4a8165fc0cbd84977032e6065bc0cb581967032c60e57c14ae8195b032b20e55c14aa81953032a20e53c0ca58394703286064e4149a838567c0a80f9fc1f3f03e7d0bafe0f5ec26bb83d730bade075b41eb583d690face075941eb183d61078f6131e81e3c84c77098ec0f1cc1e3884c67098cc131941e2f87c5e078b60f15c1e2988c520b6fc12dd82db705b6c0f6cc32d901daf01b560769c16d182cbf8497b092ee165cc2cb78296d0f2d6065a43cb3829650b2c6065841caf8895b112ae0e54c1ca78594b0b28e0e50c0c9c8293507ade0f5ac1eb383d63078de0f1ac1e3383c5f078b60f15c1e2985b6f0b6dc0ed7c1daf03b5b036b40ed5c0dab03b53076a40ed3c1da708a3e0b2de125ac24b385963072be0e56c1cab839530729e0e52c1ca3839431127e0a4f4449d819391126e0a4d44499819311107c0f5bc1eb583d6707ac60f1bc1e3583c6a078ce131981e2f83c5e078b60f15c1e2983c520b6de0ed7c1dad83b57076a60ed3c2d3704a66074bc069581d2703a460747c0e8d8449f0586f090d61219c2c318385f070b60e15c1c298384f070960e11c1c218883f11076220dc4419818290504a0f9fc1f3d83e7707ce60f5fc1ebe83d7b07af40f5dc26bb03d7507ade0f5b81eb583d6707ac60f5881e3f86c7e078fa0f1bc1e3703c6b038d40f19c0e3303c63078c40f17c1e2f03c5d0b6fc12dd81db701b66076bc0ed581da703b4c0768cecd102cbf8497b092ee165cc1cb78396b072ce0e58c1caf8395b072ae0e54c1ca78294d07296065241ca38294507286065040c9c829350708ce81101f3f03e7d07af20f5c40eb683d6903aca0f5841e3e83c75038da0f1a40e3283c610b6fc12dd82db705b6c0b6cc22d901daf01b560769c0ed1814b681969052ca065840c9c8293503ade0f5ac0eb383d630b8de171b8363584c6a0d8ce131982e3185c62078be0f1781db783b6b076ce0ed8c0dad81b57076a606d1c0da288a4e0b2de065ac34b381963032be0656c0cab819531129e0a5340ca5819491128e0a5140ca1819410727e064ec1c9b819331109c079fc1f3d81e7707ce60f5fdc2bf03d7b07af40f5dc26bb03d7307ae40f5bc1eb703d6d078fe1f1f81e3d83c77078e60f1c80e3581c6a078d20719c0e3303c63078c20715c0e2b01c550b6fc12dd81db701b66076bc0ed701dab373540769c0ed182cbf8197b0d2ee065cc0cb78196b032ce0658c1caf8295d032b6065641cab82955032a6065441ca78194b0728e0650c0c9c8293503ade075ac0eb381d63078de0f1ac1e3383c63038be0715c0e2988b6f0b6dc1adac25b506b67096cc22d8c2db101b57036ac0ed3c1da708a3e032de065ac0cb381963032be0656c0cab819530329e0652c0ca3819430327e064f40c9d819390326e064d40c99819311107c079fc0f3d81e7703ce60f5fc1ebd83d7707ae6075bc0eb703d6d03ace075940eb181d62038fe231f80e3d81c7a038ee131d80e3981c72038ce071980e3281c5f078bc071742dbf04b76036dc06d981daf03b560369c06d300da335344032fe065ec0cbb81973032de065ac0cb381963032be0656c0cab819530329e065340ca5819490328e065140ca18194103272064d40f3f81e7e03cf60f9e80f3b81e7603ce60f9c80ebf81d7b03aee075cc0eb781d6e03ada0f1fc1e3d83c77078e6071bc0e3703c6d038be071780e2d81c59038a6071481e2885b7e096ec06db81db601b66036c806d780dab03b4e0768c065fc0cbd81977032e6065bc0cb68196b032d20659c0cb281963032c20657c0cad81957032a60653c0ca58194703286064e40c9a81d6f07ad60759c1eb183c6f078d60f19c1e3183c5f038b60715c45b785b6e0d6d612da835b384b66116c616d881daf83b5e0369e06d38451f0996f032d61a59c0cb18195f032b60655c0ca98394f032960e51c0ca18893f0527a064ec0c9c889370526a064cc0c988883e03ade0f5ac0eb383d63078de0f1ac1e3383c63078be0716c0e2b89b6f0d6d61ad9c4db183b5f0369e129981d2f03a4e0747c265bc0cb586967032c60657c0cad81957032a60e53c0ca58394703286264fc0c9d89937032660a494441f01d6f07ad60759c1eb183c6f078d60f19c1e3183c5f038b60715c45b786b6b0d6ce22d8c1daf81b4f094cc0e9781d2703a3e1127c2a1bc0c3586867030c60617c0c2d81857030a60e13c0c258384703086220fc0c1d88837030660a0940f3f83e7b03cee0f9cc1ebf88d7e07af60f5dc1eb983d7207ade0f5b40eb581d6a03ace075981eb283c7f198fc0f1ec1e3d03c77098ec0f1cc1e3903c6f078dc0f1b40e2f81c5e038ba16df825bb03b6e036cc0ed781dab03b4e076980ed1991a203a46624882a5fc0cbd86977032e6065bc0cb581967032c60e57c0cad83957032a60e53c14a68194b032920e51c14a28194303282064e4149a8384660088171bc263584c670b8c61717c0e2e85c5b078b21715c0e2a85c53078a216dbc25b584b670b6c616d7c2dae85b5b076b216d5c2daa85b53076a216d3c2da585b470b686169582cb78496b092ce1658c2caf8295d0b2b6065642cab829550b2a60654444a78994b1b28e2250c2c9f8593b0b26e164cc2c2b01d6b03ad2071bc0e3688c6b078d20719c0e3288c63078c20717c262d81c570b8a616dbc2db688b6b076d216d9c2db288b63076c216d7c25ad84b570b6a616d3c0da581b4711686229b814b382965032b60a55c0ca98194f032960651c0ca18293f032760a4dc0c998886e03cfe079f80f3e81d7f09af6075dc2eb981d6f03ada0b5ac1eb481d6703aca0b58c16b085c7f098f6131dc2e3982c6f058da0b1ac1e3482c670f8ca0b18c163085c5f038b60715c562985b7e096ec0adb815b602b665a6c80ed780dab03b4e0b68c065ec24bd01979052ee0a5d80cb981971052ce0a59814b28195f032b60655c0ca98294f032960a51c0ca1819390526a079fc0f3d81e7703ce6075fc0ebf01d7b05af4075dc0ebb01d7305ae4075bc0eb701d6d078fe0f1ec1e3b83c73038de071ac0e3381c63038be0b1740e2d81c59038ae071540e2982c51116fc12dd80db701b66036bc0ad700dab01b540769c0ed180cbf8197b032ee065cc0cb58196a032d20659c0cb301963032c20655c0cab019550329e0652c0ca38194303272064d40f3e81e7503afc075f40eb701d6a03acc075882e2e83c590b8aa0f1442dbf04b76036dc06d982daf05b5c0b6ac22d501da705b460b4ac269500cbe81975032ba065640caa8195103272064d42c2b0885403ade075ac0eb381d63118de171b8363584c6a0d8ce13198463185c62038b60716845b783b6b0d6ce0ed8c0daf81b5b036ae06d4c45a785b4d076960ed2445a385b45076860ed0445230196f032d60659c0cb18195f032b60654c0ca78194d0327e064ec0c9b819331108c079fc0f3f01e7b09cf4079dc0f3b01e7354ce4075fc0ebd81d7703ae6075bc0eb701d6d118fe0f1ec363b83c73038de1f1b40e3581c69038ce071940e3183c61038be0716c0e2b81c531b6fc12dd80db72936c036cc06d900daf01b560769c1ed180cbf8197b032ee065cc0cb78196e032da0657c0caf0195b032b20654c0ca9019510329e0652c0ca38194303272064e00c9a8293403ade0f5ac0eb383d63118de171b8363584c6a0d8ce13198463185c62078be0f1780e2d81c5a038ae071581e2983c52076de0edac1db383b63076be06d6c0dab83b530369606d2445270296f032d60a59c0cb18195f032b60655c0ca9829470528a064ec149b819331109c075bc1eb581d6707ac60f1bc1e3583c67078c60f17c0e2d81c57078a622dbc35b586b67116c60ed7c0dad81b57076a606d3c253303a5e0749c0a8f8449f0286f030d60a19c0c318185f030b60615c0c298184b0508e0610c141b8282503cfe0f9ec0f3b83e7307afe0f5ec1ebb83d7307ade075ac0eb383d63058fe331f8163d82c7a058ee131d8163982c72058de0f1b80e3581c6a038ce07198163182c62038be071780e2e85b7e096ec0edb80db303b5e076ac0ad3815a602b464e6880a5fc0cbd82977032e6065bc0cb581967032c60656c1cad01959052ae0a5580ca9819510528e0a51814a2819390526a0a119302201e7f07cf6079dc1f3982d7f05afc0b5ec26bd02d7705aec0b5cc56b902d6f05adc075ac0eb501d6703acc0b58c1eb105c7f078f6171dc1e3983c6f038d60719c1e3181c5f038bc071742dbf04b76076dc06d9815af0ab5c056ac0ad501da705b46052fe065ec14bb81973032de065ac0cb381963052be0a57814ae8294f0529c0652c0ca48194307284065040c9c8293582ade1b5ac36b3bd563788de1b1ac3633b94636c8bed116d9a2baf4535c6dc12d981daf01b560769c1ed1960b78696b0d2ce2e58d58af8b95b502ae2e54d28a78b94b4828e2e50c0c9c8293503ade0f5ac0eb383d630b8de171b8363584c6a0d8ce131982e3185c62078be0f1781db786b6e076d60ed9c1db183b62036b606d680dab81b56076a606d1c0da301b450b2de065ac34b381963032be0656c0cab819531729e0a5340ca5819491728e0a5140ca1819410727e064ec1c9b8193303cfe0f9ec0f3b83e7307afe1b5f81ebd83d7a07aee135d81eb983d7207ade0f5b81eb683c7f0d8fc0f1ec1e3b83c73078e4071ac0e3503c69038ce071981e3183c61038ae071580e2a85a7f034f61a9dc0d3981a6f034d60699c0d3183a5f054ba0696c0d2c83a57054aa0694c0d2883a4f034960e91c0d218587e090ec0e1b80c330385e070b80e159102a0384e070980e1182c220182e0504c075bc0eb581d6703ac60f1bc1e3583c67078c60717c0e2f01c57038a60714835b786b6b0d6ce1ad8c0dab83b4f032de065ac0cb381963032be0656c0cab819530329e0652c0ca3819430327e064ec0c9b81933090cc061581c270384c1f07c060780eb781d6b03ace0758c1e3783c6b078ce0f18c0e2f81c5e038ae0714c0e2906b6f0b6dc1adac25b506b67096cc1ad8c2db101b57036ac0ed3c1da703b4d032de065ac0cb381963032be0656c0cab819530329e0652c0ca3819430327e064f40c9d819390326e064d40c9981931 18 262143 7 127 11 2047 19 524287
def cc_54_2 : Nat → List (Nat × Nat) := unpackCursorV4 0xc26aef4aab54feb6bda8e9a8e2b9b70655b0900ae20bf808f5f12276eadc7a869d0590ad5c8f552bf50a812d2b43304f62d35ef4b93d2989890ab1bd0c5f20122b42a3d04eb40027 0xeb781d6b03ace0758c1e3783c6b078ce0f18c0e2f81c57038a622dbc2db706b6b096d41ad9c25b308b630b6c406d5c0dab03b4f0769c065bc0cb581967032c60657c0cad81957032a60653c0ca58194703286064fc0c9e8193b03272064dc0c9a8193303262075bc0eb581d6703ac60f1bc1e3583c67078c60717c0e2f01c57038a60714845b786b6b0d6ce22d8c0dab83b4f1147c125980cab0394e0327c064f00c378186b030ce0618c0c2f8185b030ae0614c0c278184b0308e0610c0c1f8183b0306e060cc0c0c81e7f03cf6079dc0f3983d7f07af60f5dc1eb981d6f03adc0f5b40eb381d6503ac6075880e3f88c7e038f6071e80e3b84c76038e6071c80e3381c66038ca0717c1e2f01c5d0b4fc129d80d3701a66074bc0e9580d2701a4c0348d789100cbf8197b032ee065cc0cb78196b032ce0658c0caf8195b032ae0654c0ca78194d03296065240ca38194503286065040c94819250308d741100f3f81e7e03cf60f9e80f3b81e7603ce60f9c80ebf81d7b03aee075cc0eb781d6e03ada0f1fc1e3d83c77078e6071bc0e3703c6d038be071780e2d81c59038a6071481e2885a7e094ec069b81d3601a66034c8069780d2b03a4e0748c065fc0cbd81977032e6065bc0cb68196b032d20659c0cb281963032c20657c0cad81957032a60653c0ca58194703286064a40c9281d6f07ad60759c1eb183c6f078d60f19c1e3183c5f038b60715c4db786b6b0d6ce26d8c1daf81b4f094cc0e9781d2709a3e132de065ac34b381963032be0656c0cab819530729e0652c1ca3819431327e064ec4c9b819330524a075bc1eb581d6707ac60f1bc1e3583c67078c60f17c0e2d81c57116de16db835b584b6a0d6ce12d9845b185b62076be0ed780da781b4e132de065ac34b381963032be0656c0cab819530729e0652c1ca3819431127e0a4f40c9d819391126e0a4d40c998193103cfe0f9ec0f3b83e7307afe235f81ebd83d7707ae60f5c81eb783d6d03ad6075a80eb381d6607aca0f1fc663f03c7b078f40f1dc263b03c73078e40f1bc1e3703c6d038be071780e2e83b46b4688169f8253b03a6e034cc0e9781d2b03a4e074980e91ac9220a97f032f61a5dc0cb98196f032d60659c0cb18395f032b60e55c0ca98394f0529a0652c0ca4839470528a0650c0ca0819290524a171bc263584c670b8c61717c0e2e85c5b078b21715c0e2a85c53078a216dbc25b584b670b6c616d7c2dae85b5b076b216d5c2daa85b53076a216d3c2da585b470b686165bc24b5849670b2c61657c14ae8595b032b21655c14aa85953032a23653c4ca58d94713286164fc2c9d859370b266075ac0eb481c6f038da271ac1e3481c67038ca2718c1e3081c5f098b60715c2e2985b6f0b6da26dac1db485b670b6ca26d8c1db085b5f096b612d5c2da985b4f0369606d1c55a182967052ca0656c14ab819530329e0652c0ca3819430527e064ec149b8193303cfe079f80f3e81d7f09af6075dc2eb981d6f03ada0b5ac1eb481d6703aca0b58c16b085c7f098f6131dc2e3982c6f058da0b1ac1e3482c670f8ca0b18c163085c5f038b60715c562985a7e094ec0a9b8153602a66ac4c80e9780d2b03a4e0b48c065ec24bd01979052ee0a5d80cb981971052ce0a59814b28195f032b60655c0ca98294f032960a51c0ca181929032500a494149201e7f03cf6079dc0f3981d7f03afc075ec16bd01d7703aec075cc16b901d6f03adc075b41e3f83c7b078ee0f1cc0e3781c6b038ce0718c0e2f82c5d038b6071640e2b81c55038a60b1446d3f04a76034dc069980d2f02a5c034ac069501d2703a46032fe065ec0cbb81973032d6065a80cb481967032cc0658c0cb081957032ac065540ca78194b0328e0650c0c948192503cfa079d40ebf01d7d03adc075a80eb301d620b8ba0f1642e2a83c510b6ac26d502d3f04a76034dc069982d2f05a5c0b4ac269501d2705a46032fa065d40cae81959032aa065440c94819280324a0a4900eb781d6b03ace0758c4e3785c6e0d8d6131a8363384c66138c6171880e2d81c5a116de0edac35b383b63036be06d6c0dab81b531169e16d341da583b491168e16d141da183b41032de065ac0cb381963032be0656c0ca98194f0329a064fc0c9d8193703266235bc36b586d6711ac6071bc0e3581c67038c60717c45b783b6b0d6ce0ed8c45af83b5b116ae0ed4c0da781b4b0368e06d0c452b0d96e032ac065500ca307936030de061ac0c3381863030be0613c0c25818430307e060ec0c1b818330302a079fc0f3f01e7b09cf4079dc0f3b01e73a6ce4075fc0ebd81d7703ae6075bc0eb701d6d118fe0f1ec363b83c73038de1f1b40e3581c69038ce071940e3183c61038be0716c0e2b81c531b4fc129d80d375226c034cc069900d2f01a560749c1e9180cbf8197b032ee065cc0cb78196e032da0657c0caf0195b032b20654c0ca9019510329e0652c0ca38194303252064a00c9282924030dd441b00eb783d6b03ace0f58c4e3785c6e0d8d6131a8363384c66138c6171881e2f83c5e038b6071680e2b81c56078a60f1481db783b6b076ce0ed8c1daf81b5b036ae0ed4c0da581b49052de065ac14b381963032be0656c0cab819530528e0a5140c9d8393a0526e0a4d80c9981e7f07cf6079dc1f3983d7f07af60f5dc1eb983d6f03ad60759c1eb182c7f198fc0b1ec163d02c77098ec0b1cc163902c6f078dc071ac0e3501c67038cc0b18c163101c5f038bc071742d3f04a76074dc069981d2f03a560549c0a93015234f244052fe065ec14bb81973032de065ac0cb381963032b60e5680cac82957052ac0654c0ca8829470528c0a5140c948292503cfe0f9ec0f3b83e7305afe0b5f816bd84d7a05aee0b5d816b98ad7205ade0b5b80eb581d6a03ace0759816b183d620b8fe0f1ec2e3b83c73078de071ac0e3383c63038be071780e2e85a7e094ec0e9b80d3302a5e154b80a958152a03a4e0b48c0a5fc0cbd82977032e6065bc0cb581967032c60a57c14af0295d0529e0a5380ca581949032860e5080ca081929032500a49414926956f0dad61b59f32b1e546f0d8d61b19f1231df45fb88b76d15ec229d726e094cc0e9780d2b03a4e0f48d545bc34b586967172c75057c5cadd0157172a73853c5ca5cd14717286064a4149281d6f07ad60759c1eb185c6f0b8dc1b1ac263506c67098cc1718c2e3103c5f078bc0edbc1db583b67076c606d6c0dab83b530368e06d142cb78196b0d2ce0658c0caf8195b032ae0654c5ca78294d03296065245ca38294503286065041c9f8193b0726e064cc0f3f83e7b03cee0f9cc1ebf86d7e07af60f5e81ebb84d7607ae60f5c81eb783d6e07ada0f1fc363f03c7b078ee0f1cc1e3901c6b038d40f1a40e3381c66078c60f1840e2b81c56038aa169fc0d3d86a77034e6069bc0d3581a67034c60e97c152e81a5b034b20e95c152a81a53034a20e93c0d2583a4703486161f8243b0386e030cc0e1781c2e03856960a80e1381c26038460b088060b8141301d6f03ad60759c0eb183c6f078d60f19c1e3181c5f038bc0715c0e2981c520d6de16db835b584b6a0d6ce12d9835b185b62036ae06d581da783b4e032de065ac0cb381963032be0656c0cab819530329e0652c0ca3819430327e064f40c9d819390326e064d40c998193103cfe079ec0f3b81e7307afe0f5ec1ebb83d7303ade075b81eb681d6703aca0758c0eb101c7f0d8fc071ec0e3d01c77098ec071cc0e3901c67038cc071940e2f83c5e038ba069fc0d3d81a77034e6069bc0d3581a67034c60697c0d2d81a57034a60693c0d2681a4b034920691c0d2281a4303482161f8243b0186e030cc0e1781c2b0184e030980611a48220182e0304c079fc0f3f01e7b07cf4079dc0f3b01e7307ce4075fc0ebd81d7703ae6075bc0eb701d6d078fe0f1ec1e3b83c73038de071b81e3681c5f038bc0716c0e2c81c53038a40f1440d3f81a7b034ee069cc0d3781a6d034d6069a40d3381a65034c6069840d2f81a5b034ae0694c0d2781a4b0348e0690c2c3f04876030dc0e1b00c3301864030bc061581c27038460305c060980eb783d6b03ace0f58c1e3783c6b078ce0f18c1e2f81c5b038ae1adbc35b586b670d6c60ed7c0da78696f032d61a59c0cb18195f032b60655c0ca98394f032960e51c0ca18a93f03276224dc0c9984866070bc0e1387c1f0281603ade0f5ac0eb383d63078de0f1ac1e3383c63078be0716c0e2b86b6f0b6dc1adac25b506b67096cc1ad8c2db103b5f076bc06d3c0da70696f032d61a59c0cb18195f032b60655c0ca98394f032960e51c0ca18a93f0527a064ec0c9c8a9370526a064cc0c9881e7f07cf6079dc1f3983d7f0dafc0f5ec1ebb83d7307ae40f5bc1eb681d6b03ad40759c0eb303d65078fe1b1f81e3d83c7a078ee131d81e3983c72078de0f1b81e3681c5f038bc07174353f81a7b0d4ee069cc0d3781a6b034ce0698c1d2f81a5b074ae0694c1d2782a4d03496069241d2382a4503486069041ca3461440b0fc121d81c3701866070bc0e1701c2b078540709c0e1301c23450440305c0a09836b786d6b0dace1b58c363786c6b0d8ce1b18e522fc845b8e8af1114c353786a6b0d4ce1a98c5d2f8ba5b174ae2e94c5d278ba4b1748e2e90c343704866070bc061581c27078460305c0a0981eb783d6e038d60719c0e3181c57038aa16dbc1db584b67076c616d7c2dae83b5b076b216d5c2daa83b53076a206d3c0da581b4703686229780cb78196b032ce0658c0caf8195d032b6065640cab81955032a6065440ca78194b0328e0650c0c9f8193b0326e064cc442f01e7f07cfc079f40ebd84d7a03af2075dc0ebb01d7303ae20759c0eb301d650b8fe0f1ec263b83c73038de071b40e3583c69038ce1f1940e3181c61038be0716c0e2b81c530b6fc12dd80db701b6c036cd08d900daf01b560769c16d180cbf8197b032ee065cc0cb78196d032d6065a40cb381965032c6065840caf8195b032ae0654c0ca78194b0328e0650c0c9c8193503ade0f5ac0eb381c6f038dc0f17c1e2f03b6f076d60ed9c1db183b5f036b606d5c1da983b4f0769a0ed2c1da483b470768a0ed0c1da088a4e0b2de065ac24b381963032be0656c0cab819531129e0a5340ca5819491128e0a5140ca1819410727e064ec1c9b819331109c075bc1eb581d67038de0f17c1db783b6b076ce0ed8c1daf81b5b036ae0ed4c1da783b4b0768e0ed0c2d3703a5e0749c0e8d82cb78196b092ce0658c0caf8195b032ae0654c4ca78194b1328e0650c1c9f8193b0726e064cc14928884e 18 262143 7 127 11 2047 19 524287
def cc_54_3 : Nat → List (Nat × Nat) := unpackCursorV4 0xf305fd055f8a16ecf45d485796d26fa33dc133b2c5751d3e8a19ce72d91cb300a31e39db9a2d66ec6b35a93ea825d20464567d4f4e7931a42b2ca7e498fc7d160c931110821a8781f958003f 0x175bc1eb584d6707ac6171bc1e3584c67078be0f16c1e2b83c530b6de16db81daf83b5e136b606d684dab81b56076a60ed481da783b4e0b4dc269582d1f0596f092d61259c2cb18395f132b62655c1ca98394f0b2961651c1ca18993f0527a264ec0c9c899370526a264cc0c98899250bade0f5ac26b383d630b8de171b41e3584c6a098ce131982e3283c63078be171781e2d83c57078a6331482db785b6e0b6da0ed7c1daf05b5b036b416d5c0dab03b53076a40ed3c1da704b4d0b68e16d141da183b420b4de1299c1d2f8da570749e1691c2d1f85a3d0b46ff88d42cb78496b092ce1658c1caf8a95b1b2ae0e54c1ca78594b0b28e0e50c2c9f8293d0b276064e42c9b829350b266064c45495f01270b0de161b4243504867090cc1a1941c2f868570709e1611c1c1f8383d09074160dc2c1b03835070681a07c340b81d6f07ad60759c1eb185c6f0b8d61719c2e3183c5f038b60715c2db786b6b096d41ad9c25b305b63076be0ed783da787b4e0d4cc0e9783d2703a3e0b2de065ac34b381963032be0656c0cab819530f29e0652c2ca3819431327e064ec4c9b819331324a321981c270983e03ade0f5ac0eb383d630b8de1f1b82e3585c670b8c6331881e2f81c5b038b40715c0e2b03c53076de0edac1db503b67096cc0ed8c1daf83b5e076ba0ed3c3da703b4d0b4de1a99c1d2f81a570f49e1691c1d1f83a3d0746ff08d42cb78196b0d2ce0658c0caf8195b032ae0654c3ca78194b0b28e0650c1c9f8193b0726e064cc0c958a9270b0de321a834338c866070be0615c1c278384e0709a0e0fc1c1b8181f1102e075bc0eb581d6703ac60f1bc1e3583c67078c60717c0e2d81c570b6de16db835b584b6a0d6ce12d982db185b62036be06d780da781b4e032de065ac0cb381963032be0656c0cab819530329e0652c0ca3819430327e064f40c9d819390326e064d40c99819310bade1b5ac26b506d6709acc1758c0e3781c6b038ce0718c2db787b6e0b6d616d9c2db18db62036be06d6c0dad01b59036b006d5c0dab03b53076a206d3c0da581b4a0368e06d180da183a6f074d60e9a81d3386a66074c60697c1d2d83a5a074b20e95c3d2b03a53074a20693c0d2701a4b0348e0690c0d210186f030d60619c0c318185f030b60615c0c298184f030960611c0c218183f03076060e40c1b8183303062060bc0c158182703046079fc0f3f01e7b09cf4079dc0f3b01e730bce4075fc0ebd81d7703ae6171fc3e3f05c7b098f4171dc263b05c731b8e4071bc0e3705c6d0b8d8071ac0e3501c69038d00719c0e3301c65038c80718c0e3107c61f48c00717c0e2f01c5b038b40715c0e2b01c53038a40edfc1dbd83b7a076ee1add81db981b6f036dc0edb42db601b6b036d206d9c0db281b63036c40ed841db001b5f036bc06d6c0dab81b53036a4069b80d2f0197f032f6065dc0cb98196f032da065ac0cb481967032ca0658c0cb08195f032b60655c0ca98194f0329a0652c0ca4819470328a0650c0ca08193f03276064dc0c998c876030dde41b01c270383e0bade0f5ac36b383d630b8de0f1ac2e3383c63078be0f16c1e2b83c530b6de16db835b584b6a0d6ce12d982db185b62076be0ed784dad81b5a236ae06d581da983b520b4dc169182d1b0596f0d2d61a59c2cb18395f132b7cc55c1ca98394f0b2961651c1ca18993f0527a264ec0c9c899370526a264cc0c9883d6f07ad60f59c1eb185c6f0b8d61719c2e3183c5f078b60f15c1e2983b6f076d60eda81db384b66076c60ed7c1daf03b5b076ae0ed4c1da903a360b2de1a5ac34b385963072be0e56c1cab839530f29e1652c2ca3879430727e0e4ec1c9b83933190cc0e1380eb781d6b03ace0758c1e3783c6b078ce0f18c0e2f81c5b038ae0714c2db785b6e0d6d612da835b384b660b6c616d880daf81b5e036b606d680dab81b56036a606d480da781b4e0368e06d0c0da105a6f0d4ce0697c0d2b83a4f0748e3e8fc4d1e8fa371346a065bc0cb581967032c60657c0cad81957032a60653c0ca58194703286064fc0c9e8193b03272064dc0c9a8193303262064ac0c938586f0d0ce0617c0c2b8384f0308e0e0fc1c1e818370306a0607c0c0e818170502a175f826bd04d760bae4075a83e3f04c7a098ec371c80e3701c6a038cc071883e2f05c5d0b8b8271683e2c8fc580f8ac171542e2a09c520f8a2271401dbd06b76036dc06d883daf03b5d0b6b80ed641daa83b52076a20ed402d3f01a66034ac1e9384d260195d0329a065240ca2819410324a321d81c270383e03cfc139e80f3b05e7203adc075b41e3681c69038ca0f1842dbf04b7a096ec16dc80db709b6d2f6d806da80db481b68036cc06d940db201b62136c226d800daf01b5a036ac06d482d3f01a6e134d80e9182d1b0196e032da065780cac81952032a2064f40c9c8193503262175bc36b584d6a0dace135982eb181c6f038d60719c0e3181c5f038ae0714c2db787b6e0b6d616d9c2db18db62036be06d6c0dad01b59036b006d5c0dab03b53076a206d3c0da581b4a0368e06d180da183a6f074d60e9a81d3386a66074c60697c1d2d83a5a074b20e95c3d2b03a53074a20693c0d2701a4b0348e0690c0d210596f0d2ce2257c44ab8194f0328e1e4fc2c9b8392f0725a0e49c3c928186f030d60619c0c318185f030ae0614c0c278184b0308e0610c0c1f8183d03076060dc0c1a818330305e060ac0c1381823030360605c0f3f81e7e03cf6139e80f3b81e7603ce6179c80ebf81d7b03aee075cc0eb781d6e03ada171fc3e3f05c7b098f4171dc263b05c731b8e4071bc0e3705c6d0b8d8071ac0e3501c69038d00719c0e3301c65038c80718c0e3107c61ea8c00717c0e2f01c5b038b40715c0e2b01c53038a40edfc1dbd83b7a076ee1add81db981b6f036dc0edb42db601b6b036d206d9c0db281b63036c40ed841db001b5f036bc06d6c0dab81b53036a4169fc353b81a6fe84da0699c0d3281a5f034ae1e93f992685a470f48a0e8fc1d1e83a370f46a065fc0cbd81977032e6065bc0cb70196d032be065780cad81959032a6065480ca88194f0329a0652c0ca4819470328a0650c0ca08193f03276064dc0c998192b032540649c14930587f170f41a1dc643b0186f030dc221b7903601867030ca061880c2f818570709e0e1381c268383f0707c0e0c80c0f8181d0302e0a0542ebe84d7a09aec175d42eb70ad620b8fc171f41e3701c6a038cc0f1881e2f04c5d056fc12de815bc84b78056ec16dc815b885b70056dc06da80db303b62056bc16d6815ab03b520569c0ad3415a605b4a056923ad2015a302b450568816d0815a085b400b48c269100d1f0a96a052cc0a5342ca501949032900a51814a28294403282064a4243b0584607088075bc1eb581d6707ac6171bc1e3585c67078c60f17c3e2f01c5b038ae0f14c562905a6f0b4dc1a9ac253506a67094cc1698c2d3103a5f074bc0696c0d2d01a57034ac0e94c1d2902a4f0549c0a5bc0cb582967032c60657c0cad81957032a60a53c0ca58294703256064a40f3f83e7b03cee0f9cc2ebf87d7e0baf6135e82ebb84d760bae7c15c81eb783d6e03ad6075a80eb381d6607ac60f5882e3f83c7b0d8f4171dc363b03c73078de1f1b80e3581c67078c62b18815bf82b7e056f612de815bb82b76056e616dc815b782b6e036d606da80db381b66056c60ed8815af82b5e056ba0ad7015ad85b5a056b216d6015ab82b56056aa0ad5015a987b52056a3bcd4015a782b4e0569616d2815a382b46056860ed080d1f0297f032f60a5dc0cb98196f032d62a5a80cb382966032c60a57c14ae8195b032b20a55c14aa81953032a20a53c0ca58294703286064a4643b0385e0709c079fc0f3f01e7b09cf4079dc0f3b01e730bce4075fc0ebd81d7703ae6171fc363f05c7b098f4171dc263b05c730d8e4071bc0e3703c6d078d8071ac0e3501c69038d00719c0e3301c65038c80718c0e3103c61078c00717c0e2f01c5b038b4071640e2c01c57038ac0714c0e2903c51078a00edfc1dbd83b7a076ee1add81db981b6f036dc0edb42db601b6b036d206d9c0db281b63036c40ed841db001b5f036bc06d6c0dab81b53036a4065fc0cbd81977032e6065bc0cb68196b032d20659c0cb281963032c20657c0cad81957032a60653c0ca68194b032920651c0ca28194303282064fc0c9d81937032661a1d80c370185e0709c0e0f80c0b05d6f07ad61b59c1eb185c6f0f8dc171ac263505c67098cc1718fea3103c5f078bc1f16c0e2d05c57038ac0f14c1e2905b6f076d61ada82db386b66076c60ed7c3daf03b5b076ae0ed4fd9a905a6f0d4ce0e97fc12b87a4fee49a1691c3d2283a3fec47a168dc3d1a8596f0d2d61a59c2cb18395f152b7c455c1ca98794f0529a1652c0ca4859470528a1e50c0ca08393f0b276164dc1c998a92bdc24e161bc643506867190cc0e17f682b8384f0709c0e1341c1f8383e070642a07c5c0b83d6f07ad60f59c1eb183c6f078d60f19c1e3183c5f078b60f15c1e2986a6f0d4d61a99c353183a5f074b60e95c1d2983a4f074960e91c1d21839460d0dc121981c2f018560709c060b8141303d6f07adc071ac0e3381c63038ae071542db783b6b096ce0ed8c2daf85b5d076b60ed642dab85b55076a60ed440da781b4b0368e06d0c0cb78196b032ce0658c0caf8195d032b6065640cab81955032a6065440ca78194b0328e0650c0c9f8193b0326e064cc0f3f83e7e03cfa075ec26bd01d7903aee075d80eb981d7103ace075980eb285c7f078f6131dc1e3981c6f038da071ac1e3481c670f8ca0718c0e3081c5f038b60715c0e2985a7e094ec069b80d3601a66d44c8069780d2b03a4e0b48c065fc0cbd81977032e6065bc0cb68196b032d20659c0cb281963032c20657c0cad81957032a60653c0ca58194703286064a40c9281d6f07ad60759c0e3783c5f076de0edac1db383b63076be06d6c0dab83b530769e0ed2c1da383b430b4dc0e9784d2703a360b2de065ac24b381963032be0656c0cab819531329e0652c4ca3819430727e064ec1c9b819330524a075bc1eb581d67038de071b81e2f83c5e076de0edac1db383b63076be06d6c0dab83b530769e0ed341da583b490768e0ed141da183b410b2de065ac24b381963032be0656c0cab819531129e0a5340ca5819491128e0a5140ca1819410727e064ec1c9b8193303cfe079f41f3d83e7a03cee139d80f3a81d7f03afc075f41eb783d6e07ada0f1fc1e3d83c77078e60f1bc0e3581c67078c60f17c1e2e83c5b078b20f15c1e2a83c53078a20ed5b41aa05a7e094ec0e9b80d3303a5e074b80e95b392a03a4e0748c165fc0cbd84977032e6065bc0cb581967032c60e57c14ae8195b032b20e55c14aa81953032a20e53c0ca58394703286064a4149283e7f07cfc0f9f42ebf83d7b09aee0f5cc2eb781d6d07ad60f5a43eb381d6507ac60f5841e3d84c7a078f2131dc263b03c73078e21319c263304c65078be1f1781e2d83c57078a6231482d3f04a760b4dc169b03d330ca64074bc069581d2705a460b2fe125ec24bb859730b2de0a5b43cb5819690f2ce0a5942cb181961072be2256c44ab839530729e1652c2ca383943032520a4941eb783d6b07ace0f58c1e3783c6b078ce0f17c1e2d83c57078a616dbc2db703b5f076bc0ed6c0dad03b57036ac0ed4c1da903b4f0769c165bc24b5849670b2c60e57c1cad83957072a60e53c1ca58394707286264fc149e8993b03272264dc149a8993303262260d81eb783d6b07ace0f58c1e3783c6b078d40f19c263303c5f078bc0f16c1e2b83c53078a416dbc1daf83b5b076ae0ed4c1da788a3e0b2dc125981caf019560729c0e5181c9f0393c1126c161bc2435848670b0c60e17c1c2d83857070a60e13c1c258384707086220fc441d888371106606064140a83e7f07cf60f9dc1f3983d7f07afa0f5ec1ebd03d7709aec0f5d41eb783d6e07ad60f59c1eb183d62078fe1b1f81e3e83c6f078dc0f1ac0e3503c67038cc0f18c1e3103c5f078bc0f1742d3f04a76074dc069981d2f03a560749c0e9301d23642440b2fe125ec24bb85973072de0e5ac1cb383963072be0e56c1cab839530729e0a5341ca5819490728e0a5141ca181941032520a4941c236304407cfc0f9f41ebc83d7103ada0f5a40eb283d61078fa0f1d40e3683c69038ca0f1842d3f04a760b4dc169b02d3309a64074bc069581d2703a46052da065a414b281961032520a4940eb783d6b03ace0f58c2e3785c6e0d8d6131a8363384c660b8c6171881e2f83c5e076de0edac1db383b63036b606d5c1da981b470368a165bc0cb586967032c60657c0cad81957032a62253c14a68194b032922251c14a281943032820e4fc0c9d8393703266079fc1f3d81e7707ce60f5ff0abf03d7b07af40f5dc26bb03d7307ae40f5bc1eb703d6d078fe1f1f81e3d83c77078e60f1c80e3581c6a078d20719c0e3303c63078c20715c0e2b01c550b4fc129d81d3701a66074bc0e9701d2b602540749c0e9182cbf8197b0d2ee065cc0cb78196b032ce0658c1caf8295d032b6065641cab82955032a6065441ca78194b0728e0650c0c9482925 19 524287 8 255 11 2047 19 524287
def cc_54_4 : Nat → List (Nat × Nat) := unpackCursorV4 0xe14cf5ecdd1cbf0af9bd8a6dfadb28aea942a1d1254668c12224188606207227c0b9ca4c62bfd752b519792fad440fcf6b3384acb35c23d2083181dc606622144a837b3043380021 0x9d6f05d6e06d6b04d6a06d6704d669f56305d6201c6f03c6b01c6703c6303b6f03b6b03b6703b6303b5f03b5d03b5b03b5903b5703b5503b5303b5103b4f01b4b01b4703b4303a5e03a4e9c16f0196b06967019630995f0295d0195b01959099570295501953019510194f0194b01947019430393f0193b03937019339712503d6f03d6d01d6b01d6901d6701d6501d6301d6101c6f01c6d01c6701c6501c6301c5f01c5b01c5701c5303b6f03b6d03b6b03b6903b6703b6503b6303b6103b5f03b5b03b5703b5301b4f01b4b01b4701b4312a6f09a6d12a6709a6505a5f04a5701a4f01a4703a3f03a370196f0196d0196b01969019670196501963019610195f0195b01957019530194f0194b01947019430193f0193b01937019330192b019270186f0186d01867018650585f048570184f018470383f038370181f0181701e7e01e7d05d7e04d7a04d7605d7202d6e02d6d02d6c02d6a09d6919d6802d6609d6509d6402d6202d6102d6001c6d01c6901c6501c6102b6d03b6903b6502b6103b5d03b5903b5503b5103a5e01a4e0197a01979029760197102966019650295e0195d0295c01959019550195201951019500192501e7f01e7e01e7d01d7f01d7b01d7701d7301d6f01d6d01d6b01d6901d6701d6501d6301d6103c7f05c7e03c7b03c7a03c7704c7603c7303c7202c6f02c6e02c6d02c6c02c6b02c6a03c6903c6802c6702c6603c659d46402c6302c6202c6102c6003b7f03b7b03b7703b7302b6f02b6d02b6b03b6902b6703b6502b6302b6101b5f01b5b01b5701b5303b4f03b4d03b4b03b4903b4703b4503b4303b4105a7f04a7702a6f02a6d02a6711a6501a5f01a5703a4f03a4d03a479c24503a3f03a370197b0197a01979019770297601973019710196702966019650195f0195b01957019530194f0194d0194b01949019470194501943019410193f0193b01937019330192b019270587f048770286f0286d02867068650185a01857018560184701846018450383f038370181f0181703e7e03e7d01d7901d7101d6503c6d03c6903c6503c6102b7e04b7a02b7605b7202b6e02b6d02b6c05b6a02b690eb6802b6602b6502b6405b6202b6105b6001b5e01b5a01b5601b5202b4e03b4a02b4603b4201a3e0196d0196901965019610195a019560192901e7901e7105d7e03d7a04d7603d7203c5d03c5903c5503c5102a7e02a7d01a6e03a6d03a6c01a6a01a6601a6501a6401a6203a5e03a5d03a5c03a5a05a5905a5803a5605a5512a5403a5203a5103a5003a4e03a4a03a4603a420197d019750195d01959019550195101929018660185601d6f01d6b01d6701d6303c6f03c6b03c6703c6301c5f01c5b01c5701c530ea6f05a6e06a6b04a6a06a6704a660ea6305a6201a5701a5603a4f03a4e03a4b03a4a03a4703a4603a4303a420196f0196b01967019630195f01957019530194f0194b01947019430192b0192909d6f06d6b06d6709d6301c6f01c6b01c6701c6303b6f03b6b03b6703b6303b5f03b5b03b5703b5301b4f01b4b01b4701b4302a6f02a6b02a6702a6302a5f02a5e01a5b01a5901a5701a5301a5201a5101a5001a4f01a4e01a4b01a4701a4301a4202a3f02a3b02a3702a330196f0196b01967019630195f0295e0195b01959019570195301952019510194f0194b0194a0194701946019430193f0193b01937019330282e01d6f01d6b01d6701d6303c6f03c6b03c6703c6303b6f03b6b03b6703b6301b5f01b5b01b5701b5303b4f03b4b03b4703b4308a6f06a6b06a6708a6301a5f03a5d01a5b01a5a01a5701a5601a5501a5302a4f02a4d01a4b01a4a01a4701a4601a4501a4401a4303a3f03a3b03a3703a33039460186f0186b01867018630185f0185b0185a0185701856018530184f0184d0184b0184a018470284601845018430183f0183b018370183301e7f01e7b01e7701e7303d7f9a57e03d7b03d7a03d7704d7603d7303d7203c7f03c7b03c7703c7301c6f01c6b01c6701c6303c5f03c5d03c5b03c5903c5703c5503c5303c5102b7f02b7e02b7b04b7a02b7702b7602b739937201b6f01b6e01b6b01b6a01b6701b6601b6301b6202b5f02b5e02b5d02b5c02b5b03b5a02b599835802b5702b5602b5502b5402b5303b5202b5103b5002b4f02b4e02b4b03b4a02b4702b4602b4303b4203a569725401a3e0197f0197b01977019730196f0196b0196a0196701966019630195f0195d0195b0195a01959019580195702956019550295401953019510194f0194b01947019430192901866018560283e9603c01d6f03d6b01d6703d6303c6fa246e03c6b03c6a03c6704c6603c6303c6203b6f03b6b03b6703b6303b5f01b5b01b5703b5303b4f03b4d03b4b03b4903b4703b4503b4303b41a026f06a6703a5f01a5703a4f03a4d03a479e24503a3f03a379b16f0196b06967019630195f0195b01957019530394f0294d0194b01949039470294501943019410393f0193b03937019330192b951270686f068670185a01857018560184701846018450383f038370181f0b81701c5f01c5b01c5701c5303b5f03b5b03b5703b5301b4f01b4b01b4701b430195f0195b01957019530194f0194b01947019430193f0193b019370193301c5f01c5b01c5701c5305b5f05b5b05b5705b5301b4f01b4b01b4701b430195f0195b01957019530194f0194b01947019430193f0193b019370193301d6f01d6b01d6701d6306c6f03c6b06c6703c6301c5f01c5b01c5701c5301a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4701a430195e0686e04866018560384e9304c07846920440182e0182601d6f01d6b01d6701c6f01c6e01c5f01c5e05b6f03b6b04b6703b6301b5f01b5b01b5701b5305b4f05b4d03b4b03b4905b4705b4503b4303b4105a6e05a4e0196f0196b01967019630195f0195b01957019530194f0194d0194b01949019470194501943019410193f0193b01937019330192501d6f01d6d01d6b01d6701d6501d6301c6f01c6e01c6d01c5f01c5e01c5701c5301c5205b6f03b6b04b6703b6301b5f01b5b01b5701b5305b4f05b4d03b4b03b4905b4705b4503b4303b4105a6f04a6701a5f01a5705a4f05a4d05a479024503a3f05a370196f0196b01967019630195f0195b01957019530194f0194d0194b01949019470194501943019410193f0193b01937019330192b019270586f0586d04867068650185f018570384f0384d05847038450383f058370181f0181703e7f03e7e03e7d01d7f01d7e01d7b04d7a01d7701d7601d7305d7201d6f01d6e01d6d01d6c01d6b07d6a01d690cd6801d6701d6601d6501d6401d6305d6201d6105d6001c7f01c7b01c7701c7301c6f01c6d01c6b01c6901c6701c6501c6301c6103b7b03b7a03b7903b7704b7603b7303b7103b6704b6603b6501b5f01b5e03b5d05b5c01b5b01b5901b5701b5501b5301b5203b5103b5001b4f01b4e01b4b01b4701b4301b4205a7f04a7705a6f07a6d07a670ca6501a5f8b25d01a5701a5501a4f01a4703a3f03a370197f0197b01977019730196f0196d0196b01969019670196501963019610195f0195d0195b01959019570195501953019510194f0194b01947019430193f0193b01937019330192b019270587f048770586f0686d06867068650185f0185e0385d0184f0184e018420383f038370181f0181701d6f01d6701d6301c6701c6601c5f01c5e05b6f03b6b04b6703b6301b5f01b5b01b5701b5305b4f05b4d03b4b03b4905b4705b4503b4303b410196f0196b01967019630195f0195b01957019530194f0194d0194b01949019470194501943019410193f0193b019370193301d7f01d7e01d7b04d7a01d7701d7601d7305d7201d6f01d6e01d6d01d6c01d6b0dd6a01d698d56801d6701d6601d6501d6401d6305d6201d6105d6001c7f01c7b01c7701c7301c6f01c6d01c6b01c6901c6701c6501c6301c6105b7f03b7b04b7703b7305b6f07b6d03b6b03b6905b6707b6503b6303b6101b5f05b5d01b5b01b5901b5701b5501b5303b5101b4f01b4b01b4701b4304a7604a6601a5e8a25c0197f0197b01977019730196f0196d0196b01969019670196501963019610195f0195d0195b01959019570195501953019510194f0194b01947019430193f0193b01937019330185e0184e03e7e03e7d01d6d01d6901d6501d6105c7e04c7a04c7605c7205c6e07c6d05c6c07c6a09c6909c6807c660cc650cc6405c6207c6105c6003b7a03b7904b7603b7104b6603b6501b5e01b5203b4d03b4903b4503b4105a7e01a5601a460196d0196901965019610194d01949019450194101c6f01c6b01c6701c6301c5f01c5d01c5b01c5701c5501c5305b6f09b6d04b6b04b6a04b6704b6606b6501b6301b5f01b5d04b5b04b5a01b5701b5601b5501b5401b5305a6f03a6b04a6703a6305a5f03a5b05a5703a5301a4f01a4b01a4701a4305a3f03a3b05a3703a330196f0196b01967019630195f0195b01957019530194f0194b01947019430193f0193b01937019330192f0192b019270192301d6f01d6b01d6701d6310c6f05c6e06c6b04c6a06c6704c6609c6305c628b36f03b6b06b6703b6301b5f01b5b01b5701b5309b4f05b4d03b4b03b4910b4705b4503b4303b418a26e01a5601a460196f0196b01967019630195f0195b01957019530194f0194d0194b01949019470194501943019410193f0193b019370193301d6f01d6b01d6701d6303c6f03c6b03c6703c6301c5f01c5b01c5705b6f05b6e06b6b04b6a06b6704b6605b6305b6201b5f01b5e01b4f01b4e0196f0196b01967019630195f0195b01957019530194f0194b01947019430193f0193d0193b019390193701935019330193101e7f01e7e01e7b04e7a01e7701e7601e7305e7201d7f01d7b01d7701d7305c7f07c7e05c7b04c7a05c7704c7605c730dc7201c6f01c6e05c6d05c6c01c6b01c6a01c6901c6801c6701c6601c6501c6401c6301c6207c618846001c5f01c5e01c5b01c5a01c5701c5601c5301c5203b7f03b7b03b7703b7301b6f03b6d01b6b01b6901b6701b6501b6303b6101b5f01b5b01b5701b5303a4e03a3e0197f0197b01977019730196f0196d0196b01969019670196501963019610195f0195b01957019530194f0194d0194b01949019470194501943019410193f0193b01937019330186e0185e01d6f01d6e01d6b04d6a01d6701d6601d638f56201c6f01c6b01c6701c638e36f03b6b06b6703b6301b5f07b5d01b5b01b5901b5701b5501b5303b5101b4f01b4b01b4701b438c26f06a6701a5f8925d01a5701a5501a4f01a4703a3f872370196f0196b01967019630195f0195d0195b01959019570195501953019510194f0194b01947019430193f0193b01937019330192b019270686f068670185f0185e0385d0184f0184e018420383f6d0370181f0181701c5f01c5b01c5701c5303b5f03b5b03b5703b5301b4f01b4b01b4701b430195f0195b01957019530194f0194b01947019430193f0193b019370193301c5f03c5b01c5703c5303b5f03b5b03b5703b5303b4f01b4b01b4703b430295f0295b02957029530294f0194b01947029430293f0293b029370293301d6f03d6b01d6703d6303c6f03c6b03c6703c6303c5f01c5b01c5703c5306a6f01a6b06a6701a6301a5f01a5b01a5701a5303a4f01a4b03a4701a43019560686e048660385e0384e038460182e8502c028268402403d6f03d6b03d6703d6305c6f05c6b04c6a05c6704c6605c6303c5f03c5e03c5b03c5703c5303c5203b6f03b6b03b6703b6303b5f03b5b03b5703b5303a4e0596f0696b06967059630395f0395b03957039530794f0594b05947079430393f0393b03937039330383603d6f03d6b03d6703d6309c6f05c6e06c6b04c6a06c6704c660cc6305c6203c5f03c5e03c5b01c5a03c5701c5603c5303c5203b6f03b6b03b6703b6303b5f03b5b03b5703b5303a4e03a3e0a96f0696b06967099630395f0395b03957039530994f0294d0994b01949099470294509943019410393f0393b03937039330a92503d6f03d6b03d6703d6303c6f03c6b03c6a03c6706c6603c6303c5f03c5e03c5b03c5703c5303c5203b6f0cb6e03b6b03b6a03b6704b6603b6303b6203b5f03b5e03b5b01b5a03b5701b5603b5303b520ca6f06a6703a5f03a5703a4f03a4d03a478224503a3f03a3d03a37812350a96f0696b069670a9630395f0395b03957039530394f0394b03947039430393f0293d0393b01939039370293503933019310a92b0a9270686f068670385f038570384a03847038460383703836078350a81f0a81705d6f03d6b06d6703d6305c6f03c6b05c6703c6303c5f03c5b03c5703c5305a6f06a6b06a6705a6303a5f0aa5b0ba5703a5303a4f05a4b05a4703a43069660394e0686e048660385e01856078460182e02826 18 262143 7 127 11 2047 20 1048575
def cc_54_5 : Nat → List (Nat × Nat) := unpackCursorV4 0x80b5e7927976a28719516998063b5e5f3485d22159d355722b52f434d05f4a22e4455d3c67f3c40236d5733d303122b2937f2682b223451be651744a15c1814319121220f32e0a74c07c2b0205c00020 0x1d7f01d7e01d7b04d7a01d7701d7601d7305d7201d6f01d6e01d6d01d6c01d6b06d6a01d6906d6801d6701d6601d6501d6401d6305d6201d6105d6001c7f01c7b01c7701c7301c6f01c6d01c6b01c6901c6701c6501c6301c6105b7f03b7b04b7703b7305b6f07b6d03b6b03b6905b6706b6503b6303b6101b5f05b5d01b5b01b5901b5701b5501b5303b5101b4f01b4b01b4701b4301a5e01a4e0197f0197b01977019730196f0196d0196b01969019670196501963019610195f0195d0195b01959019570195501953019510194f0194b01947019430193f0193b019370193304876048660185ebf05c01d7f01d7b01d7701d7301d6f01d6d01d6b01d6901d6701d6501d6301d6101c7f01c7e01c7b02c7a01c7701c7601c7302c7201c6f01c6e01c6d01c6c01c6b02c6a01c6902c6801c6701c6601c6501c6401c6302c6201c6102c6001c5f01c5e01c5d03b7f03b7b03b7703b7303b6f03b6d03b6b03b6903b6703b6503b6303b6101b5f01b5b01b5701b5301b4f02b4d01b4b01b4901b4701b4501b4302b4105a7f04a7705a6f08a6d06a6706a6501a5f01a5701a4f02a4d01a4701a4503a3f03a370197f0197b01977019730196f0196d0196b01969019670196501963019610195b0195a01959019570195601953019510194701946019450193f0193b01937019330192b019270487a04877048760486704866048650185f018570184f0284d01847018450383f038370181f0181701d6d01d6901d6501d6105c7e04c7a04c7605c7205c6e09c6d05c6c06c6a06c6906c6806c6606c6506c6405c6209c6105c6001c5a07b6d03b6906b6503b6105b4d03b4905b4503b4105a7e01a5601a460196d0196901965019610194d01925048760486605c6f08c6d04c6b04c6a04c6704c6606c6501c6301c5f01c5d04c5b04c5a01c5701c5601c5501c5401c5301b6f01b6b01b6701b6301b5f01b5d01b5b01b5701b5501b5301b4f01b4701b4305a6f03a6b04a6703a6305a5f07a5d03a5b05a5706a5503a5305a4f03a4b05a4703a4301a3f01a3b01a3701a330596f049670595f069570894f089470193f019370392f059270186f0186b01867018630185f0185d0185b0185701855018530184f01847018430183f0183b01837018330182f0182b01827018230181b0181701d7f01d7e01d7b04d7a01d7701d7601d7305d7201d6f01d6e01d6d01d6c01d6b06d6a01d6906d6801d6701d6601d6501d6401d6305d6201d6105d6001c7f01c7b01c7701c7301c6f01c6d01c6b01c6901c6701c6501c6301c6101c5f01c5e01c5d05b7f03b7b04b7703b7305b6f07b6d03b6b03b6905b6706b6503b6303b6101b5f05b5d01b5b01b5901b5701b5501b5303b5101b4f01b4b01b4701b4305a7f04a7705a6f0da6d06a6706a6501a5fbc25d01a5701a5501a4f01a4703a3f05a370197f0197b01977019730196f0196d0196b01969019670196501963019610195f0195e0195d0194f0194e0194b019490194301942019410193f0193b01937019330192b0192a01927029260487a04877048760486704866048650185f0185e0685dbb05c0185701855018520184f018470383f058370181f0181d018170281501d7f04d7b01d7705d7301d6f01d6d06d6b03d6901d6701d6505d6303d6105c7f04c7b04c7705c7305c6f07c6d05c6b03c6905c6706c6505c6303c6105c5f01c5b01c570ac5302b7f02b7e02b7b04b7a02b7702b7602b7305b7202b6f02b6e02b6d02b6c02b6b06b6a02b6906b6802b6702b6602b6502b6402b6305b6202b6105b6002b5f02b5e01b5b01b5a01b5701b5602b5303b5202b4f02b4e02b4b05b4a02b4702b4602b4303b4201a3e0297f0197b02977019730296f0296d0196b01969029670296501963019610195f0195b0b95a0195702956019530294f0194b029470194301929048760486605c6f04c6b04c6705c6305c5f01c5d06c5b03c5906c5701c5505c5303c5105b6f04b6b04b6705b6305b5f07b5d05b5b03b5905b5706b5505b5303b5105b4f0cb4b05b470cb4305a6f04a6705a5f2e25d06a5706a55c024fbe2470ca3f05a370596f0496b04967059630595f0295d0695b0195906957029550595301951bd14f0b94bba1470b9430c93f0593b059370b9330b92bb91270486a04867048660485704856048550684f068470683f058370681f0681704d6f04d6b04d6704d6304c6f04c6b04c6704c630cc5f0cc5b0cc570cc5304a6f04a6b04a6704a630ba5f0ba5b0ba570ba530ba4f0ba4b0ba470ba430496e0c946048660385e018560384e078460182e0282604c6f04c6b04c6704c6309c5f01c5d11c5b03c5911c5701c5509c5303c5104b6f04b6b04b6704b6309b5f05b5d0cb5b03b590cb5705b5509b5303b510cb4f0cb4b0cb470cb4304a6604a56b424e0ca3e0496f0496b04967049630995f0295d0995b01959099570295509953019511194f0994bad147099430c93f0993b0c93709933a912503d6f03d6e03c6b01c6703c6301c5701c5503b6f03b6b03b6703b6303b5f03b5d03b5b03b5903b5703b5503b5303b5103b4f01b4b01b4703b430496f0196b04967019630895f0295d0195b01959089570295501953019510194f0194b01947019430393f0193b039370193301c6f03c6b01c6703c6301c5f01c5d03c5b03c5a01c5709c5601c5503c5303b6f03b6b03b6a03b6704b6603b6301b5f01b5d03b5b03b5a03b5704b5601b5501b5403b5303a6f03a6b03a6703a6303a5f03a5b03a5703a5303a4f01a4b01a4703a4303a3f03a3b03a3903a3703a3303a310496f0196b04967019630995f0195b09957019530194f0194b01947019430393f0293d0193b0393702935019330392f0192b039270192301d7f01d7d03d7b03d7901d7701d7503d7303d7101d6f03d6b01d6703d6303c7f04c7e03c7db547c03c7b03c7a03c7903c7803c7704c7603c7504c7403c7303c7203c7103c7003c6f04c6e03c6b03c6a03c6704c6603c6303c6203b7f03b7d03b7b03b7903b7703b7503b7303b7103b6f03b6b03b6703b6303b5f01b5b01b5703b5303b4f03b4d03b4b03b4903b4703b4503b4303b4104a7eb427c01a5601a460497f0297d0197b01979049770297501973019710496f0196b04967019630195f0195b01957019530394f0294d0194b01949039470294501943019410393f0193b03937019330487e0486e0383601d6f01d6b01d6701c6f01c6e01c5f01c5e04b6f03b6b04b6703b6301b5f01b5b01b5701b5308b4f05b4d03b4b03b4908b4705b4503b4303b4101a5e0196f0196b01967019630195f0195b01957019530194f0194d0194b01949019470194501943019410193f0193b01937019330486e0c83601d7f01d7e01d7d01d7c01d7b04d7a01d7904d7801d7701d7601d7501d7401d7304d7201d71b257001d6f01d6e01d6b04d6a01d6701d6601d6304d6201c7f01c7d01c7b01c7901c7701c7501c7301c7101c6f01c6b01c6701c6304b7f07b7d03b7b03b7904b7704b7503b7303b7104b6f03b6b04b6703b6301b5f05b5d01b5b01b5901b5701b5501b5303b5101b4f01b4b01b4701b4301a5e01a4e0197f0197d0197b01979019770197501973019710196f0196b01967019630195f0195d0195b01959019570195501953019510194f0194b01947019430193f0193b01937019330487e0486e0c83601d7f01d7d01d7b01d7901d7701d7501d7301d7101d6f01d6b01d6701d6301c7f01c7e01c7d01c7c01c7b02c7a01c7902c7801c7701c7601c7501c7401c7302c7201c7102c7001c6f01c6e01c6b02c6a01c6701c6601c6302c6201c5f01c5e01c5d03b7f03b7d03b7b03b7903b7703b7503b7303b7103b6f03b6b03b6703b6301b5f01b5b01b5701b5301b4f02b4d01b4b01b4901b4701b4501b4302b4104a7f11a7d04a7704a7504a6f04a6701a5f01a5701a4f02a4d01a4701a4503a3f03a370197f0297e0197d0297c0197b019790197701975019730197201971019700196f0196b01967019630195b0195a01959019570195601953019510194701946019450193f0193b01937019330192b019270487f0487e0687d0486f0486e048620185f018570184f0284d01847018450383f0383a03837038360181f0181709a540292401d6f01d6b01d6701d6301c6f01c6e01c6701c6301c6201c5f01c5e01c5b01c5a01c5701c5601c5301c5204b6f03b6b04b6703b6301b5f01b5b01b5701b5308b4f05b4d03b4b03b4908b4705b4503b4303b4104a6f04a6701a5f01a57af24f09a4d1aa4709a4503a3f08a370196f0196b01967019630195f0195e0195b0195701953019520194f0194d0194b01949019470194501943019410193f0193b01937019330192b0192a01927029260486f0486e01867048620185f018570684f0584d01847018450383f0683a068370c8360181f0181d018170281501d7e04d7a01d7604d7201d6e01d6d01d6c09d6a01d6916d6801d6601d6501d6409d6201d6109d6001c6d01c6901c6501c6101c5e01c5d05b6d03b6905b6503b6105b5d01b5901b5503b5104a7604a6601a5e09a5c01a4e03a3e0196d0196901965019610195e0195d0194e019490194201941019250292401d7d01d7901d7501d7104c7e09c7d10c7c04c7a04c7904c7804c7604c7504c7404c7209c7109c7004c6e04c6a04c6604c6201c5a07b7d03b7904b7503b7105b4d03b4905b4503b4104a7e09a7c04a6e01a5601a460197d0197901975019710194d019250487e0486e0c83601d7f01d7e01d7d01d7c01d7b04d7a01d7904d7801d7701d7601d7501d7401d7304d7201d71ae57001d6f01d6e01d6b04d6a01d6701d6601d6304d6201c7f01c7d01c7b01c7901c7701c7501c7301c7101c6f01c6b01c6701c6301c5f01c5e01c5d04b7f07b7d03b7b03b7904b7704b7503b7303b7104b6f03b6b04b6703b6301b5f05b5d01b5b01b5901b5701b5501b5303b5101b4f01b4b01b4701b4304a7fad27d04a7704a7504a6f04a6701a5fac25d01a5701a5501a4f01a4703a3f08a370197f0197d0197b01979019770197501973019710196f0196b01967019630195f0195e0195d0194f0194e0194b019490194301942019410193f0193b01937019330192b0192a01927029260487f0487e0687d0486f0486e048620185f0685d01857018550184f018470383f0683a068370c8360181f0181d018170281501d6f04d6b01d6704d6304c6f04c6b04c6704c630cc5f01c5b01c570ac5302a6f02a6e0ea5f03a5e01a5b01a5a01a5701a560ea5303a520aa4f03a4e0ca4b05a4a0ca4705a460aa4303a420296f0196b029670195f0195b01957019530294f0194b02947019430192b0192901c6f04c6b01c6704c6301c5f09c5b01c5709c5304b6f04b6b04b6704b6309b5f09b5b09b5709b530cb4f01b4b01b470ab4302a6f02a6b04a6a02a6702a6602a6302a5f02a5b04a5a01a5901a5802a5702a5601a5301a5102a4f02a4e01a4b01a4702a4303a4202a3f02a3e02a3b02a3702a3303a320296f0196b02967019630295f0195b0995a01959029570295601953019510194f0194b0994a0194702946019430293f0193b029370193301d7f01d7d04d7b03d7901d7701d7504d7303d7101d6f04d6b01d6704d6304c7f07c7d04c7b03c7904c7704c7504c7303c7104c6f04c6b04c6704c630cc5f01c5b01c570ac5302b7f02b7e02b7d02b7c02b7b04b7a02b7904b7802b7702b7602b7502b7402b7304b7202b71aa37002b6f02b6e02b6b04b6a02b6702b6602b6304b6202b5f02b5e01b5b01b5a01b5701b5602b5303b5202b4f02b4e02b4b05b4a02b4702b4602b4303b4204a7ea927c01a3e0297f0297e0297d0297c0197b019790297702975019730497201971019700296f0196b02967019630195f0195b0b95a0195702956019530294f0194b0294701943019290487e0486e0c84604c6f01c6d04c6b03c6904c6701c6504c6303c6104c5f04c5b04c5704c5304b6f07b6d04b6b03b6904b6704b6504b6303b6104b5f04b5b04b5704b530cb4f0cb4b0cb470cb4304a6fb626d04a6704a6504a5f04a57b324fb12470ca3f0ca370496f0296d0496b01969049670296504963019610495f0495b0495704953b014f0b94bab1470b9430c93f0b93b0c9370b9330b92ba81270486f0486e0686d0485f0485e048520684f068470683f0683a068370c8360681f0681703c5f03c5b03c5703c5303b5f03b5b03b5703b5303b4f03b4b03b4703b430595f0495b04957059530394f0394b03947039430393f0393b039370393305c5f04c5b04c5705c5305b5f04b5b04b5705b5305b4f07b4b05b4707b430595f0495b04957059530b94f0b94b0b9470b9430793f0593b05937079330485605d6f04d6b04d6705d6305c6f04c6b04c6705c6305c5f0cc5b05c570cc5305a6f04a6b04a6705a630ba5f0ba5b0ba570ba530ba4f05a4b05a470ba43049660686e0385e018560384ea604c07846a50440182e0282603d6f03d6e03c6b01c6703c6301c5701c5503b6f03b6b03b6703b6303b5f03b5d03b5b03b5903b5703b5503b5303b5103b4f01b4b01b4703b4305a6e05a5e01a460596f0196b04967019630995f0295d0195b01959099570295501953019510194f0194b01947019430393f0193b039370193303d6f03d6e03d6d01c6f03c6b03c6901c6703c6303c6101c5f01c5d03c5b01c5701c5503b6f03b6b03b6703b6303b5f03b5d03b5b03b5903b5703b5503b5303b5103b4f01b4b01b4703b4305a6f04a6705a5f05a5d05a57a325503a4f01a4703a3f03a370596f0196b04967019630595f0295d0195b01959059570295501953019510194f0194b01947019430393f0193b03937019330192b9a1270586f0586d04867068650185f0185d05857018550384f018470383f038370181f0681703d6f03d6d01c6f01c6d01c5f03c5b03c5303b6f03b6d03b6b03b6903b6703b6503b6303b6103b5f03b5b03b5703b5303b4f01b4b01b4703b431196f0296d0196b01969119670296501963019610595f0195b04957019530194f0194b01947019430393f0193b039370193301d7f03d7b01d7703d7301d6f01d6d03d6b03d6901d6701d6503d6303d6103c7f05c7e03c7b03c7a03c7704c7603c7303c7203c6f05c6e03c6d05c6c03c6b03c6a03c6903c6803c6711c6603c65a146403c6303c6203c6103c6003b7f03b7b03b7703b7303b6f03b6d03b6b03b6903b6703b6503b6303b6103b5f01b5b01b5703b5303b4f03b4d03b4b03b4903b4703b4503b4303b4104a7604a660597f0197b04977019730596f0296d0196b01969099670296501963019610195f0195b01957019530394f0294d0194b01949039470294501943019410393f0193b0393701933018560184605e7e09e7d05e7c04e7a04e7606e7506e7406c7e09c7d04c6e04c6d04c6c03c5e03b6d03b6903b6503b6103b4d03b4903b4503b4103a6e03a5e0996d0196909965019610294d01949029450194109925 20 1048575 8 255 11 2047 20 1048575
def cc_54_6 : Nat → List (Nat × Nat) := unpackCursorV4 0x9992694d4c9034a8b64d833837e64d78e587612d6db8665e7d60f4f5927d55c3650f4d4e62945f874203f3f12f3a34e33d663112c2a968243662172c1af681703f13b350f14a0bf3209f200435c00043 0x4d6f04d6e05d6d01c6f01c6b01c6701c6301c5f01c5b01c5701c5304b6f04b6b04b6704b6305b5f05b5b05b5705b5301b4f01b4b01b4701b4304a6e0196b01969019670196301961019570194f0194b01947019430193f0193b019370193301d6f01d6e01d6d01c6f01c6b01c6701c6301c5f01c5d01c5b01c5901c5701c5501c5301c5105b6f04b6b04b6705b6305b5f05b5d05b5b03b5905b5705b5505b5303b5101b4f01b4b01b4701b4305a6f05a6d04a67de26502a5f02a5d05a5702a5501a4f01a4705a3f05a370196f0196b019690196701963019610195f0195d0195b01957019550194f0194b01947019430193f0193b01937019330192b019270586f048670585f0585d058570b8550184f018470583f058370181f0181701d6f01d6b01d6701d630ac6f0ac6b0ac670ac6301c5f01c5b01c5701c53e036fdf36701b5f01b570ab4f0ab4701a6f01a6b01a6701a6301a5f01a5b01a5a01a5701a5601a5301a4f01a4b01a4701a4301a3d01a3701a350196fdd16e0196b0196a019670496601963019620195f0195e0195b0195a019570195601953019520194f0394e0194b0194a019470794601943019420193702936019350b86f0b8670185f018570a84f0a8470182f018270181f0181d018170b81501d6f01d6b01d6701d6303c6f03c6b03c6703c6301c5f01c5b01c5701c5304b6f04b6701b5f01b5703b4f03b4702a6f02a6e01a6b01a6a01a6701a6601a6301a6201a5f01a5e01a5b01a5a01a5701a5601a5301a5203a4f03a4e03a4b03a4a03a4703a4603a4303a4201a3b01a3a01a3701a360196f0196b01967019630195f0195b01957019530194f0194b01947019430193b019370192b019290192701923019210486f048670185f018570384f038470682f0682d06827068250181f0181701e7f01e7e01e7d01e7701e7501e7303e7201d7701d7601d7501d6f01d6e03d6d03c7f03c7b03c7703c7301c6f01c6b01c6701c6303c5f03c5d03c5b03c5903c5703c5503c5303c5102b7f02b7e02b7b04b7a02b7904b7802b7702b7602b7304b7202b71ce37001b6f01b6e01b6b01b6a01b6701b6601b6301b6202b5f02b5e02b5d02b5c02b5b03b5a02b59db35802b5702b5602b5502b5402b5303b5202b5103b5002b4f02b4e02b4b03b4a02b4702b4602b4303b4204a7f04a7701a6f01a6703a5f03a5d03a5709a5503a4f03a4701a3f01a3e01a3d0197f0197b01977019730196f0196b0196a0196701966019630195f0195d0195b0195a01959019580195702956019550295401953019510194f0194b01947019430192b01929019210487f048770186f018670385f0385d03857068550384f038470283f0683d02837028350181f0181701d6f01d6b01d6701d6303c6f03c6b03c6703c6301c5f01c5b01c5701c5305b6f04b6701b5f01b5703b4f03b4701a6f01a6e01a6b01a6a02a6702a6601a6301a6201a5f01a5e01a5b01a5a01a5701a5601a5301a5203a4f03a4e03a4b03a4a03a4703a4603a4303a4201a3b01a3a01a3701a360196f0196b01967019630195f0195b01957019530194f0194b01947019430193b019370192b019290192701923019210586f048670185f018570384f038470e82f0882d0e827088250181f0181701d6f01d6b01d6701d6301c6f01c6701c6301c5f01c5701c5303b6f03b6b03b6703b6301b5f01b5b01b5701b5303b4f03b4b03b4703b4302a6f02a6e02a6b02a6901a6702a6305a6202a6105a6001a5f01a5e01a5b01a5701a5301a5202a4f02a4e01a4b01a4901a4701a4301a4201a4101a4002a3f02a3b03a3a02a3702a3602a330196f0196b01967019630195f0195b0195a0195701956019530194f0294e0194b01949019470194301942019410193f0193b01937019330586f048670185f018570984f098470383f038370282f0882d02827028250181f0181701d7e01d6e03c5d03c5903c5503c5102b7e04b7a02b7605b7201b6e01b6a01b6601b6202b5e02b5d02b5c08b5a02b5908b5802b5602b5502b5413b5202b510eb5002b4e03b4a02b4603b4201a3e0196a019660195d019590195501951019290587e0186e0385e0384602836028340181601e7f01e7d01e7b03e7a01e7701e7601e7501d7f01d7e01d7d01d6f01d6e03d6d03c7f03c7b03c7703c7301c6f01c6b01c6701c6303c5f03c5d03c5b03c5903c5703c5503c5303c5102b7f02b7e02b7b04b7a02b7904b7802b7702b7602b7305b7202b7105b7001b6f01b6e01b6b01b6a01b6701b6601b6301b6202b5f02b5e02b5d02b5c02b5b03b5a02b59d935802b5702b5602b5502b5402b5303b5202b5103b5002b4f02b4e02b4b03b4a02b4702b4602b4303b4205a7f04a7701a6f01a6703a5f03a5d03a5a03a5703a5609a55d825403a4f03a4701a3f01a3e01a3d0197f0197b01977019730196f0196b0196a0196701966019630195f0195d0195b0195a01959019580195702956019550295401953019510194f0194b01947019430192b01929019210587f048770186f018670385f0385d03857d70550384f038470283f0883d02837028350181f0181703e7f03e7e03e7d01d7f03d7b01d7703d7301d6f01d6d03d6b03d6901d6701d6503d6303d6103c7b04c7a03c7904c7704c7603c7303c7104c6704c6604c6503c5f07c5e01c5b01c5703c530ac5202b7f02b7e02b7b04b7a02b7702b7602b7305b7202b6f02b6e02b6d02b6c02b6b07b6a02b690cb6802b6702b6602b6502b6402b6305b6202b6105b6002b5f02b5e01b5b01b5a01b5701b5602b5303b5202b4f02b4e02b4b05b4a02b4702b4602b4303b4205a7f04a7705a6f07a6d07a6709a6503a5f01a5703a4f05a4701a3f01a3e01a3d0297f0197b02977019730296f0296d0196b01969029670296501963019610195f0195b0a95a0195702956019530294f0194b02947019430192b01929019210587f048770586f0786d078670c8650385f018570384f058470283f0883d02837028350181f0281701d6f03d6b01d6703d6304c6f03c6b02c6703c6303c5f01c5b01c5703c5304b6f04b6703b5f01b5703b4f05b4702a6f02a6e03a6b03a6a02a6702a6602a6302a6203a5f03a5e01a5b01a5a01a5701a5603a5303a5202a4f02a4e05a4b05a4a02a4702a4602a4302a4201a3b01a3a04a3701a360296f0196b02967019630195f0195b0a95a0195702956019530294f0194b02947019430193b029370192b019290292701923019210486f048670385f018570384f058470682f0682d06827068250181f0281703e7f03e7e03e7d01d7f01d7d03d7b03d7901d7701d7503d7303d7101d6f03d6b01d6703d6304c7f04c7e07c7d04c6f04c6e03c6b03c6903c6304c6203c6103c5f01c5b01c5703c5302b7f02b7e02b7d02b7c02b7b04b7a02b7904b7802b7702b7602b7502b7402b7304b7202b71d437002b6f02b6e02b6b04b6a02b6702b6602b6304b6202b5f02b5e01b5b01b5a01b5701b5602b5303b5202b4f02b4e02b4b05b4a02b4702b4602b4303b4204a7f09a7d04a7704a7504a6f04a6703a5f01a5703a4f05a4701a3f01a3e01a3d0297f0297d0197b01979029770297501973019710296f0196b02967019630195f0195b0a95a0195702956019530294f0194b02947019430192b01929019210487f0687d04877048750486f048670385f018570384f0684d05847068450283f0683d02837028350181f0281703e7e03e7d01d7901d7101d6d01d6901d6501d6103c7d03c7501c6d03c6901c6501c6102b7e04b7a02b7605b7202b6e02b6d02b6c05b6a02b690eb6802b6602b6502b6405b6202b6105b6001b5e01b5a01b5601b5202b4e03b4a02b4603b4205a6d09a6501a3e01a3d0196d0196901965019610195a0195601929019210586d138650883d0283501d6f01d6b01d6701d6303c6f03c6b03c6703c6301c5f01c5b01c5701c5305b6f0cb6701b5f01b5703b4f03b4705a6f05a6e0ca6b04a6a0ca6704a6605a6305a6201a5f01a5e01a5b01a5a01a5701a5601a5301a5202a4f02a4e01a4b01a4a01a4701a4601a4301a4201a3b01a3a01a3701a360196f0196b01967019630195f0195b01957019530194f0194b01947019430193b019370192b019290192701923019210586f0c8670185f018570384f038470e82f0882d0e827088250181f0181705d7e04d7a04d7605d7201d6e01c5502b7e04b7a02b7605b7201b6e01b6a01b6601b6202b5e02b5d02b5c08b5a02b5908b5802b5602b5502b5413b5202b510eb5002b4e03b4a02b4603b4201a3e0196a019660195d019590195501951019290186e0385e0384601e7f01e7b01e7701e7303d7fd257e03d7b03d7a03d7704d7603d7303d7201d6f01d6e03d6d03c7f07c7e03c7b03c7703c7303c7201c6b01c6a01c6901c6701c6601c6303c6101c5701c5601c5502b7f02b7e02b7b04b7a02b7702b7602b7305b7201b6f01b6e01b6b01b6a01b6701b6601b6301b6202b5f02b5e02b5d02b5c02b5b03b5a02b59d135802b5702b5602b5502b5402b5303b5202b5103b5002b4f02b4e02b4b03b4a02b4905b4802b4702b4602b4303b4202b4103b4005a7f0ca7701a6f01a6703a5f03a5d03a5709a5503a4f03a4701a3f01a3e01a3d0197f0197b01977019730196f0196b0196a0196701966019630195f0195d0195b0195a01959019580195702956019550295401953019510194f0194b01947019430192b01929019210587f0c8770186f018670385f0385d03857d00550384f0384d03847078450283f0883d02837028350181f0181701d6f01d6e03d6d01c6f01c6b01c6701c6303c5f03c5b03c5703c5301b6f01b6703b5f03b5d03b5709b5503b4f03b4701a6f01a6b01a6a01a6701a6601a6303a5703a5605a5503a4f03a4b03a4703a4301a3b01a370196f0196b01967019630195f0195d0195b0195701955019530194f0194b01947019430193b019370192b01927019230186f018670385f038570384f038470582f058270181f0181701d6f04d6b01d6705d6305c6f04c6b04c6705c6305c5f01c5b01c5705c5302a6f02a6e08a5f03a5e01a5b01a5a01a5701a5608a5303a5205a4f03a4e05a4b05a4a05a4705a4605a4303a420296f0196b029670195f0195b01957019530294f0194b02947019430192b019290586e01856058460582e01d6f04d6bce56901d6705d6305d6105c6f04c6b04c6705c6305c5f01c5b01c5705c5305b6f05b6d04b67ca36514b5f01b5705b4f05b4702a6f02a6e02a6d05a5f03a5e01a5b01a5a01a5701a5605a5303a5205a4f03a4e05a4b05a4a05a4705a4605a4303a4201a3b01a3a05a3701a360296f0296d0196b0296702965019630195f0195b01957019530294f0194b02947019430193b029370192b019290292701923019210586f048679905f018570584f058470582f0582d05827cd0250181f0281701d7f04d7b01d7705d7301d6f01d6d09d6b03d6901d6701d6505d6303d6105c7f04c7b04c7705c7305c6f07c6d05c6b03c6905c6707c6505c6303c6105c5f01c5b01c570ac5302b7f02b7e02b7b04b7a02b7904b7802b7702b7602b7305b7202b7105b7002b6f02b6e02b6d02b6c02b6b04b6a01b6901b6802b6702b6602b6502b6401b6301b6201b6101b6002b5f02b5e01b5b01b5a01b5701b5602b5303b5202b4f02b4e02b4b05b4a02b4702b4602b4303b4204a7604a6601a3e0297f0197b02977019730296f0296d0196b0996a01969019680296702966029650296401963019610195f0195b0995a0195702956019530294f0194b02947019430192901d6f04d6b03d6901d6704d6303d6104c6f04c6b04c6704c6305c5f01c5b01c5705c5304b6e01b5605b4604a6f04a6e05a6d05a5f01a5b01a5705a5305a4f05a4b05a4705a4301a390296f0296d0196b02967029650195f0195b01957019530294f0194b0294701943019390192b01d7f01d7d04d7b03d7901d7701d7504d7303d7101d6f04d6b01d6704d6304c7f07c7d04c7b03c7904c7704c7504c7303c7104c6f04c6b04c6704c630cc5f01c5b01c570ac5302b7f02b7e02b7d02b7c01b7b01b7a01b7901b7802b7702b7602b7502b7402b7304b7201b7101b7002b6f02b6e02b6b04b6a02b6904b6802b6702b6602b6304b6202b61ca36002b5f02b5e01b5b01b5a01b5701b5602b5303b5202b4f02b4e02b4b05b4a02b4702b4602b4303b4204a7e04a6e01a5609a4601a3e0297f0297e0297d0297c0197b019790297702975019730497201971019700296f0196b02967019630195f0195b0995a0195702956019530294f0194b02947019430192901e7f01e7b01e7701e7303d7f14d7e03d7b03d7a03d7704d7603d7303d7203c7f03c7b03c7703c7301c6f01c6b01c6701c6303c5f03c5d03c5b03c5903c5703c5503c5303c5102b7f02b7e02b7b04b7a02b7702b7602b7314b7201b6f01b6e01b6b01b6a01b6901b6801b6701b6601b6301b6202b6103b6001b5f01b5e01b5d01b5c01b5b01b5a01b5901b5801b5701b5601b5501b5401b5301b5201b5101b5002b4f02b4e02b4b03b4a02b4702b4602b4303b4201a6601a5601a3e0197f0197b01977019730196f0196b0196a0196701966019630195f0195d0195b0195a01959019580195702956019550295401953019510194f0194b01947019430192905d7d05d7505c7e05c7d03c6e01c6a01c6603c6203c5e02b7e04b7a02b7605b7202b6e01b6a01b6603b6202b5e05b5a02b5603b5202b4e02b4d02b4c05b4a02b490eb4802b4602b4502b4405b4202b4105b4004a7605a4603a4401a3e0996a029660294d0194902945019410192901e7f03e7b01e7703e7305d7f07d7e05d7b04d7a05d7704d7605d73c757203d6f03d6e01d6b01d6a01d6701d6603d6303d6205c7f03c7b05c7703c7303c6f01c6b01c6703c6302b7f02b7e02b7b04b7a02b7702b7602b7305b7202b6f02b6e01b6b01b6a01b6701b6602b6303b6202b5f02b5e02b5d02b5c01b5b01b5a01b5901b5802b5702b5602b5502b5402b5303b5201b5101b5002b4f02b4e02b4b05b4a02b4905b4802b4702b4602b4303b4202b4103b4009a7601a6603a5e03a4e01a3e0297f0197b02977019730196f0196b0996a0196702966019630295f0295e0295d0295c0195b019590295702955019530795201951019500294f0194b02947019430192901d6f01d6b01d6701d630ac6f03c6b0ac6703c6301c5f01c5b01c5701c5302b6f02b6b02b6702b6301b5f01b5e01b5b01b5701b5301b5202b4f02b4b02b4702b4309a6f09a6701a5f01a5703a4f09a4701a3f01a3e01a3d0196f0196b01967019630195701956019550194f0194b01947019430193f0293e0193d0192b019270b86f0b8670185f018570384f0a8470283f0b83d02837028350181f0181701d6f06d6b01d6708d6308c6f06c6b06c670ac6308c5f01c5b01c5708c5309b6f05b6e06b6b04b6a06b6704b6608b6305b6208b5f03b5e01b5b01b5a01b5701b5608b5303b5208b4f03b4e08b4b05b4a08b4705b4608b4303b420296f0196b02967019630195f0195b0b95a0195702956019530294f0194b02947019439605e028360281601d6fda56b01d67d6563d546f0ac6bd34670ac63cf45f01c5b01c570ac5302b6f02b6e02b6b04b6a02b6702b6602b63cc36202b5f02b5e01b5b01b5a01b5701b5602b5303b5202b4f02b4e02b4b07b4a02b4702b4602b4303b42cb26fc9267c825f01a570aa4fc624701a3f01a3e01a3d0296f0196b02967019630195f0195bc515a0195702956019530294f0194b02947019430192b0192901921b906fa80679505f018570a84f6e0470283fc403d02837028350181f0281701c6f01c6b01c6701c6301c5f01c5d01c5b01c5901c5701c5501c5301c5105b6f04b6b04b6705b6305b5f05b5d05b5b03b5905b5705b5505b5303b5101b4f01b4b01b4701b430196f0196b019690196701963019610195f0195d0195b01959019570195501953019510194f0194b01947019430193f0193b019370193301d6f01d6b01d6701d630ac6f0ac6b0ac670ac6301c5f01c5b01c5701c5301a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a35c216e049660195e019560394e079460192e01d7f03d7b01d7703d7301d6f01d6d03d6b03d6901d6701d6503d6303d6103c7f05c7e03c7b03c7a03c7704c7603c7303c7203c6f05c6e03c6d05c6c03c6b03c6a03c6903c6803c6706c6603c6506c6403c6303c6203c6103c6003b7f03b7b03b7703b7303b6f03b6d03b6b03b6903b6703b6503b6303b6103b5f01b5b01b5703b5303b4f03b4d03b4b03b4903b4703b4503b4303b4101a5601a460597f0197b04977019730596f0296d0196b01969069670296501963019610195f0195b01957019530394f0294d0194b01949039470294501943019410393f0193b0393701933048760486605c6f08c6d04c6b04c6a04c6704c6606c6501c6301c5f01c5d04c5b04c5a01c5701c5601c5501c5401c5301b6f01b6b01b6701b6301b5f01b5d01b5b01b5701b5501b5305a6f03a6b04a6703a6305a5f07a5d03a5b05a5706a5503a5305a4f03a4b05a4703a4301a3f01a3b01a3701a330186f0186b01867018630185f0185b018590185701853018510184f0184b01847018430183f0183b01837018330182f0182b0182701823 20 1048575 8 255 11 2047 20 1048575
def cc_54_7 : Nat → List (Nat × Nat) := unpackCursorV4 0x858d305ca9f66abc255723c2deab9aa26b3d2e627a6b8d855da8287e74c29a8c38500309d6d334cc2642acb91e95e28291564a4fc84df8f42b1a78231278579588fbf0ed6419a8019b380066 0x1d6f00eb70075b4038de01c6b00e3480719c038c601c6100e2f807174038b601c5900e2b807154038a601c5101db780edb4076d603b6701db280ed8c076be03b5d01dad80ed64076ae03b5501da980ed440369e01b4b00da3806d0c0b4de04a6b0253381698c0b4be05a5d02d2d81695dfe4aa05a5300d2780692c0348e01a4301d1f80e8ec0746e03a3300cb78065ac032d20196700cb1806584032be0195d00cad806564032ae0195500ca98065440329e0194b00ca380650c0327e0193b00c9b8064cc0325e0192b00c9380648c0b0de0486b0243381618c0b0be0585d02c2d81615c170aa0585300c2780612c0308e0184301c1f80e0ec0706e0383305c1781a0ac1704e0682300c0f80606c0302e0181300eb78075ac03ace01d6301e3780f1ac078ce03c6300e2f80716c038ae01c53025b7812db8036d604b67025b1812d88036be03b4f01da580ed1c0768604a6600d2f00e9181b47c0196f00cb580659c032c60195f00cad806568032ae0195600ca780652c0328e0194300c9d8064a4038de01c6b00e3480719c038c601c6100e2f80716c038ae01c5301db780edb4076d603b6701db280ed8c076be03b5b01dab80ed4c0369e01b4b00da3806d0c094de04a6e00d358069a4034ce01a6300d31006984034c004a5f0252f01296c094b201a5702529812948134a201a4f00d2380690c0747e03a3b01d1b80e8cc032de0496e00cb58065a4032ce0196300cb1006584032be0195b00cab80654c0329e0194b00ca500651c0328c0194300c9f8064ec0326e0193300c9580649c032460486f0243381217c090ae0184f00c2380e0fc0706e0682f0341380607c0302e01d6f00eb580759c03ac603c6f01e3580f19c078c601c5f00e2d80715c038a609b6f02db703adac096d409b67025b303ad8c0b6c401b5f00daf006d5c036a601b5201da780ed380769603b4a01da380ed180768603b4204d37bf49a8134cefc26600d2f806978034ae01a5201d2780e9280748e03a4600d1f8068f80347a0196f00cb580659c032c60195f00cad806568032ae0195600ca980653c032960194700ca18064ec032720193700c998064c4032560192900c93806484170de0b86700c2f80615c0709e0384704c1f82e0f41306e0b83505c1482e0840303e0181700eb78075ac03ace01d6301e3780f1ac078ce03c6300e2f80716c038ae01c53831b7c10dae046cf0036300daf806d6c036ae01b5301da780ed2c0768e03b4300d378069ac034ce01a6300d2f806974034b601a5a00d2b806958034aa01a4f00d2580691c0348601a3f00d1d8068dc034660196f7f0b70065ac032d401967024b300658c032c40195f00caf0065740329e0394e00ca58065280328e0394600ca18065080327e0193b00c9d0064ddf626c0193300c978064b80325a0b86f05c3582e19c170c60185f00c2d80615c030a60384f01c2580e11c070860b83f05c1d82e0dc170660182f00c1580609c030460181f00c0e80606c0302e0b81500c098075bc07ad601d6701eb18231bc0b8dc06c6b0263501b19c098cc08c6302e3100f17c078bc01c5b00e2d00715c038ac03c5301e2900edbc076d603b6701db180ed7c036b601b5701da980ed2c076920296f00cb580a59c032c60195f00cad80655c032a602947014a28064ec0526e01933044370221180706c01d6f01eb580759c07ac609c6f02e370331ac098d409c670263303318c0b8c403c5f01e2f00716c038b401c5700e2b00f14c078a403b6f01db580ed9c076c603b5f00dad806d5c076a601b4b00da480ed1c0768601b4104d3782699c074be01a570152780a9380549a03a3f01d1f00e8dc074640296f00cb580a59c032c60195f00cad80655c032a60294f014a680652c0528e029450149f8064ec0526e01933014968064ac0524e029250643783219c070be0185704c27be41341308e2704501c1f80e0dc0303e0281700eb780f5ac03ace03d6301e3780f1ac078ce03c6301e2f80716c038ae03c5304db7816db80d6d604b6a035b3812d98136c605b6201daf80ed78036b601b5a00dab806d58076a603b5201da780ed38134dc03a460451b00a5bc032d60296700cb180657c032b60195700ca980652c0528e019430149b80a4d403ade03d6b00eb380f58c078de03c6b01e3380f18c078be01c5b00e2b80f14c116de05b6e035b5812da80d6ce04b66065b1816d88076be03b5e00dad806d68036ae01b5601da980ed480369e01b4e01da380ed0c036840ca6f0353380e97c034ae03a4f01d2383e8fdee47a08a371391a80a5bc032d60296700cb180657c032b60195700ca980a53c032960294700ca180a4fc0527a0193b0149b80a4d403256029270343782e1a80d0ce0c86601c2f80e178030ae0385201c2780e1380708e038420141f80a0f80507a0b82a1301300607c05034028170140b0075bc07ad601d6701eb180f1bc078d603c6701e3180f17c038b601c5701e2980adbc196dc02b6b015b500ad9c096cc02b63015b100ad7c076bc01b5b00dad006d5c036ac02b53015a9006d3c0369c01b4d065378329ac194ce0ca6301d2f80696c034ae03a5301d2780e92c0748e03a430151f80a8f40547602a377c11a80a8cc052de0196b014b380658c032be0195b00cab80654c032960394a00ca480a51c0528c0194300ca080a4dc0526c02935014978064ac0524e019230643782e1ac190ce0b86301c2f80616c030ae0385301c2780e12c0708e038430141f80a0f405076028377b01a80a0cc9c05e0b82b1281382e08c0303e0281b0140b80604c03ad601d6900eb380758c03ac201c6f00e368071ac038d201c6700e3280718c038c201c5f00e2d80715c038a605b6f02db680edac076d205b6702db280ed8c076c205b5f01dad812d5c076a601b4f00da5806d1c0368605a6f02d370169b40b4be05a5e00d2b8169480349e01a4701d1f8168dc032de0196d00cb58065a4032ce0196500cb1806584032be0195b00cab80654c0329e0194b00ca380650c0327e0193b00c9b8064cc0325a0192b00c93806494130de0886d04c338221940b0be0485700c2780611c0707e0583700c0f80605c03ade01d6e00eb68071bc038d601c6700e3180717c038ba01c5b00e2c80715c038aa01c5300e28816dbc0b6da03b6b025b3816d94076c602b5f015ae80ed6c076b205b57015aa80ed4c076a201b4f00da5806d1c0368605a6f0253581299c0b4c605a5f02d2e81696c0b4aef425502d2980693c0349601a4700d2180e8fc0b47605a3701d198065bc032d60196900cb380658c032c20195f00cae80656c032b20195700caa80654c032a20194f00ca580651c032860193f00c9d8064dc032660192f00c9580649c032460586f0243581219c0b0c60585f02c2e81616c0b0ae0b85502c2980613c030960184700c2180e0fc0b0760583701c1982e0bc0d0560b8270341180607c030360181700c098075bc03ad601d6700eb18171bc078d605c6701e3180717c038b601c5700e29816dbc0b6dc0cb6b025b5026d9c096cc05b6302db1006d7c036bc01b5b00dad006d5c036ac01b5300da900ed3c0b69602b4a015a380ad180b4de09a6700d2f80695c0749e05a4a02d238169180347e01a3e00d1e8065bc032d60196700cb180657c032b60195700ca980653c032960194700ca18064ec032720193700c998064c4032560192900c938064840b0de0b86700c2f80615c0709e0584704c1f82e0f41306e0b83500c0f80605c03ade01d6b00eb380758c0b8de03c6b02e3380f18c038be01c5b00e2b80714c0b6de0cb6b065b3816d8c036be01b5b00dab806d4c0769e05b4b02da380ed0c034de01a6b00d3380698c034be01a5b00d2b80694c0349e03a4e00d2680691c0348a01a4300d210068fc0347601a3700d198065bde62dc0196b00cb500659c092cc0196300cb100657c032bc0195b00cad00655c032ac0195300ca900651c0528c0194500c9f8064ec03274019377909b0064cc0325e0192e00c968161bc170d60b86702c3180617c030b60185700c2980e13c0b0960584701c2182e0fc170760b83705c198060bc030560182700c1180607c0303a0181b00c0b82e0540302601d6f01eb580759c07ac602c6f0163700b1ac098d402c670163300b18c158c402c5f0162f00716c038b401c5700e2b00b14c078a405b6f01db5816d9c076c603b5f00dad806d5c076a601b4f00da7006d340b4de0ca6b0653381698c074be01a5b00d2b80e94c0549e0aa4d0152580a91c0548a02a4301d1f8168ec0b46e03a33014b78065ac052ce0196300caf80656c032ae01953014a780a5380529a0293f0149f0064ec032720193301c990064c40525e0192b0149380648c0b0de0b86b0643381618c070be0185b00c2b80e14c0509e0a84d0142580a11c0508a0284301c1f8160ec0b06e038332681782e0ac4804e0b82300c0f80a06c0502e0181300eb78075ac03ace01d6301e3780f1ac078ce03c6300e2f80716c038ae01c5304db7816db8196d604b6a04db3812d98196c605b6200daf806d78036b601b5a00dab806d58036a601b52015a780ad380768e03b43015a10269bc194d409a670653300697c034b401a5700d2b00e93c0749c03a4701d210068fc0347c01a3d00cb78065ac032ce0196300caf80656c032ae0195300ca780652c0328e0194300c9d8064e40326e0193300c988064ac032520192700c9082e1bc170ce0185f00c2b80e13c0708e0983f05c1e8260dc1706a0b82905c1080607c0302e01d6f00eb580759c03ac603c6f01e3580f19c078c601c5f00e2d80715c038a60cb6f065b5832d9c196c601b5f00dad806d5c036a603b4f01da580ed1c0768601a6f00d3580699c034c601a5f00d2d80695c034a601a4f00d2680692c0349401a4701d230069140347e01a3b00d1b8068cc032de0c96e00cb58065a8032ce0496600cb1806588032be0195e00cad806568032ae0195600ca98065480329e0294e00ca68064fc032760193a00c9bbbc4d8032660192f00c970064b4170de0b86b05c3382e18c030be0185b00c2b80614c0709e0384b01c2380e10c1707e0b83b05c1b82e0cc0305e0182b00c1380608c0303e0181d00c0d80605c1702a0181300eb780759c03ac601c6700e3300717c038bc03b6f01db580ed9c076c601b5f00dad806d5c036a603b4f01da680ed2c0769203b4701da280ed0c076820196f00cb580659c032c60195f00cad80655c032a60194f00ca680652c032920194700ca280650c032820193f00c9d8064dc0326601e7f00f3f0079f403cee01e7500f3980f9c803aee01d7600eba8075bc03adc03d6d01e3f80f1ec078ee03c7300e378071ac038ce01c6301e2f80f174078b603c5901e2b80f154078a603c510253f0129d8034dc01a6601d2f00e970074aced25401d2700e918032fe0197b00cbb8065cc032de0196b00cb380658c032be0195d00cad806564032ae0195500ca98065440329e0194b00ca380650c032720192500eb78075ac03ace01c6f00e2f80edbc076d603b6701db1806d7c036b601b5700da980ed3c0769603b4701da18169b8034bc09a4e01d1b0065bc032d60196700cb180657c032b60195700ca980653c032960194900ca380650c032820193f00c9d8064dc032660192500eb78075ac03ace01c6f00e3700717c038bc03b6f01db580ed9c076c601b5f00dad806d5c036a603b4f01da680ed2c0769203b4701da280ed0c076820196f00cb580659c032c60195f00cad80655c032a60194f00ca680652c032920194700ca280650c032820193f00c9d8064dc0326601e7f00f3e8079ec07cf401e7700f3b0079d403afe01d7e00ebe8075bc03adc03d6d01e3f80f1ec078ee03c7300e378071ac038ce01c6301e2f80f174078b603c5901e2b80f154078a603c5101dab3acd500b4fc04a7600d37006998074bc03a5c01d2b3a89500749c03a4600cbf8065ec032ee0197300cb78065ac032ce0196300caf806574032b60195900cab806554032a60195100ca780652c0328e0194300c9c80649407cfe03e7e01f3e8075fc07af601d7701eb98075bc03ada03d6b01eb480759c03aca03d6301eb080f1ec098f403c790263b8131d8078e603c7102633813198098ca03c5f03e2f00716c038ae03c53056290169f8094ec05a6e02d3601e998194c803a5e00d2b00e9380b48c0297f00cbd80a5dc032e60296f014b68065ac032d202967014b280658c032c20195f00cad80655c032a60294f00ca580a51c03286019390149280f5bc07ada01c6f00e3680f1ac078d201c6700e3280f18c078c201c5f01e2d80715c078a605b6f02db6812d7c076b603b5301da7806d2c0368e03b43014b780a5b4032d601969014b380a594032c601961014af80656c052ae0195300ca780652c0328e019430149f8064ec0526e0193301f3f80f9f807cfa01d7f00ebe80f5ec07af201d7700eba80f5cc07ae201d6f01eb580759c07ac604c7f0263f01f1f4098de04c6e01e3580f1a4078c604c6201e3080f17c038b601c5701e298129f9ce4f804a760253a0129b8094cc03a5e00d2b00e9380b48c0297f014bf00a5f4052f80197b00cbc80a5dc052ea01973024b90065c4032e00296f00cb580a59c032c60195f00cad80655c032a60294f00ca580a51c03286019390149280f9f807cfa01d7900eb88075b403ad201d6500eb080f1f4078ea01c6d01e34807194038c205a7e0253b0169b80b4d805a6604d32006978034ac03a4e01d230065b4032d20196500cb08064e40324a01d6f00eb580759c03ac605c6f02e370271ac098d409c670263301718c0b8c401c5f00e2f00edbc076d603b6701db1806d6c036ae01b5300da3806d14032de0196b00cb380658c032be0195b00cab80654c0329e0194d00ca58065240328e0194500ca18065040327e0193b00c9b8064cc03cfe01e7b00f3b8079cc07afee557e01ebd80f5e807aee04d7601eb980f5c803ade01d6e01eb680f1fc0f8fc03c7b01e3b80f1cc078e401c6b00e350071a4038ce01c6600e3180f184038ae01c5600e2a8169f8094ec01a6e00d3300e978074b803a567212a00e9380748c0197f00cbd8065dc032e60196f00cb580659c032c60195f00cae80656c032b20195700caa80654c032a20194f00ca580651c032860193900c928071bc098d601c6702e3180717c038ba05c5b01e2c80715c038aa05c5301e28816dbc096d604b6702db1816d7c0b6ba05b5b01dac816d5c0b6aa05b5301da8816d3c0369601b4702da180a5bc052da0196b014b380a594032c60295f014ae80656c032b202957014aa80654c032a20194f00ca580651c032860293f00c9d80a4dc0326601d6f762b580759dd2ac6e846f05635b9919c158c6e345f00e2d80715c158a6e226e0253300e978034ac03a4e03d2300a5bc032d60296700cb180657c032b60195700ca980a53c032960294700ca18064e40524a01d7f00ebd8075dc03ae601d6f00eb68075ac03ad201d6700eb280758c03ac205c7f0263d8131dc0b8e605c6f03e368171ac078d205c6703e3281718c078c201c5f00e2d80715c038a604b76025b3006d78034fe01a7b00d3b8069cc034de01a6d00d358069a8034d201a6800d33826998034ca02a6400d31806984034be01a5b00d2d00695c034ac01a5300d2780692c0348e01a4300d1a8065fc0b2fc0197d02cbe0065ec032f401977024bb0065d4092e80197300cb90065bc052dc0196d014b60065ac032d40196900cb400659c092cc01965014b200658c032c40196100cb000657c032bc0195b00cad00655c032ac0195300ca900653c0729c0194b00ca500651c0b28c0194300ca10064d403afe01d7d00ebd8075e403aee01d7500eb98075c403ade01d6b00eb380758c098fe07c7d0263d80f1e4098ee04c750263980f1c4098de04c6b0263381318c038be01c5b00e2b80714c096fc04b6e00d3f8129f8034fa02a7c00d3d8069e4034ee01a7500d398069c8034e201a7000d378069ac034ce01a6300d2f80696c034b401a5700d2b00694c0349e01a4b00d2380690c0346a0197f024bf0065f4052f80197b00cbd0065e4032f001977014bb0065d4052e80197300cb90065c4032e00196f024b70065b5bc2d80196b00cb500659c092cc01965024b200658c032c40195f00caf00656c032b40195700cab00654c032a40194f01ca700652c032940194702ca300650c0328401935 19 524287 7 127 11 2047 21 2097151
def cc_54_8 : Nat → List (Nat × Nat) := unpackCursorV4 0x86d808531a8272c7e44378f557127d6e72b6a0476683862d3b5de4f5b5295892c53a4f50f2b4ca454795144c2d3cd7f3a22b3742e321532bc6526d4f1f4791c72d1883f13b4d0bb8008b3004e3d0004e 0x1d7f00ebf0075ec09af401d7700ebb0075cc0bae401d6f00eb70075b403ad801d6b06eb50075a640ad001d6700eb300759403ac801d6302eb10075840bac001c7f00e3d8071dc038e601c6f00e368071ac038d201c6700e3280718c038c201c5f00e2f0071740b6fe03b7b025bb80edcc0b6de07b6d01db580eda40b6ce07b6501db180ed84036be05b5d00dad806d64036ae01b5500da980ed440369e01b4b00da3806d0c094f404a770253b01299c094cc04a6500d2f806978134bb1425c00d2b806954034a401a4f00d2380e8fc0b46e0197f00cbd8065dc032e60196f00cb68065ac032d20196700cb280658c032c20195f00caf0065740329e0194e00ca5806524032860194200ca08064fc032760193700c998064ac0325401927014930161fc090ee0586f06c3682619e3e0ca0185f8582e80615c030aa0184f00c2380e0fc0b06e0181f00c0e80605c0502a01d6f00eb580759c03ac601c6f00e3580719c038c605c5f01e2d81715c078a601a6602d2b0065bc032d60196300caf80656c032ae0195300ca780652c0328e0194300c928075bc03ad601d6700eb18071bc038dc04c6b0263500719c038cc01c6300e3100716c038b404b6f01db5812d9c076c601b5f00dad806d5c036a60cb4f02da680ed2c076920cb4702da280ed0c0768204a6e00cb78065ac032ce0196300caf80656c032a60194f00ca68064fc032760193700c998079fc03cfc01e7b0273d0079e409cf001e7700f3b0079cc09ce401e718eb380075fc03af601d7700eb98075bc03adc01d6d0263f80f1ec098ee03c7300e378171b4038d601c6900e33807194038c603c6100e2f80716c038ae01c53025bf0129d8034dd1c26c00d33006990034bc01a5601d2701e918032fe0197b00cbb8065cc032de0196e00cb680657c032bc0195b00cac80654c032a40195100ca780652c0328e0194300c948064a00324a0292400eb78075ac03ace01d6300e378071b8038ce01c6300e3100717c038bc01c5b00e2d00715c038ac01c5300e29012dbc076d604b6701db1806d7c036b601b5700da9832d3c0b69a03b4b01da4832d1c0b68a03b4301da08129bc094dc01a670253100697c034ae09a4f02d2680691c0348a03a3f04d1b8065bc032d60196700cb180657c032bc0195b00cab80654c032a40194f00ca680652c032920194700ca280650c032820193f00c9d8064dc032660192b00c9500649c0524c0486f0243380617c030ae0684f0342681a11c0d08a0383f0341b80607c0303a018170140a8075fc03afc01d7d00ebe0075ec09af401d79026bc0075dc03aec01d7500eba0075cc09ae401d718d2b80075bc03adc01d6b026b500759c03acc01d63026b10071fc038fa01c7b00e3c8071dc038ea01c7300e388071bc038d601c6700e3180717c038bc01c5d025bf81edf4076f603b79025bb812dd4076e603b71025b780edac096ce03b6300daf816d74036b601b5900dab806d54036a603b5100da7806d2c0368e01b430253f8129f81b4fa04a6f02537012988034be09a5d00d2b8069540349e01a4701d1f8268dc032fe0197d00cbd8065e4032ee0197500cb98065c4032de0196b00cb380658c032be0195e00cae80653c0329c0194b00ca480650c032840194100c9f8064ec0326e0193300c958064a80324e029260243f81a1f4090ee048750243781219c030be0685d00c2b8061540309e0184701c1f81a0dc0303e0181d00c0b80a05403ade01d6b00eb380758c038de01c6e00e358071a8038ce01c6602e31817188038b601c5a02db780edac096ce03b6300daf806d6c036ae01b5302da7816d340769603b4902da3816d140768603b4100cb78065ac032ce0196300caf80656c032a60194f00ca68064fc032760193700c998079fc03cfc01e7b0273d0079e409cf001e7700f3b0079cc0bce401e7102f380075fc03af601d7700eb98075bc03adc01d6d02e3f80f1ec098ee03c7300e378171b4038d601c6900e33807194038c603c6100e2f80716c038ae01c53025bb006dba266d80da7e00d374609b0034cc01a6400d2f00e970034ac01a5401d2701e918032fe0197b00cbb8065cc032de0196e00cb680657c032bc0195b00cac80654c032a40195100ca780652c0328e0194300c948064a00324a0292401f3f00f9f403ada01d6900eb28075840b8fc04c7a0263b0171c80b8dc07c6d02e3601f1a8138d209c6803e33033194198c805c6203e30817180038b401c5601dbd00ede4096ec03b71025b300ed94036bc01b5201da680ed240768a03b4102d3f0169c80f4da09a6500d2d0069580348c01a4500cb68065a4032ca0196100ca68065140325a0192503c368321941109a0884501f3f00f9f403afa01d7900eba8075c4098fc10c7d0863e0131e8098f204c780263b0131d4098e804c7204e388271c0098dc04c6a02633013188038b401c56025bf00edf4096dc03b6901db100ed840769a03b4901da280ed04094fc09a7d04d3e0129d4094e404a6e02531006968034ac01a4600d228065f4032f20197500cb88065340328a0192d00c9281a1f4090ea0684d0342280e0f40d06a01c6f00e3580719c038c601c5f00e2e80716c038ae01c5500e29816dbc136da04b6b025b5012d9c096cc09b6500db1806d7c036ba04b5b025ad006d5c036ac01b5500daa006d4c0369601b4700da18169bc074d604a6701d3181697c074b605a5701d2980693c0349601a4700d218168fc0747605a3701d198065bc032d60196700cb180657c032ba0195b00cab806554032a60194f00ca580651c032860193f00c9b8064cc0325e0192b00c9380648c0b0de0486702c2f82615c0309e0184704c1f8260dc0705e0582700c0f80605c03ade01d6b00eb380758c038de04c6b026350271a4098ce04c6602e31827184038b605b6f01db5812d9c076c601b5f00dad806d5c036a605b4f01da5816d1c0768609a6e00d2b042918032de0196b00cb380658c032be0195b00ca980653c0327e0193b00c9b8064cc0324a01d6f00eb580759c03ac608c6f02e3701b1ac098d406c670263302318c0b8c401c5b00e2d022dbc076d606b6701db1806d7c036b601b5700da9822d3c0b69a03b4b01da4822d1c0b68a03b4301da08065bc032d60196700cb180657c032b60195300ca78065340327e0193b00c9b8064cc1109c01d6f00eb580759c03ac610c6f02e370271ac098d410c670263302718c0b8c401c5b00e2d00715c038ac01c538b1b780edae2a6ce03b6300daf806d6c036ae01b5304da7816d340769603b49085a3816d140768603b4104d37c509b8134cf1326200d2f806968034ae01a5600d238069180348a03a3f04d1b8065bc032d60196700cb180657c032b60195700ca980653c0329a0194700ca280650c0327e0193b00c9b8064cc0325a0192b00c93806495780deac06700c2f80615c1309e2904d04c23c481140707e7403700c0f80605c03ade01d6b00eb380758c0b8de05c6e066358131a8198ce04c6602e31817188038b601c5a01db780edac076ce03b6300daf806d6c036ae01b5301da780ed340369601b4900da3806d140368601b4100cb78065ac032ce0196300caf80656c032a60194f00ca68064fc032760193700c998079fc03cfc01e7b0273d0079dc03cec01e7302f390075fc03af601d7700eb98075bc03adc01d6d01e3f80f1ec078ee03c7300e378071b8078da05c6c00e358071a4038ce01c6500e31807188078c203c6000e2f80716c038ae01c5301da70369f8094ec01a6e88136006998034c801a5e01d2e006958034a803a4600cbf8065ec032ee0197300cb78065b8032da0195f00caf00656c032b20195300ca90065440329e0194b00ca380650c032520192800c9280a49003ade01d6b00eb380758c078de03c6b01e3380f18c038be01c5b00e2b80714c0b6de05b6e065b5812da8196ce04b6602db1816d88036be01b5e00dad806d68036ae01b5600da9806d480369e01b4e00da3806d0c0368405a6f04d3380697c034ae03a4f00d2380e8fc0747a01a3700d1a8065bc032d60196700cb180657c032b60195700ca980653c032960194700ca18064fc0327a0193b00c9c8064dc0326a0193300c988064ac0325401927014930161bc110ce0185f00c2b80e13c0709a0384703c228220fc1107a088370441a80607c0302e01e7e0273d0079d80bce401d6e00eb68171f8098f404c7602e390071b8118da09c6c00e350071a4038d001c6600e32807190038c408c6104630007178038b401c5600e2900edb4036d201b6501db08065b8032da0195e00cac806548032a20194d00ca4806514032820587e00c370221b00b08c0383600f3f8079f803cf604e7a00f3b8079d803ce605e7200ebf8075ec03aee01d7300eb78075b803ada05c7f03e3f0171ec098f405c770263b0171cc1b8e401c6f00e370171b40b8d801c6b00e350071a4038d001c6700e33007194038c801c6300e3101f1861c8c001c5f00e2f00716c038b401c5700e2b00714c038a403b7f01dbd80eddc076e601b6f01db6806dac036d201b6700db2806d8c076c201b5f00dad806d5c036a605a7f04d3b8069bc134da01a6700d3280697c034ae03a4f01d2700e9340747e03a3e01d190065fc032f60197700cb98065bc032dc0196d00caf806578032b60195900ca9806548032a20194f00ca680652c032920194700ca280650c032820193f00c9d8064dc032660192b00c9500649c0524c0587f0443b8061bc110da0186700c3280617c030ae0784f8682681611c0f08a0383f01c1e80e0dc0f06a0181f00c0e80605c0502a05d7e026bd0135d80bae405d6e04eb68175b013ad408d69046b402759825aca12d6402eb10235840bac001c6d00e34807194038c201c5d03db680eda40f6ca03b6102dae80ed640b6aa03b510253b012998032da0196900cb2806584032ba0587e04c33022190030ac0184602c1b00605813ade05d6e036b58135a80dace04d6604eb1817588038de01c6b00e3380718c038be01c5d045b780edac0d6ce03b63045af816d74076b603b59045ab816d54076a603b5100da7806d2c0368e01b430452f0065bc032d60196700cb180657c032ba0194f00ca580650c0327e0193b00c9b8064cc030bc0185c096b78175b80dad604d6a036b381359811ac605d6200e378071ac038ce01c6300e2f807174038ae01c5500e29822dbc076d606b6701db1822d7c0b6ba03b5b01dac822d5c0b6aa03b5301da8806d3c0369601b4700da1c2c9bc0d4ce08a5f1492e84a95e144aa01a4f00d2380e8fc1146e0196f00cb580659c032c60195f00cae80655c032aa0195300ca780652c0328e0194300c9f8064ec0326e0193300c9580649c0d0debb06e0343382e188030ae0185600c2a80613c030940184700c2300e0fc17074088373901b1440b8170440181f00c0d00605c0302c01d6f00eb70075ac09ad401d6700eb300758e4eac401c6f00e3580719c038c601c5f00e2f0071764c6de03b6b909b380ed8c036be07b5d00dad806d64036ae01b5500da980ed440369e01b4b00da3806d0e3c4df1b26b8c933c5c98c034bf1125d00d2d80695c034aa01a5300d2780692c0348e01a4301d1fc3c8ee1846e03a3300cb78065ac032ce0196300caf806578032ba0194f00ca700652c032920194300ca10065040327e0193b00c9b8064cc0325e0192b00c9500649c0524c019235d03782e1ad560ce0b86300c2fc24174030b60185700c2a80614c0309e0184b00c2380610c0707e0b83b3881b80e0cca005e0b82b1401382e08c0303e0181d00c0d80605c0502a0181300eb58075a803ace01d6600eb18071bc038d601c6700e3180717c038ba01c5b00e2c80715c038aa01c5300e2880edbc076d603b6701db180ed7c076ba03b5b01dac80ed5c076aa03b5301da8806d3c0369601b4700da18069bc094d404a670253300697c034ba04a570252a80693c0348e03a3f01d1b8065bc032d60196700cb180657c032ba0195b00cac80655c032aa0195300ca880653c032960194700ca18064fc032760193700c998064ac0324e0586f0243382617c110ba098570442a80613c0308e0383f01c1b80607c0302e01d7f00ebd8075dc03ae601d6f00eb68075ac03ad201d6700eb280758c03ac203c7f01e3d80f1dc078e603c6f01e3680f1ac078d203c6701e3280f18c078c201c5f00e2d80715c038a604b7a025bb812dd8096ce04b66025b2806d7c036ae03b4f01da38069fc034f601a7700d398069bc034da01a6b00d3480699c034ca01a6300d3080697c034ba01a5b00d2d00695c034ac01a5500d2780692c0348e01a4300d1d8068dc032fe0597e00cbd8065e8032ee0497600cb98065c8032de0596e00cb68165b0032d60196a00cb48065a0032ce0996600cb2c1c590032c60196200cb0806580032be0195e00cae80653c0729c0194b00ca500651c0728c0194300ca10064ec032740193704c9b0064bc0325c0192d02c3f8121dc0b0de0886d04c33822194030be0185701c2780e11c0305e0182700c0f8060740302e0981500eb78075ac03ace01d6301e3780f1ac078ce03c6300e2f80716c038ae01c5300d378069b8034d601a6a02533812998034c601a6200d2f8069780749e03a4e01d2580e9280748e03a4601d2180e908032de0196b00cb380658c032be0195b00cad00655c032ac0194f00ca580651c032860192b00c948079fc03cf601e7700f3980f5fc07af603d7701eb98075bc03ad601d6700eb18131f8096ec01b6e00db300ed78076ac01a7f00d3d8069dc034e601a6f00d368069ac034d401a6700d33006994034be01a5b00d2b80694c0347201a3500cbf8125f8032f60197a00cbb8125d8032e60197200cb78065b8032da0195f01caf00656c032b40195701cab00654c032a4019457e8a20064e403270019358289a0064bc0325c0192d00eb58075a403ace01d6300eb08071bc038da01c6b00e3480719c038ca01c6300e3080717c038b601c5700e2980edbc076da03b6b01db480ed9c076ca03b6301db080ed7c076b603b5701da9806d3c0369601b4700da18269bc0b4da01a6700d3281297c034ae01a4f00d2380e8fc0746e0196f00cb68065ac032d20196700cb280658c032c20195f00cad80655c032a60194f00ca580651c032860193f00c9d8064dc032660192b00c9381a1bc0d0da068670343281217c090ae0184f00c2380e0fc0706e0181f00c0b8075fc03afa01d7b00ebc8075dc03aea01d7300eb88075bc03ad601d6700eb180f1fc078fa03c7b01e3c80f1dc078ea03c7301e3880f1bc078d603c6701e3180717c038b601c5700e29812dfc096fc09b7d025b7812db8096c401b5f00dab80ed3c0768e01a7f0253f0069f4054f801a7b00d3c8069dc034ea01a7300d390069c4034e001a6f00d3580699c034c601a5f00d2e80696c034b401a5700d2b0069540349e01a4b00d2380690c0347601a3700cbf8125f8032fb0317c00cbd8065e8032f20197800cbb8125d8032ea0497400cb98065c8032e20197000cb78125b8032d60196a00cb3812598032c60196200caf806578032ba0194f01ca700652c032940194701ca300650c032840193d00c9d8064e80326e0993600c9abf04d00325e0192e00c968121fc0d0fa048770243a8121bc090ce0185f00c2b80e13c0708e0182f00c1380607c0303a018170340a8075bc03ad601d6700eb180f1bc078d603c6701e3180717c038b601c5700e29812d980b4de05a6e00d358069a8034ce01a6600d31806988034be01a5e01d2780e9380749603a4a01d2380e9180748603a4200cb78065ac032ce0196300caf806574032b60195a00cab806558032aa0194f00ca580651c032860192b00c948079fc03cf601e7700f3980f5fc07af603d7701eb98075bc03ad601d6700eb18131d8136fc01b6e00db300ed78076ac01a7f00d3d8069dc034e601a6f00d368069ac034d401a6700d33006994034be01a5b00d2b80694c0347201a3500cbf8165f8032f60197a00cbb8125d8032e60197200cb78065b8032da0195f01caf00656c032b40195701cab00654c032a40193900c9c0064d6022680192f00c970064b403ad601d6900eb380758c03ac201c6f00e368071ac038d201c6700e3280718c038c201c5f00e2d80715c038a603b6f01db680edac076d203b6701db280ed8c076c203b5f01dad80ed5c076a601b4f00da5806d1c0368605a6f02d370169b40b4be05a5e00d2b8169480349e01a4701d1f80e8dc032de0196d00cb58065a4032ce0196500cb1806584032be0195b00cab80654c0329e0194b00ca380650c0327e0193b00c9b8064cc032560192704c378221b4130ce0886502c2f81215c0309e0184701c1f80e0dc0303e01817 20 1048575 8 255 11 2047 21 2097151
def cc_54_9 : Nat → List (Nat × Nat) := unpackCursorV4 0xa49419e86199553934618bb7987e3d8017d7c23f761617124f6957d66a2b62b3f5d85355b7d52e2d4ef3f49f50438673eb4d38665332542e052277691d7a01d5021cf061636c1204307ca402d4f0002d 0x3cfe01e7e00f3e8075fc03afa01d7b00ebc8075dc03aea01d7300eb88075bc03ad601d6700eb180b1fc078fa02c7b0163c80b1dc058ea02c7301e3880f1bc078d603c6701e3180717c038b601c5700e2980adfa806f801b560153f4fc9f0054ec02a7402537012998034bc03a4e01d230065fc052fc0197d00cb780a5b8032d60196900cb1806588032c20195f00cad80655c032a60194f00ca580651c032860192900c940064940524801d6f00eb70075b4038de01c6d0163580b1a4038ce01c650163180f184038be04c5b00e2b81314c056de07b6d015b580ada4056ce02b65015b180ed84096be04b5b025ab812d4c1969e01b4b00da382ad0c054df4426d0153580a99c054ca02a630252f81296c094ae04a53a092780692c0348f3e2430551f8328ec1946e0aa33014b780a5b8052da0295f014af00656c032b201953024a90065440329e0194b00ca380650c0527e0193b0149b8064cc0525e0192b0149380648c050de0686d0143580a19c050ca028630242f81216c090ae048530342780612c0308e068430341f81a0ec0d06e068330341781a0ac0d04e0682300c0f80a06c0502e0181300eb78075ac03ace01d6302e378131ac098ce05c6300e2f80716c038ae01c53015b780adb8096ce05b63015b1006d7c036bc01b5b00dad006d5c036ac01b5300da9026d3c0769c05b4b02da5016d1c0b68c0ab4301da10169bc0b4dc04a6702d3100697c034b401a5700d2b02693c0b49405a4702d230068fc0347c01a3d00cb78065ac032ce0196300caf80656c032ae0195300ca780652c0328e0194300c9d8064e40326e0193300c988064ac032520192700c908161bc090ce0185f00c2b82a13c0b08e0983f05c1e8260dc1706a0b82d05c1280607c0302e01d6f00eb580759c03ac605c6f0263581319c0b8c601c5f00e2d80715c038a605b6f025b5812d9c0b6c601b5f00dad806d5c036a60ab4f02da5816d1c1568601a6f00d368069ac034d401a6702533006994034be01a5b00d2b80694c0349e01a4b00d2380690c0347e01a3b00d1b8068cc032de0296e00cb680657c032bc0195b00cad00655c032ac0195300ca900653c0729c0194b00ca500651c0f28c0194300ca10064fc032760193a00c9bcf04d8032660192f00c970064b40b0de0486b0243381618c030be0185b00c2b80614c1509e0584b02c2381a10c1707e0683b05c1b81a0cc0305e0182b00c1380608c0303e0181d00c0d80605c1702a0181300ebf8075ec03aee01d7300eb78075b403ad601d6900eb380759403ac601d6100e3f8071f8038f602c7a00e3b8071d8038e602c7200e378071b8038da01c6c00e3580b1a8038d202c6800e33807198038ca01c6400e3180b188038c202c6000e2f807178038ba03b7f01dbd80eddc076e603b6f01db680edac076d203b6701db280ed8c076c201b5f00dad806d5c036a601b4f015a6806d2c0369201b4700da2806d0c0568204a7a0253b8129d8094ce04a660253280697c034ae01a4f0152680691c0348a03a3f01d1b8065fc032f60197700cb98065bc032da0196b00cb480659c032ca0196300cb080656c032b40195900cab806558032a60195100ca38065180328a0193f00c9d8064dc032660192b00c938161fc090ee0586f0443682619c110ca0185f00c2b80613c0509a0184700c2280e0fc0706e0181f00c0b8079fc03cf601e7700f398075fc03afc01d7b016bd0075dc03aec01d73016b90075bc03adc01d6d01e3f80f1ec078ee03c7300e378071ac038ce01c6300e2f80b174038b601c5900e2b807154038a602c51025bf0129d8034dc01a6600d2f00a970034ac01a5401d2700e918032fe0197b00cbb8065cc032d60196a00cb480659c032cc0196300cb080655c032ac0195500ca780652c0328e0194300c9480649403afe01d7d00ebd8075e403aee01d7500eb98075c403ade01d6b00eb380758c038fe01c7e00e3e8071f0038f602c7a00e3c80b1e0038ee01c7600e3a8071d0038e602c7200e3880b1c0038de01c6e00e3580b1a8038ce01c6600e3180b188038be01c5e00e2e80edfc076fa03b7b01dbc80eddc076ea03b7301db880edbc076d603b6701db1806d7c036b601b5700da9806d3c0569a01b4b00da4806d1c0368a01b43015a08129fc094fc0da7d025378129b8094c401a5f00d2b80693c0549a01a4700d2280e8fc0746e0197f014bf0065f4052f80197b00cbc8065dc032ea0197300cb90065c4032e00196f00cb580659c032c60195b00cad006564032ae0195600ca98065440328e0194600ca28064fc032760193700c998064ac0324e0487f0343e8121dc090ea0486f0243380617c030ae0184f0142680611c0308a0383f01c1b80607c0302e01e7f00f3d8079dc03ce601d7f00ebf0075ec05af401d7700ebb0075cc05ae401d6f00eb70075b4078fe03c7b01e3b80f1cc038de01c6b00e3380718c038be02c5d00e2d807164038ae01c5500e2980b144096ec0da7e00d3700e9b0034cc01a6400d2f00a970034ac01a5401d2700e918032fe0197b00cbb8065cc032d60196a00cb480659c032cc0196300cb080655c032ac0195500ca780652c0328e0194300c9480649403ade01d6b00eb380758c038de01c6e00e3580b1a8038ce01c6600e3180b188038be01c5e00e2e80edbc076d603b6701db1806d7c036b601b5700da9806d3c0569a01b4b00da4806d1c0368a01b43015a0ce89be724d7382679b93180697c034b601a5700d2980693c0549a01a4b00d238069140348603a3f01d1d80e8dc074660196f00cb580659c032c60195b00cad006564032ae0195600ca98065440328e0194600ca28064fc032760193700c998064bc032560192700c91af41bc170d6b006705c3180617c030b60185700c2980613c0509a0184b00c23806114030860383f01c1d80e0dc070665402f05c158ac09c170460181f00c0d80605c0302601d6b00eb500759c03acc01d6300e378071ac038ce01c6300e2f807174038b601c5900e2b807154038a601c5102db780edac096ce03b6302daf816d74076b603b5902dab816d54076a603b5100da7806d2c0368e01b4300d3781299c034be01a5d0252b8129540349e01a4701d1f8168dc032de0196b00cb380658c032be0195d00cad806564032ae0195500ca98065440329e0194b00ca380650c0327e0193b00c9b8064cc032560192a00c938264980b0de0486704c2f822174130ae0885500c2780611c0707e0583700c0f80605c03afe01d7b00ebb8075cc03ade01d6d00eb58075a403ace01d6500eb18075840b8fe03c7b0263b80f1cc0b8de07c6d01e3580f1a40b8ce07c6501e3180f184038be01c5b00e2b80714c096f404b77025bb012d9c096cc04b6500daf806d5c0769e05b4700d3f8069ec034ee01a7300d378069b4034d601a6900d33806994034c601a6100d2f806978034ba01a5700d2a80694c034a401a4f00d2580691c0348601a3b00d1d0068dc1346c0197f02cbf0065ec032f401977024bb0065cc032e40196f02cb70065b40b2d80196b00cb50065a4032d00196704cb30065966a2c80196300cb1006584032c00195700cab0065540329e0394e00ca58065280328e0594600ca1806508032760193a00c9b8264d80325e0192e00c968161fc090ee0586f04c3682619c130ca0185f00c2b80e13c0b08e0182f00c1680609c1304a0181f00c0e80605c1302a01d6f00eb580759c03ac604c6f01e3581319c078c601c5f00e2d80715c038a601a6f00d370069ac034d404a670253300698c034c401a5700d2b00e93c0749c0aa4b02d2502a91c0b48c03a4301d210065bc032d60196700cb180657c032ae0195300ca780652c0328e0194300c958064a403cfe01e7b00f3b8079cc09afe03d7b026bb80f5cc03ade01d6b00eb380758c098fc04b7600db7006d98076bc07b5600d3f8069ec034ee01a7300d378069b8034da01a6700d3280698c034c401a5f00d2d80695c034a601a3900d1c0068d4054680197f024bf0065ec032f401977024bb0065cc032e40196700cb3006594032be0395e00cad806568032ae0595600ca9806548032720193800c9accc4d00325e0192e00c968075ac03ad201d6700eb1807584038de01c6d00e358071a4038ce01c6500e31807184038be01c5b00e2b80714c136de05b6d01db580eda4136ce05b6501db180ed84096be03b5b025ab80ed4c0369e01b4b00da3806d0c134de05a6d00d33806994094be01a5700d2780691c0747e09a3700cb78065b4032d60196900cb3806594032c60196100caf80656c032ae0195300ca7806538032960194700ca18065080327e0193b00c9b8064cc032560192a00c938264980d0de0686d0343381a194090be0485700c2780611c0707e0683700c0f8060740302e0681500ebf8075f403af601d7900ebb8075d403ae601d7100eb78075ac03ace01d630263f81f1f4078f603c790263b8131d4078e603c710263780f1ac098ce03c6300e2f80716c038ae01c53025bf812df8136fa04b6f025b7012d88036be01b5701da7826d1c034fe01a7d00d3d8069e4034ee01a7500d398069c4034de01a6b00d3380698c034be01a5e00d2e80695c034aa01a5300d2900693c0349601a4700d218068ec0347401a3704d1b0065fc092fc0197d988be0065ec032f40197900cbc0065dc092ec01975024ba0065cc032e40197100cb80065bc092dc0196b00cb500659c092cc0196300cb100655c032ac0195500ca780e538032960194a00ca3816518032860194200c9d8064e80326e0993600c978064b80325a0487f0343e8121dc090ea0486f0243380617c030ae0384f034238060bc0305a018270341280607c0303a018170340a8075bc03ad601d6700eb18171bc078d604c6701e3180717c038b601c5700e298169bc0b4dc01a6b00d3500699c034cc01a6300d3100695c034ac03a4f01d2701692c0b49405a4702d2300e90c074840196f00cb580659c032c60195f00cae80655c032aa0195300ca780652c0328e0194300c958064a403cfe01e7b00f3b8079cc0bafe03d7b026bb80f5cc03ade01d6b00eb380758c098ec09b7e00db7006d98076bc07b5600d3f8069ec034ee01a7300d378069b8034da01a6700d3280698c034c401a5f00d2d80695c034a601a3900d1c0068d4054680197f02cbf0065ec032f401977024bb0065cc032e40196700cb3006594032be0395e00cad806568032ae0595600ca9806548032720193800c9acbc4d00325e0192e00c968075ac03ad201d6700eb1807584038de01c6d00e358071a4038ce01c6500e31807184038be01c5b00e2b80714c0b6de05b6d01db580eda40b6ce05b6501db180ed840b6be03b5b025ab80ed4c0369e01b4b00da3806d0c0b4de05a6e02d3681697c0b4bc01a5702d2900693c0348e03a3f02d1b8065bc032da0196b00cb480659c032ca0196300cb080657c032b60195700ca980653c032960194700ca18064fc032760193700c998064b4032560192700c928261bc110da098670443281617c090ae0184f00c2380e0fc0b06e0181f00c0b8075bc03adc01d6d00e378071b4038d601c6700e3280718c038be01c5d00e2d807164038ae01c5500e298071440b6de03b6b025b380ed8c0b6be05b5d01dad80ed640b6ae05b5501da980ed440369e01b4b00da3806d0c0b4de04a6b0253381698c0b4be05a5d02d2d81695e5a4aa05a5300d2780692c0348e01a4301d1f8168ec0b46e03a3300cb78065ac032d20196700cb1806584032be0195d00cad806564032ae0195500ca98065440329e0194b00ca380650c0327e0193b00c9b8064cc0325e0192b00c9380648c0b0de0486b0243381618c0b0be0585d02c2d81615c170aa0585300c2780612c0308e0184301c1f8160ec0b06e0383305c1781a0ac1704e0682300c0f80606c0302e0181300eb78075ac03ace01d630563780f1ac158ce03c6300e2f80716c038ae01c5304db7816db81d6d604b6a04db3812d981d6c605b6200daf806d6c036b401b5700dab00ed3c0769c0ab4b02da5026d1c0b68c03b4301da10269bc134ce01a5f00d2d00695c034ac03a4f04d238068fc0347c01a3d00cb78065ac032ce0196300caf80656c032ae0195300ca780652c0328e0194300c9d8064e40326e0193300c988064ac032520192700c9082e1bc170ce0185f00c2b80e13c1508e0983f05c1e8260dc1706a0181f00c0b8075bc03ad601d6700eb182b1bc078d60ac6701e3180717c038b601c5700e29cd0dbe646d730367971b1806d7c036b601b5700da980ed3c156960ab4701da18069bc034d601a6700d3180697c034bc01a5d00d2b806954034a601a5200d2780692c0348e01a4300d1f8068ec0347401a376291b0068cc032df2c16e00cb58065a8032ce0496600cb1806588032ae0195600caa80653c0729c0194b00ca500651c0f28c0194300ca10064fc032760193a00c9bcac4d8032660192f00c970064b4170de0b86b05c3382e18c030be0185b00c2b80614c0709e0a84b0542380e10c1707e0b83b05c1b82e0cc0305e0182d00c1580609c1704a0182300c0f806074030360181705c0a80604c03ade01d6b00eb380758c038de01c6e00e3380718c038c401c6100e3000717c038bc01c5b00e2d00715c038ac01c5300e29016dbc076d604b6701db1806d7c036b601b5700da9816d3c0b69a03b4b01da4816d1c0b68a03b4301da08169bc0b4dc01a6702d3100697c034ae05a4f02d270169340747e05a3a02d1b8168d8032de0196b00cb380658c032be0195b00cab80654c0329e0194d00ca58065240328e0194500ca18065040327e0193b00c9b8064cc032560192702c3781219c030be0185704c278221341308e0884501c1f8160dc1305a0982500c0f80605c03ade01d6b00eb380758c038de01c6e00e3380718c038c401c5f00e2f00716c038b401c5700e2b00714c038a405b6f01db5812d9c076c601b5f00dad806d5c036a605b4f02da680ed2c0769205b4702da280ed0c0768205a6f0253380697c034ae08a4f04d2682291c1148a03a3f02d1b8065bc032d60196700cb180657c032b60195700ca980653c0329a0194b00ca480651c0328a0194300ca08064fc032760193700c998064ac0324e0586f02c3700619c0b0c40185f00c2b81613c0b09c0584d01c1f8160e80b06e05836034150220980303e0181700eb78075b403ad601d6700eb280758c038de01c6e00e3680717c038bc01c5b00e2d00715c038ac01c5300e29016dbc076d604b6701db1806d7c036b601b5700da9816d3c0b69a03b4b01da4816d1c0b68a03b4301da08169bc094d71d2690253381698c0b4c201a5f00d2d80695c034a605a4f02d2681692c0b48f2924502d2180e8fc0b47605a3701d198065bc032da0196b00cb3806594032c60195f00cad80655c032a60194f00ca680652c032920194700ca280650c032820193f00c9d8064dc032660192f00c9580649c032460586f0243581219c0b0c60185f00c2d80615c030a60584f02c2681612c0b08f2804502c2180e0fc0b0760583701c1994c0bc0d0562a0270341180607c030360181700c0980f9fc07cfc03e7d00ebf8075f803af604d7a00ebb8075d803ae605d7200eb78075b803ada01d6c00eb581f5a803ad20cd6800eb380759803aca01d6400eb181758803ac205d6000e3f8071ec038ee01c7300e378071b4038d601c6900e33807194038c601c6100e2f807178038ba03b7b01dbd00ede4076ee04b7601db980edc4076ce04b6601db2806d7c036bc03b5d02dae006d6c036b201b5700daa806d4c036a403b5101da8006d3c0369c01b4b00da3806d0c0368405a7f0253d8129dc0b4e605a6f03d3681e9ac0f4ce0ca6502d3180697e2c4ba01a5b00d2b806954034a601a4f00d2580691c0348603a3f01d1d80e8dc074660197f00cbd8065dc032e60196f00cb68065ac032d20196700cb280658c032c20195f00caf0065740329e0194e00ca5806524032860194200ca08064fc032760193700c998064bc032560192a00c9380a498032460587f0243d8121dc0b0e60586f03c3681a1ac0f0ce0c86502c3180617c110ba0185b00c2b806154030a60184f00c2580611c030860383f01c1d80e0dc070660882f0341582209c0d0460181f00c0e80606c0302e0281500c09856960134a815b5404d2e00e9300b48801928014920075bc03ad601d6700eb18071bc038dc03c6b01e3500719c038cc01c6300e3100717c038bc01c5b00e2d00715c038ac01c5300e2900edbc096dc03b6b00db380ed8c076c401b5f00dad806d5c036a603b4f01da6806d2c0369201b4700da2806d0c0368204a6f0253581299c094c601a5f00d2d80695c034a72524f04d2685692c2b48e09a459212180e8fc0747603a3701d198065bc032d60196700cb180657c032b60195700ca980653c0329a0194b00ca480651c0328a0194300ca08064fc032760193700c998064bc032560192700c918121bc090d6048670243180617c030b60185700c2981a13c0d09a0684b0342381a1140d0860383f01c1e80e0ec0706e0683501c1981a0bc0d056068270341180607c030360181700c0980f9f407cea01d7e00ebe8075f013af401d790b6bc0075d803aea01d7404eb90075c413ae001d6e026b500759809ac401c7d00e3c8071d4038e201c5e00e2e80edf4076ea03b5d00dac806d54076a204a760253a8129a8094cc01a5e04d2e826970034aa01a5201d1d00e8d8052fc0197d014be0065e4032ea0197200cb88065c0032bc0195d00ca7006524032840194100c9500a4980d0fa068750342e8061540707a068350341481a0840303a0281501f3f80f9f807cfa01d7f00ebf0075f403af801d7b026bd0075e409af001d7700ebb0075d403ae801d73026b90075c646ae001d6f00eb70075ac09ad401d6700eb300758c09ac401c7f00e3f0071f4038f801c7b00e3c8071dc038ea01c7301e390071c4078e001c6f00e3580719c038c601c5f00e2f007174076fe04b7e01dbe80edbc096dc03b6b01db480ed8c076c403b6100daf80ed74036b601b5900dab806d54036a603b5100da7806d2c0368e01b430253fc889f4094f604a770253a8129cc094de04a6b0253381298c034bf1525d00d2d80695c034aa01a5300d2780692c0348e01a4301d1f80e8ec0746e03a3300cbf80a5f8032fa0297c00cbd8065e4032ee0197500cb98065c8032e20197000cb78065ac032ce0196300caf806578032ba0194f00ca700652c032920194300ca10065040327e0193b00c9b8064cc0325e0192b00c9500649c0524c019230243f81a1f4090f6048770243a8121cc090de0486b0243381218c030be0685d00c2d80615c030aa0185300c2780612c0308e0184301c1f80e0f407076038370341a80e0cc0d05e0682b0341381a08c0303e0181d00c0d80605c0502a0181300eb78075ac03ace01d6300e378071ac038d401c6700e3300717c038bc01c5b00e2d00715c038ac01c5300e29016dbc076d604b6701db1806d7c036b601b5700da9816d3c0b69a03b4b01da4816d1c0b68a03b4301da08069bc094ce01a5f00d2b81293c0949a01a4700d2280e8fc0b46e0196f00cb580659c032c60195f00cad80655c032a60194f00ca680652c032920194700ca280650c032820193f00c9d8064dc032660192b00c9500649c0524c0586f0243380617c030ae0d84f0442683611c1108a0383f02c1b80607c0302e01d7e026bd0075d80bae401d6e00eb68075b011ad401d69046b400759803aca01d64046b100758413ac001c6d00e34807194038c201c5e00e2e816db4076d205b6501db0816d74036b201b5501da88065b4032d20196500cb0806578032ba0194e00ca4806508032820587e02c37006178110b805836 20 1048575 8 255 11 2047 21 2097151
def cc_54_10 : Nat → List (Nat × Nat) := unpackCursorV4 0xf9263d898f1e8bad35e212b6f32d7c834730c8532ee66b52ceafcaa7e8289ac98d363ccd894bde8f9746b9b23f6926d8eac59d3d36e143d3cdee12dd3c90cd1a53c2b7c05ca0002e 0x1c5f00e2d80715c038a603b5f01dad80ed5c076a601b4f00da5806d1c036860195f00cad80655c032a60194f00ca580651c032860193f00c9d8064dc0326601c5f01e2d80715c078a603b5f01dad80ed5c076a603b4f00da5806d1c076860295f014ad80a55c052a60294f00ca580651c052860293f0149d80a4dc0526601d6f01eb580759c07ac603c6f01e3580f19c078c603c5f00e2d80715c078a601b56af937012998074bc03a4e01d2352c5bc032d73e16700cb180657c032b60195700ca980e53c032960394700ca18064a6bc25002925ae89200f5bc07ad603d6701eb180f1bc078d603c6701e3180f17c078b603c5701e29822dbc0b6dc06b6b025b501ad9c096cc09b6302db100ed7c076bc03b5b00dad00ed5c036ac03b5301da902a5bc0d2d60696704cb180e57c072b60395701ca980e53c072960394701ca18264fc0527a0893b00c9c8224dc0526a0993300c98832198070bc0384e01c1f02a05807ade03d6b01eb380f58c078de03c6b01e3380f18c078be03c5b01e2b80f14c076de0cb6e01db580eda8076ce04b6601db180ed88076be03b5e01dad806d68076ae01b5601da980ed48194de0ca6701d2f80e95c0749403a4701d2300e8dc0746c07a35054b782a5ac152ce0a96301caf80e56c072ae0395301ca780e52c0728e0394301c9f80a4f4072760193901c9b80a4d407266019310549582a49c190de0c86701c2f80e15c0709e0384d01c239d81140707e0383d01c1bd6c0d41503e0a81702e3780f1ac098ce03c6302e2f807174078b603c5902e2b807154078a603c5102db7816db4076d604b6702db280ed8c0b6be05b5d01dad80ed640b6ae05b5501da980ed440769e03b4b01da380ed0c0b2de0496b024b381658c0b2be0295d02cad8065640b2ae0295502ca98065440729e0a94b06ca380e50c0727e0593b02c9b80e4cc0bade03d6b066b380f58c0b8de03c6b02e3380f18c078be03c5b01e2b80f14c0769d5926e0253300e978034ac07a4602cb782a5ac192ce0596301caf82a56e1e2ae0395301ca781652c0b28e0394300c9480a4940bade03d6b026b380f58c0b8de03c6b0263380f17c078b603c5701e29816dbc0b6dc03b5f01daf022d6c036b408b5700dab00ed4c076a403b4f01da70165bc092d60496702cb180e57c112b60895701ca980e53c0b2960594701ca18224fc0527a0893b00c9c8224dc0526a0893300c988161b8110ac0584602c1f0220580bade03d6b026b380f58c0b8de05c6d01e3581319c0b8ca03c6301e2f80f16c078ae03c5302db7816db80b6da03b5f01daf016d6c036b405b5700dab00ed4c076a403b4f01da7016d1c0768603b4202d378169b4094ce0ca6501d2f83695c0749e05a4701d1f80e8f40b46e03a3502cb78125ac092ce0596301caf82a56c1b2ae0395301ca781652c0b28e0394302c9f80a4f40b2760193902c9b80a4d40b2660193105495b1c49c0b0de0486701c2f83615c0709e0584702c1f8160f40b06f570350540f81005c03cfe01e7e00f3d8139e803cee01e7600f398179c803afe01d7b00ebb8075cc0b8fe07c7e02e3d8131e80b8ee04c7602e398371c8038de01c6e01e3680f1b0038d601c6a00e348071a0038ce01c6600e32807190038c601c6201e3080f180038be01c5e00e2d807168038b201c5800e2b807158038a601c5201e2880f140076fe03b7b01dbb80edcc036de01b6e01db6816db0036d601b6900db3806d94036c601b6201db080ed80036be01b5b00dab806d4c134ec01a6e00d2f00e9380747c0197f00cbd8065dc032e60196f00cb68065ac032d20196700cb280658c032c20195f00cad80655c032a60194f00ca680652c032920194700ca280650c032820193f00c9d8064dc032660192502eb780f5ac0dace03d6302e378171b80d8d604c6a036338131980b8c605c6201e2f80f178118b601c5a0462b807158078a603c5202db780edac0b6ce03b6301daf80ed6c076ae03b5302cb781a5ac0d2ce0596301caf82656e1a2ae03953044a780a534132960194904ca380a514112860194101c9f8164ec0b26e0393302c370161180b06c05d6f01eb583359c07ac605c6f03e370171ac098d405c670263301718eac8c403c5f01e2f01f16c038b405c5700e2b00f14c078a405b6f01db5816d9c076c603b5f01dad80ed5c076a605a6f0653380e97eaa4ae03a4f01d2700e9340747e03a3e01d190165bc152d60c96702cb180e57c152b70c15701ca981e53c0529a0594b00ca481651c0528a0794300ca080e4fc0b2760593701c9982a4ad8c24e0586f0643380e17d0e0ae0784faa02681611c0f08a0383f4101e8160dc0f06a0a81f0180b80f5bc07ad603d6701eb180f1bc078d603c6701e3180f17c078b603c5701e2980ed18194dc04a6601d2f0069580749c0a96f054b582a59c152c60395f01cad80e55c072a60394f01ca580e51c0728601929014928175ac0bad201c6f00e368231ac078d201c6700e3282318c078c201c5f0262d80715c0b8a605b6f02db6822dac076d205b6702db2822d8c076c205b5f025ad812d5c0b6a605b4f00da5806d1c1168602967014b280656c052ae0195300ca780652c0328e019430149f8064ec0526e01933044330075ac03ad204d6702eb1807584038de01c6d04e3580f1a4038ce01c6508e3180f184038be04c5b00e2b81714c0b6de05b6d04db580eda40b6ce05b65055b180ed840b6be04b5b025ab816d4c0b69e01b4b00da382ad0c054de02a6e0153681697c0b4bc04a5702d2902693c0348e09a3f02d1b80a5bc052da0196b014b380a594052be0195b014ab80654c0329e0194b00ca380650c0527e0193b0149b8064cc0525a0192b0149380a494130df5106d04c338b41940b0be0485708c2780611c1507e0583700c0f80a05c07ade03d6d00eb58075a403ace01d6500eb1807584038de01c6d00e33807194038c601c5f00e2d80715c038a603b6f01db680edac076d203b6701db280ed8c076c203b5f01dad80ed5c076a601b4f00da5806d1c0368601a6f00d3680699c034ca05a5f0252b80693c0348e03a3f01d1b8065bc032da0196b00cb480659c032ca0196300cb080657c032b60195700ca980653c032960194700ca18064fc032760193700c998064ac0324e1086f0443684219c110ca0585f0242b80613c0308e0383f01c1b80607c0302e01e7e00f3e8075b403ad201d6500eb08171f8098f404c7602e3900b1b8058da02c6c016350271a4138d002c6604632823190058c402c610163000adb4076d203b65015b080ed340769203b4501da08065e8032f20297600cb880a598032ca0294e00ca680a530032920194500ca1006504032800185e01c2700605803cfe01e7e00f3e8075fc03af601d7700eb98075bc03ada01d6b00eb480759c03aca01d6300eb080f1fc0b8fc03c7b01e3d00f1dc098ec03c7301e3900b1bc058dc02c6d0163600b1ac058d403c6901e3400b19c058cc03c65a7a3200b18c058c402c610163000edfc076f603b7701db980adbc056da02b6b01db480ad9c076ca02b63015b0806d7c036b601b5700da980ed3c0769a03b4b01da480ed1c0768a03b4301da08169fc094ee02a6f0153680a99c134ca01a5a00d2b8069580348e01a4600d2280e8fc0746e0197b00cbd0065e4032ee0297600cb98065c4032ce0296600cb280657c032b60195700ca980653c0329a0194b00ca480651c0328a0194300ca08064fc032760193700c998064ac0324e0587f0243b80a1bc050da028670443280617c030ae0384f01c2680e11e9c08a0383f01c1b80607c0302e01d6b00eb48071bc038da01c6b00e3480719c038ca01c6300e3080717c038b601c5700e2980edbc076da03b6b01db480ed9c076ca03b6301db080ed7c076b603b5701da9806d3c0369601b4700da180659c052cc0196500cad806568032ae0295600ca980653c032960194700ca18064fc032760193700c998079fc03cfc01e7d00ebf8075ec03aee01d7300eb78075b403ad601d6900eb380759403ac601d6101e3f80f1ec078ee03c730163780b1b4058d603c690163380f194058c602c6100e2f80716c038ae01c5300dab0169f8094ec02a6e0153600a99a984c801a5e01d2700e918032f60197a00cbc8065dc052ec0197300cb880659c052cc0196500caf80656c032ae0195300ca780652c0328e0194300c948064a00324a0292400f3f0175f8038da08c6900e32823184038ba03c5900e2a80f1440b6da08b6902db2822d840b6ba03b5902daa80ed44114cc08a640452b00a594052aa0587e014370160d80502c05d6f02eb70071bc098d601c6702e3180717c038ba08c5b01e2c80715c038aa08c5301e28816dbc096d604b6702db1816d7c0b6ba09b5b01dac816d5c0b6aa09b5301da8816d3c0369601b47045a1822958032d60296700cb180a55c052aa0194f00ca580651c032860293f00c9d80a4dc0326601d6f00eb701359c0bac601d6200e378131ac038ce05c6300e2f807174118b603c5900e2b807154118a603c5102db7812dac096ce05b6302daf816d74116b603b5902dab816d54116a603b5102da7806d2c0368e08b4302d3781299e944bf4925d0452b8b49541149e01a470551f8168dc052de0196b014b380658c052be0295d00cad80a55c052aa0194f00ca580651c032860293f00c9d80a4dc032660192b014938161bc0b0dc0486702c3100a17c050bc0285d0342780611c0d07e0583a02c1b8160d80303e0281a0140b80a05803ade01d6e00eb68071bc098d601c6702e3180717c038ba02c5b01e2c80715c038aa02c5301628816dbc096d604b6702db180ad7c056ba02b5b01dac80ad5c0f6aa02b53015a8816d3c0369601b47055a18169bc094d604a6702d3180a97c054ba02a5b0152bd40954054a74d24f00d2580691e964860aa3f02d1d8168dc154660196b024b50065a4052ce0296600cb1806584052ae02956014aa80653c032960194700ca180a4fc032760293700c9980a4bc032560292700c918161bc090d60486702c3180a17c050ba0285b0142bd20154050a69b04f00c2580611c0d0860a83f02c1d8160dc0d0665502f034158b009c0d0460181f0140d80a05c0302601d6f00eb580759c03ac604c6f0263581319c098c601c5f00e2d80715c038a604b6f025b580ada8056ce02b6600daf806d78036b601b5a00dab806d58036a601b5204da780ed381569605b4a04da3816d181568603b42025378129a8094ce04a6600d2f80695c1349e09a4700d1f8068f80347a0196f00cb580659c032c60195f00cad80655c032a60194f00ca580651c032860193b00c9c8064dc032660193100c958064a40324e019210243781219c030be018570342781a11c0d07e0683d0341b81a0d40d0520682100c0f80605c03ade01d6b00eb380758c098de04c6b0263381318c038be01c5b00e2b80714c096de04b6b025b3812d8c036be01b5b00dab806d4c1569e0ab4b055a382ad0c034de04a6e00d3680699c034ca01a6300d3100697c034b601a5700d2980693c0349601a4700d218068fc0347601a3700d1980659c052cc0196500caf806578032b60195a00cab806558032a60195200ca780e538032960194a00ca381e518032860194200c9f8064ec0327401937a309b0064cc0325e0192e00c968121bc090d6048670243180617c030b60185700c2981a13c0d096068470342181a0fc0d07606837034198060bc030560182700c1180607c0303a0181b00c0b81a0540302601d6b00eb501359c03acc04d6300e378131ac038ce04c6300e2f8071741b8b603c5900e2b807154138a603c51025b7812dac096ce04b6304daf816d74156b603b59065ab816d54136a603b51065a7806d2c0368e0ab43025378129a8094ce04a660152b80a958054aa09a4fa112700691e8048409a3f04d1b80a5bc032d60296700cb180a57c052ba02957014aa80654c0329e0194b00ca380650c0527e0193b0149b8064cc0525a0192b0149380a494090de048670342f81a1740d0ae068550342780611c0d07e0683700c0f80a05c07ade03d6e00eb58075a803ace01d6600eb1807588038de01c6b00e3380718c038be01c5d00e2d80715c038aa03b6f01db580ed9c076c603b5f01dae80ed6c076b203b5701daa80ed4c076a201b4f00da5806d1c0368604a6f0253380697c034ba01a5700d2a80693c0348e03a3f01d1b8065bc032d60196700cb180657c032ba0195b00cac80655c032aa0195300ca880653c032960194700ca18064fc032760193700c998064ac0324e0486f0243381a17c0d0ba068570342a80613c0308e0383f01c1b80607c0302e01d6b00eb380758c038de01c6b00e3380718c038be01c5d00e2d80f168038ae01c5600e2a80714c076de03b6b01db500ed9c096cc01b6300daf806d74056b602b5a00dab806d58036aa01b5400da980e9bc074d603a6701d3180e97c074b603a5701d2980693c0349601a4700d2180e8fc0747603a3701d198065bc032d60196700cb180657c032ae0195300ca780652c0328e0194300c9f8064f4032760193700c9a8064cc0325e0192b00c9380648c090de048670342f81a15c0309e0184701c1f80e0dc0705e0382700c0f80605c03cfe01e7e00f3e8075fc03afa01d7b00ebc8075dc03aea01d7300eb88075bc03ad601d6700eb180b1fc058fc03c7da1a3e00b1ec058f402c790163c00b1dc058ec02c750163a00b1cc058e403c7101e3800f1bc098dc03c6b01e3500f19c098cc03c6301e3100adfc076fa02b7b015bc80addc056ea02b7301db880edbc076d603b6701db1806d7c036b601b5700da980ed3c0769a03b4b01da480ed1c0768a03b4301da080a9fc054fc09a7da113e00a9dc054ea02a720253781299c034b401a5700d2b00691c0348c01a4501d1f80e8dc032fe0297e00cbe8065bc052dc0196b00cb480658c032c40196100caf80656c032ae0195300ca7806534032960194900ca3806514032860194100c9f8064ec0326e0193300c9580649c050fe0687d0143b80a1d4090de0486700c2f80615c0709e0384d01c2381a1140707e0383700c0f80605c03ad601c6f00e3580719c038c601c5f00e2e80716c038ae01c5500e2980edbc076d603b6701db180ed7c076b603b5701da9806d3c0369601b4700da18129981b4ac01a4e00cb78065ac032c60195f00ca780652c0328e0194300c9f8064ec0326e0193300c9280a49003ad601d6a00e378071ac038ce01c6300e2f807174038b601c5900e2b807154038a601c5101db780edac076ce03b6301daf80ed74076b603b5901dab80ed54076a603b5100da7806d2c0368e01b4300cb780a5b8032d60196300cb100657c052bc0195d00ca780652c0328e0194300c9f8064ec0326e01933 18 262143 7 127 11 2047 21 2097151
def cc_54_11 : Nat → List (Nat × Nat) := unpackCursorV4 0x847e4fabc9e1a7ba9b370b90dd681a8e4338b265140c44bd75a62b8e554b4c9cf912d19a364842b827fcb4ef609c5b236b40678bcbba7137ff21ea2347ec4ff208ba80b1cc0f8d40d2400034 0x1d7f00ebd8075dc03ae601d6f00eb68075ac03ad201d6700eb280758c03ac205c7f0263d8131dc0b8e605c6f02e368171ac0b8d205c6702e3281718c0b8c201c5f00e2d80715c038a604b7a025bb812dd8096ce04b66025b2806d7c036ae05b4f02da38069fc0b4fc01a7b00d3b8069cc034e401a6f02d370069b40b4d801a6700d3280698c034c401a6100d3000697c034b601a5700d2980693c0349601a4700d218068ec0347401a3704d1b0065fc032f60197a00cbb80a5d8032ce0296600cb280a590032be0195e00cad806568032ae0195600ca98065480329e0394e00ca58065280328e0594600ca1806508032760193a00c9b8124d80325e0192e00c968161fc090ee0586f02c3681619c130ca0185f00c2b81613c0b08e0182f00c1380607c0303a0181704c0a8079ec03cf402e770173b00b9cc03ade01d6e00eb68075b0038fe04c7b00e3b8171cc038de01c6d0163580b1a4038ce01c650163180f184038be01c5d02e2d837164038ae01c5502e298171440b6fe04b7b025bb816dcc056de05b6d015b580ada4056ce02b65015b180ed840b6be05b5d02dad816d640b6ae05b5502da9816d440b69e01b4b00da3816d0c094f404a770253b00a9bc094da02a670153281295c094ac04a5504d2780691c0b47e05a37014bf80a5f8032f60297700cb98165c8052de0296e014b680a57c052bc0295d014ae00656c032b20195302ca90065440b2a00194f00ca580651c032860293f00c9d80a4dc032660192b04c9500a49c0524c0587f0243b80a1bc130da028670143281617c0b0ba0585704c2a82613c0308e0583f02c1b80607c0502e05c7f0263d8131dc0b8e609c6f00e368271ac078d209c6700e3282718c078c205c5f02e2e81716c118b205c570b62a81714c0b8a205b7f025bd812ddc0b6e605b6f02db6816dac076d205b6702db2816d8c076c205b5f02dae816d6c0b6b205b5702daa816d4c0b6a205b4f02da5816d1c0b68604a760252b0165fc092f60497702cb98265bc052da0996b00cb482659c052ca0996300cb081657c0b2ba0595b04cac81655c132aa0595302ca882653c132960994704ca18164fc0b2760593702c998161f80b0dc0585e02c2e0160d80b8de04c6b0263381718c118be01c5d0462d80f164118ae01c550462980f1440b6de04b6b025b3816d8c0b6be05b5d045ad80ed640b6ae05b55045a980ed440b69e08b4b02da3822d0c0b2de0496b024b381658c132be0295d044ad806564112ae0295504ca98065441129e0994b8f8a382250c1927e0593b02c9b8264cc0b0dc0585e02c1b0171bc098d604c6702e3181717c038bb8045b01e2cdfd15c038aa05c5301e28816dbc096d604b6702db1816d7c0f6ba05b5b01dac816d5c0f6aa05b5301da8816d3c1969605b47065a18129a8094ce04a660252b812958094ab7324fb21238328fc0b46e0596f024b581259c0b2c60595f014aedf856c032b37d157014aa81654c032a33a14f9a0a5c7851e0c2860c93f02c9d8164dc19266e012b658938161bc090ce0585f1702edf015ef60aaa004f460238320fc0b06e1601f0400b8135bc09ad604d67026b18131bc098d604c670263183317c198b60cc5706629812db8094cc03a5e00d2b00e9380f48c0496f024b581259c092c73915f990adc6c55e082a60c94f064a583251c1928601929014928131bc038da04c6b01e3481319c038ca04c6301e3081317c098b604c5702629812dbc0f6da04b6b01db4812d9c096ca04b6301db0812d7c096b604b57025a9832d3c196960cb47065a18129bc094dd7726d0252f812978094a57124fb11238328fc1946e0496f014b68125ac032d204967014b281258c032c20495f024ad81255c092a73814f980a5c6451e042860c93f0649d8324dc19266df12b648938121bc0d0da048670243281217c090ae0684f0342381a0fc0d06e0681f0340b8131bc098d604c670263181717c038ba05c5b01e2c81715c038aa05c5301e28812dbc096d604b67025b1816d7c0b6ba05b5b01dac816d5c0b6aa05b5301da8816d3c0b69605b4702da1812998094ac0496f024b581259c092c60595f014ae81656c032b205957014aa81654c032a20d94f04ca583651c132860593f02c9d8164dc0b26605d6f026b581359c0bac605c6f0263581319c0b8c605c5f0662d81715c198a604b66bb93700e978034ac03a4e03d230165bc092d60496702cb1cdc57e5c2b717157800a983253c0b29605947064a18064a40524a03d6f01eb700f1ac038ce03c6300e2b807154076de03b6b01db380ed8c076be03b5d01dad80ed64076ae03b5501da980ed440769e01b4b00da380ed0c0b2de0196b024b380658c112be0295d00cad806564112ae0295500ca98065440329e0194b00ca380650c0727e0193b01c9b8064cc0b0dc0585e00c2300e0d807ade03d6e01eb68071bc078d603c6900e3380f18c078c201c5f00e2e80f16c038ae01c5501db780edac076ce03b6301daf80ed74076b603b5901dab80ed54076a603b5101da7806d2c0368e03b4302d378169b4094cf7226500d2f8069740b4ae01a5501d2780691c0747e03a3702cb78065ac092ce0196302caf80a574032b60195902cab80a554032a60195100ca780652c0328e0194301c9f8064ec0726e0193300c9585249c0b0de0486702c2f8161740b0af7505501c2780611c0707e0383700c0f81c05c03afe03d7b00ebb80f5cc03ade01d6d01eb580f5a807ad203d6800eb382759803aca01d6401eb180f584078fe05c7e01e3e8171f0078f603c7a01e3b8131d8078ea04c7401e3980f1c8038de01c6e00e368071b0078d603c6a01e3480f1a0078ce04c6600e32807190078c603c6201e3080f180076fe03b7b01dbb80edcc076de03b6d01db580eda4076ce03b6501db180ed84076be01b5b00dab80ed4c0769e03b4d01da580ed240768e03b4501da180ed04094ec04a6600d2b0069180b2fe0197b024bb8065cc0b2de0296d00cb58065a4132ce0296500cb1806584032be0195b00cab80654c0729e0294d00ca58065240728e0294500ca18065040727e0193b01c9b8064cc0325204d6f026b70175b4078d603c6900e3380f18c078c201c5701db780edac076ce03b6301daf80ed6c076ae03b5301da7806d2c0368e03b43025370125bc032d60496700cb181657c032b60595700ca980653c032960194700ca180e4fc032760393700c998075fc09afc01d7d00ebe00f5ec07af201d7700eba80f5cc07ae403d7101eb80075bc07ad601d6701eb180f1fc098fc01c7d00e3e00f1ec078f403c7901e3c0071dc038ec01c7500e3a00f1cc078e403c7101e3800f1bc098dc03c6db923600f1ac078d403c670263300f194098c803c6301e3100edfc076fa03b7b01dbc80eddc076ea03b7301db880edbc076d603b6701db180ed7c036b601b5701da980ed3c0769a03b4b01da480ed1c0768a03b4301da08129f8094dc01a5600d230125fc052fa0197b00cbc8125dc052ea0197300cb88125bc032d60496700cb180657c032b60195700ca980e53c0529a0194b00ca480e51c0528a0194300ca080e4fc032760393700c998075bc07ad601d6701eb18231bc0b8dc06c6b0263501b19c098cc09c6302e3100edbc076d603b6701db180ed7c036b601b5701da980ed3c0769a03b4b01da480ed1c0768a03b4301da0d385bc032d60696700cb180657c032b60195700ca982653c0529a0194b00ca482251c0528a0194300ca080e4fc032760393700c9980e1780709c0601600eb780f5ac03ace03d6301e37dd11b8078d603c6a01e33813198078c603c6201db780edac076ce03b6301daf806d6c036ae03b5301da780ed340769603b4901da380ed140768603b41b9937dc499c034b401a5700d2b00691c0348c01a4501d1f80e8de9a2de0196ba08b380658c032be0195b00cab80654c0729e0294d00ca58065240728e0294500ca18065040727e0193b01c9b8064cc03256c812760037acc19c070be0185701c2780e1340708f7004501c1f80e0dc0303e0501701f3f80f9f807cfa01d7f00ebd8075dc03ae601d6f00eb68075ac03ad201d6700eb280758c03ac203c7b01e3d00f1e4078ee04c7601e3980f1c4078ce04c6601e3280717c038bc01c5b00e2b80714c038a401b5e02d3f0129d80b4dc05a6c03d33032990034ac03a4e01d2600e9180b4880197f00cbd8065dc032e60196f00cb68065ac032d20196700cb280658c032c20195f00cad80655c032a60194f00ca580651c032860192900c9280f5bc07ada01c6f00e368071ac038d201c6700e3280718c038c201c5f00e2d80715c038a603b6f01db680ed7c096bc03b5b01da980ed480369e01b4b00da3806d0c032de0196d00cb58065a4032ce0196500cb1806584032be0195b00cab80654c0329e0194b00ca380650c0327e0193b00c9b8064cc07cfe03e7e01f3e8075fc03afc01d7d00ebe0075ec03af201d7700eba8075cc07ae401d7101eb80075bc03ad601d6700eb180f1fc098fc03c7d01e378131b8078d603c6901e3180f188078c201c5f00e2d80715c038a601b5e0253f5b49f0094ec04a7402537012998034ac03a4e01d230065fc032fa0197b00cbc8065dc032ea0197300cb88065bc032d60196700cb180657c032b60195700ca980653c032960194700ca18064a40324a01c6f00e368071ac038ce01c6500e3180717c038ba01c5b00e2c80715c038aa01c5300e28816dbc076d604b6701db1816d7c0b6ba03b5b01dac816d5c0b6aa03b5301da8806d3c0369601b4700da18065bc032d60196700cb180657c032ba0195b00cac80655c032aa0195300ca880653c032960194700ca18064fc032760193700c998075bc03ad601d6700eb1db91bc078d76c46701e3180717c038b601c5700e29806d7ad64dc04a6600d2b00e9380f48c0196f00cb580659c032c60195f00cad80655c032a60194f00ca580651c032860192900c928075bc03ad601d6700e378071b8038be01c5e02db780edac096ce03b6300daf806d6c036ae01b5302da7816d340769603b4902da3816d140768603b4100cb78065ac032ce0196300caf80656c032ae0195300ca7806534032960194900ca3806514032860194100c9f8064ec0326e0193302c370161380b06c0181600eb78075b403ad601d6700eb280758c038de01c6e00e3680717c038bc01c5700e298071480b6de03b6b025b380ed8c036be01b5b00dab806d4c0b69e05b4d01da580ed240b68e05b4501da180ed040b4de05a6d02533d8c994034be01a5701d2780e9340b48e03a4501d1f8168dc032de0196b00cb480659c032c60196100caf80656c032ae0195300ca7806534032960194900ca3806514032860194100c9f8064ec0326e0193300c9580649c0b0de0486700c2f80615c0b09e0584d02c23da41140707e0583700c0f80605c07cfe03e7e01f3e8075fc03afc01d7b026bd0075dc03aec01d7302eb90075bc03adc01d6d00eb60075ac0fad401d69066b400759c03acc01d6500eb200758c0bac401d6102eb00071fc038f601c7700e398071bc038da01c6b00e3480719c038ca01c6300e3080edec076f403b7901dbb812dd8076e603b7101db3812d98076ca01b5f00daf00ed740b6b801b5b00dac806d5c036aa01b5300da900ed44076a001b4f00da7006d2c0368e01b4300da10169fc094ee05a6f03d3681e99c134ca01a5f00d2f00e9740349e01a4e00d2100e8fc0746e0197f00cbd8065dc032e60196f00cb68065ac032d20196700cb280658c032c20195f00cae80656c032b20195700caa80654c032a20194f00ca580651c032860193f00c9d8064dc032660192b00c938161fc090ee0586f03c3681e19c190ca0185f0442e80615c030aa0184f00c2380e0fc0706e0181f00c0b8075bc03ad601d6700eb18071bc038dc03c6b01e3500719c038cc01c6300e3100717c038bc01c5700e29807148076de04b6e01db5806d9c076c603b6200daf806d6c036ae01b5301da780ed340369601b4900da3806d140368601b410253781299c034be01a5701d2780e9340748e03a4501d1f80e8dc032de0196b00cb380658c032be0195b00cab80654c0329e0194d00ca58065240328e0194500ca18065040327e0193b00c9b8064cc03256019270243781219c030be018570342781a1340d08e0684501c1f80e0f40706e0683500c0f80605c07cfe03e7e01f3e8075fc03afc01d7d00ebe0075ec09af401d79026bc0075dc03aec01d7500eba0075cc09ae401d71b32b80075bc03adc01d6b026b500759c03acc01d63026b10071fc038fa01c7b00e3c8071dc038ea01c7300e388071bc038d601c6700e3180edfc096fc03b7d01db7812db8076d603b6901db180ed88076c201b5f01dae806d6c036b201b5700daa806d4c076a201b4f00da5806d1c0368604a7f04d3e8129dc094ea04a6f0253380697c034bc03a5d00d278069380348403a3f01d1b8065fc032fa0197b00cbc8065dc032ea0197300cb88065bc032d60196700cb180657c032ba0195b00cac80655c032aa0195300ca880653c032960194700ca18064fc032760193700c998064ac0324e0487f0343e8121dc090ea0486f0243380617c0d0ba0185700c2a80613c0308e0383f01c1e80e0dc0d06a0181f00c0b8075fc03afc01d7b026bd0075e409af001d7700ebb0075cc0bae401d7102eb80075bc03adc01d6d00eb60075ac09ad401d6901eb400759c03acc01d6500eb200758c07ac401d6101eb00071fc038f601c7700e398071bc038da01c6b04e350071a4078d001c6700e33007194038c801c6300e30816dfc076f604b7701db9816dbc0f6da03b6b01db4816d9c0f6ca03b6301db0806d7c0b6ba01b5b00dac806d5c036aa01b5301da8806d3c0369601b4700da18129d8094cc01a5e00d270065fc032f60197700cb98065bc032da0196b00cb480659c032ca0196300cb080657c032ba0195b00cac80655c032aa0195300ca880653c032960194700ca18064fc032760193700c998075bc03ada01d6b00eb3807594098de04c6e02e3680717c096de03b6b025b380ed8c036be01b5b00dab806d4c0b69e03b4b02da380ed0c094dc0196f00cb58065a4032ce0196300cb080657c032b60195700ca980653c032960194700ca18064fc032760193700c998075fc03afc01d7d00ebe0075ec07af401d7901ebc0075dc03aec01d7500eba0075cc09ae401d7101eb80075bc03adc01d6b026b50075a409ad001d6700eb300758c09ac401d61b1ab00071fc038fc01c7d00e3e0071ec038f201c7700e3a8071cc098e401c7101e380071bc038d601c6700e31812dfc0f6fa03b7b01dbc812ddc096ea03b7301db8812dbc076d604b6701db1806d7c0b6ba01b5b00dac806d5c036aa01b5301da8806d3c0369601b4700da18129f8094dc01a5e00d270268d8032fe0197d00cbd8065e4032ee0197500cb98065c4032de0196b00cb380658c032be0195d00cad806564032ae0195500ca98065440329e0194b00ca380650c0327e0193b00c9b8064cc0324a09d6f02eb701b5ac09ad406d67026b302358c0bac401c6f00e3580719c038c608b6f01db581ad9c076c608b5f02dae80ed6c076b208b5702daa80ed4c076a201b4f00da5806d1c036860196f00cb580659c032c60195f00cae80656c032b20195700caa80654c032a20194f00ca580651c032860193f00c9d8064dc03266bf06e00c2b006118f206c0181e00eb78075b803ad604d6a00eb380759803ac76856200e378071ac038ce01c63b39b780edaeca6ce03b6300daf81ed74036b601b5900dab806d54036a603b5100da7806d2c0368e01b43b2137d8899c034be01a5e01d2e80693c0349c01a4201d1fd548dc032de0196b00cb380658c032be0195d00cad806564032ae0195500ca98065440329e0194b00ca380650c0327e0193b00c9b8064cc03256019275f037ac419c030bf6105d00c2b8061540309e0184701c1f9e00dc0303e0181700e3780f1ac078d201c6701e3180f184038be01c5d01e2d80f164038ae01c5501e2980f144076de03b6d01db580ed9c076ca03b6301daf80ed74076b603b5901dab80ed54076a603b5101da7806d2c0368e03b4302cb78065ac092ce0196302caf80a574032b60195902cab80a554032a60195100ca780652c0328e0194301c9f8064ec0726e01933 19 524287 7 127 11 2047 21 2097151
def cc_54_12 : Nat → List (Nat × Nat) := unpackCursorV4 0x8eaa31a4622917421e17efa8f80bddaeaba2a671364da7019b33b0e505caa4ac79d4dd62744f4bc588df3502b29ef2c3919a6c6b8c3aa956e124cc243cb8726a8ce2d149a61c9941cb900072 0xf5bc07ad603d6701eb180f1bc078d603c6701e3180f17c078b603c5701e29816dbc0b6dc04b6702db1816d88076be03b5e01dad806d68076ae01b5601da980ed480769e03b4e01da380ed0c0768405a6f02d3701299c0b4c403a5f01d2d00e95c074ac03a4f01d2700e91c0748403a3f01d1f00e8f40b2de0496b024b381658c072be0395b01cab80e54c0729e0394b01ca380e50c1327e0293d04c9d8064e41326e0293504c998064c41525a0992b04c9382a4940b0de0486701c2f80e15c0709e0384704c1fe7c0f41306e3b03504c0f82605c078be03c5b01e2b80f14c076be03b5b01dab80ed4c0769e03b4b01da380ed0c0b2be0495b024ab81654c0729e0394b01ca380e50c0727e0393b01c9b80e4cc07ade03d6b01eb380f58c078de03c6b01e3380f17c078b603c5701e29816dbc0b6dc03b5f01daf00ed6c036b403b5700dab00ed4c076a403b4f01da70228d80b2de0496b024b381658c072be0395b01cab80e54c0729e0394b01ca380e50c1327e0293d04c9d8064e41326e0293504c998064c40706c0383401eb780f5ac07ace03d6301e3780f1ac078d403c670263300f18c078be03c5e01e2d80f15c078a603c5202db7816db8096ce05b6302db100ed7c076bc03b5b00dad00ed5c036ac03b5301da900ed3c0769c03b4701da180ed080b4de04a6701d2f80e95c0749e03a4707d1fe708f41146e3b23502cb78125ac092ce0596301caf80e56c072ae0395301ca780e52c0728e039430549f80a4f411276019390449b80a4d415266019310549582a49c0b0de0586e0243501219c090cc0586201c2f80e178070b40385701c2b00e1480709e0384e01c2500e11c0708c0384201c1f80e0f80707a6302e034150e80980d0440681f0540f01a0680d02e0a8160340900f5bc07ad603d6701eb180f1bc078d603c6a01e33813198078c603c5f01e2f00f16c078ae03c5301e29016dbc096ce05b6301daf80ed6c076ae03b5301da780ed1c0768605a6f02d3701299c094cc05a6302d3100e97c074bc03a5b00d2d00e95c034ac03a5301d2900e93c0749c03a4701d2300e90c074840596f024b380e57c072ae0394f01ca38224e81126e08936044938224981124a0586f0243581219c0b0c60385f01c2d80e15c070a60384f01c2580e11c070860a83f0441d8220dc150660a82f0141682a0ac030520a8270141282a08c030420a81b0540b80f5bc07ad603d6701eb180f1bc078d603c6a01e33813198078be03c5e01e2d80f15c078a603c5202db780ed7c076b603b5701da980ed3c1147c0596e024b300e578032ac0394e01ca30224d80b0de0486b0243381618c070be0385b01c2b80e14c0709e0384b01c2380e10c1107e0883b0441b8220cc030320281501eb780f5ac07ace03d6301e3780f1ac078d403c670263300f18c078be03c5e01e2d80f15c078a603c5202db7816db8096ce04b6602db1816d88076be03b5e01dad806d68076ae01b5601da980ed480769e03b4e01da380ed180768603b4202d3781299c0b4c603a5f01d2d80e95c074a603a4f01d2380e90c0b2de0496701caf80e55c0729e039470449f8224f81f27a0892f0449702248b2e2400586f0243581219c0b0c60385f01c2d80e15c070a60384f01c2580e11c070860883f0141e8220ec03072088370141a8220cc030620882f0441582209c110460a81b0540b80f17c078b603c5701e2980ed7c076b603b5a01dab812d580769e03b4e01da580ed1c0768603b4202d2f80e93c0749603a4701d2180e8fc1125c0585f0242d81215c0b0a60384f01c2580e11c070860383f01c1d80e0dc070660882f0441582209c1104603d6f01eb580f59c07ac603c6f01e3580f1a8078ce04c6601e2f80f178078b603c5701e2980f1480b6de03b5f01dad80ed5c076a603b4f0451b65c8d00b2dc0496601caf0065580729c0394c01ca30165101f27c0586f0243581219c0b0c60385f01c2d80e15c070a60384f01c2580e11c070860a83f0441d8220dc15066018190140a80f17c078b603c5701e2980ed7c076b603b5a01dab812d58076a603b4f01da700ed2c0768e03b4301da101697c094b604a5702d2980e93c0749603a4701d2180e8fc0747603a3701d1981657c092b60495702ca980e53c072960394701ca180e4fc072760393701c99e684bf3225798127cb09181617c090b60485702c2980e13c070960384701c2180e0fc070760383701c1982a0bc150560a8270541182a07c150360a8170540980f5bc07ad603d6701eb180f1bc078da03c6b01e3500f19c098cc03c6501e2f80f178078b603c5701e2980f148076de07b6e01db680ed7c076bc03b5b00dad00ed5c036ac03b5301da900ed3c0769c03b4d02d378129ac094ce05a6301d2f80e96c074ae03a5301d2780e92c0748e03a4301d1f80e8f40747603a37cf11a80e8cc0b2de0496b024b381658c072be0395b01cab80e54c0729e0394b01ca380e50c0727e0293d01c9d8064e40726e0293501c998064c41525e0a92b0549382a48c0b0de0486b0243381618c070be0385b01c2b80e14c0709e0384b01c2380e10c0707e0383d01c1d80e0eb3a0700383701c1b66c0d72a068038333101781a0ac7204e068230540f81a06c1502e0681301eb780f5b807ace03d6301eb10071bc078d601c6701e3180717c038ba03c5b01e2c80715c038aa03c5301e2880edbc076d603b6701db180ed7c076ba03b5b01dac80ed5c076aa03b5301da880ed3c0369601b4701da18169bc0b4dc03a6702d3101697c0b4bc05a5d01d278069280348e01a4601d1f80e8dc0b2de0196b024b380658c132be0295d00cad806564132ae0295500ca98065440329e0194b00ca380650c0727e0193b01c9b8064cc032560992702c3781219c130be0885d04c2b8221540709e0184701c1f80e0dc0303e0981701eb780f5b807ace03d6301eb10071bc078d601c6701e3180717c038ba03c5b01e2c80715c038aa03c5301e2880edbc076d603b6701db180ed7c076ba03b5b01dac80ed5c076aa03b5301da880ed3c0369601b4701da18169bc094ce08a5f04d2e82295c114aa03a4f00d2380e8fc0746e0596f00cb581259c032c60895f014ae80656c032b208957014aa80654c032a20194f00ca580651c032860393f00c9d80e4dc032660192b09c938161bc0b0dc0386702c3101617c0b0bc0585d01c278061280308e0184601c1f80e0e80706e0383600c0f81a05c07ade03d6e01eb68071bc078d603c6900e3380f18c078c201c5f00e2e80f16c078b201c5700e2a80f14c078a203b6f01db680edac076ce03b6501db1806d7c036ba03b5b01dac80ed5c036aa03b5301da880ed3c0369601b4701da18169bc094d604a6702d3181697c0b4ba05a5b02d2be4c9540b4a603a4f00d2580691c0748603a3f01d1d80e8dc074660596f00cb581259c032c60595f014ae80656c032b205957014aa80654c032a20194f00ca580651c032860393f00c9d80e4dc03266e512f00c95b4849c032460586f0243581219c0b0c60585f02c2e81616c0b0af9205502c2980e13c030960184701c2180e0fc070760383701c199840bc0d056380270341180607c0d0360a01700c098075bc07ad601d6701eb18171bc0b8dc06c6b0263501b19c098cc05c6302e3100f17c078bc03b6f01db580ed9c076c601b5b00dab80ed4c0768e03b4502cb78065ac0d2ce0196300caf80656c032ae01953044a780a5340329601949044a380a514032860194101c9f8064ec0726e01933044230075bc07ad601d6701eb18171bc0b8dc0cc6b0263502719c098cc05c6302e3100f17c078bc01c5701e2980f148076de03b6b01db380ed8c076be01b5b00dab80ed4c0769e01b4d01da5806d1c0368a05a6f04d3380e97c074bc01a5701d2900e93c0749c03a4d01d1f80e8e80746e03a3602cb78065ac192ce0196300caf80656c032ae0195304ca780a534032960194904ca380a514032860194101c9f8064ec0726e0193300c9582649c0b0de0c86701c2f80615c1309f9004d04c238dc1140707e0383d01c1b81e0d40303e0981700eb780f5ac03ace03d6302e378171b80d8d604c6a036338131980b8c605c6201e2f80f178076de03b6b01db380ed8c036b601b5701da980ed1c0768a08a4602cb78065ac0d2ce0196300caf80656c032ae0195304ca780a534032960194904ca380a514032860194101c9f8064ec0726e0193300eb780f5ac03ace03d6302e378171b80d8d604c6a036338131980b8c605c6201e2f80f178038ae03c5301e2900edbc076d603b6701db180ed7c036b601b5701da980ed3c0369a03b4b00da3806d140b4de06a6701d2f80695c3149f8e24d045238dc9140747e03a3702cb78065ac0d2ce0196300caf80656c032ae0195309ca780a5340329601949044a380a514032860194101c9f8064ec0726e0193300c95b4049c0b0de0686701c2f80e178030ae0385201c2780e1380709a0383f01c1d00e0dc0706c0181f0440b8075bc07ad601d6701eb180f1bf228dc03c6b01e3500f19c098cc03c6301e3100f17c078bc03c5d01db781edb8076d603b6701db180ed88036b601b5a01dac806d5c036ac03b5301da8806d1c0368c01b4502d378329ac194ce05a6301d2f80696c034ae03a5301d2780e9340749603a47c792280e90c0747e03a3b01d1b80e8cc0b2de0196b064b380658c032be0195b00cab80654c0729e0294d00ca58065240728e0294500ca18065040727e0193b01c9b8064cdc625e0192b6789380648c0b0de0c86b0643381618c070be0185b00c2b80e14c0709e0384d01c2580e11f1a08a0384301c1f80e0f4070760383703c1a80e0ccbe05e4a02b1b01388408c0303e0f01b0480b80604c03ade01d6b00eb380758c078de03c6b01e3380f18c038be01c5700e29822dbc0b6dc06b6b025b501ad9c096cc08b6302db1006d5c036ac03b4f01da70065bc032d60196700cb180657c032b60195700ca980653c032960194700ca18064fc0327a0193b00c9c8064dc0326a0193300c988220d803ade01d6b00eb380758c078de03c6b01e3380f18c038be01c5b00e2b80714c116de05b6e065b5812da8116ce04b66065b1816d88036be01b5b00dad006d5c036ac03b4f01da700ed1c0768603b4204d3782699c034be01a5a00d2b8069580749e03a4e01d2380e9080347e01a3e00d1e8065bc032d60196700cb180657c032b60195700ca980653c032960194700ca18064fc0327a0193b00c9c8064dc0326a0193300c988064ac0324e0886f0443380617c030ae0384f01c238220ff1607a088371a81a80607c0302e01d6f00eb580759c03ac603c6f01e3580f19c078c601c5f00e2b80714c136de05b6e035b5812da80d6ce04b6604db1816d88036ae01b5601da780ed381146c0196f00cb580659c032c60195f00cad80655c032a60194f00ca580651c032860193f00c9e8064ec032720193700c9a8064cc032620183600c1a0075bc03ad601d6700eb180f1bc078d603c6701e3180717c038bc01c5b00e2b80714c038a408b6f02db701adac096d406b67025b3032d8c0b6c401b5f00dad806d68036ae01b5601da780ed380768e03b4301da10329bc0d4ce01a5f00d2b80e93c0748e0fa3fc491e8228dc6a46a0196f00cb580659c032c60195f00cad80655c032a60194f00ca580651c032860193f00c9e8064ec032720193700c9a8064cc032620192b00c9381a1bc190d4068670643300617c030b40185700c2b00e13c0709c0384701c210060fc0307c0183d2e8170800880303e0181e00c0b80604803ade01d6b00eb380758c078de03c6b01e3380f18c038be01c5e01e2e80715c038aa01c5300e29006dbc196dc01b6b00db5006d9c096cc01b6300db1006d5c036ac01b5500da780ed380369a0ca6f0653583299c194c601a5f00d2d80695c034a603a4f01d2580e91c0748601a3f00d1e8068ec0346f8a23500d198065bc032d60196700cb180657c032b60195700ca980653c032960194700ca18064fc0327a0193b00c9c8064dc0326a0193300c988064bc032560192700c918321bc190d60c8670643180617c030b60185700c2980e13c070960384701c218060fc0307a0183b00c1be200d4030665c02f240158d009c3c0460181f00c0d80605c0302601d6f00eb70075ac07ad401d6700eb300758c07ac401c6f00e3580719c038c601c5f00e2f007174076de03b6b01db380ed8c036be01b5e01dae806d3c0369c01b4b00da4806d0c0368403b4102d378329ac194ce05a6300d2f80e974034b601a5700d2a80694c0349e01a4b00d2380690c0747e03a3b01d1b80e8cc032de0196b00cb380658c032be0195d00cad806564032ae0195500ca98065440329e0194b00ca380650c0327e0193b00c9b8064cc0325e0192b00c9380648c0b0de0c86b0643381618c030be0385d00c2d80615c030aa0185300c2780612c0308e0184301c1f80e0ec0706e038332d81791c0ac6604e1d02300c0f80606c0302e0181300eb780f5ac03ace03d6301e3780f1ac078ce03c6301e2f80716c038ae08b6f02db701adac096d406b67025b3022d8c0b6c403b5f01daf00ed3c0769c0996f00cb581a59c032c60195f00cad80655c032a60394f00ca580e51c032860893f0149e8064ec03272089370149a8064cc032620886e01c230220d803ade03d6b00eb380f58c078de03c6b01e3380f18c078be01c5b00e2b80f14c136de05b6e065b5812da8136ce04b66065b1816d88076be03b5e00dab80ed4c076a401b4f00da700ed1c0768601b4204d378329a8134ce0ca6601d2f80e978034ae03a5201d2780e9380748e03a4201d1f80e8f80747a0a96f00cb582a59c032c60195f00cad80655c032a60394f00ca580e51c032860993f0149e8064ec03272099370149a8064cc032620a92d00c9582649c1524a0c86f0643380e17c030ae0384f01c2680e11cf808a0983fc281e8260dc6406a5a02d1881280607c1302e01d6f01eb580759c07ac603c6f01e3580f19c078c603c5f00e2d80715c136de05b6e035b5812da80d6ce04b6604db1816d88076be03b5e01da780ed38134dc08a3604cb78065ac0d2ce0196300caf80656c032ae0195301ca780652c0728e0194304c9f80a4f4032760193904c9b80a4d4032660193100eb780f5ac03ace03d6301e3780f1ac078ce03c6301e2f80716c038ae03c53045b7816db80d6d604b6a035b3812d98196c605b6201daf80ed78036ae03b5301da9006d3c0369c03b4701da1806d08194de06a6701d2f80695c0749e03a4707d1fe0c8f41146e32235054b78065ac0d2ce0196300caf80656c032ae0195301ca780652c0728e019430549f80a4f403276019390449b80a4d4032660193100c9582a49c0d0de0c86a03433832198070be0385e00c2b80e1480709e0384e01c2380e1080707e0383e01c1e9180a86004c0181f0540d02205c1502c01d6f01eb580759c07ac603c6f0663700f1ac078ce03c6301e3100f17c078ba01c5b00e2d00715c038ac03c5501db7832db8076d603b6a01db3812d98076c603b6201daf80ed78076ba01b4f00da7006d34194de0ca6b0653383298c074be01a5b00d2b80e94c0749e03a4b01d2380e90c0747e03a3d01d1d80e8df0846a03a33054b78065ac152ce0196300caf80656c032ae0195301ca780652c0728e0194301c9f80a4f4032760193901c9b80a4d40326601931054978064ac1524e01923064378321ac190ce0c86301c2f80616c030ae0385301c2780e13407096038473d82280e10c0707e0383d01c1d80e0df0406a038332c0179100ac5e04e1b02300c0f82a06c1502e0181300ebf8175f807af601d7701eb980f5c803ade05d6e00eb68175b003ace01d6501eb180f58807ac203d6001e3f80f1ec078f401c7700e3b00719c038cc01c6500e3200f17c078bc03c5d01dbf80edec076ee03b7301db780edb4076d603b6901db380ed94076c603b6101daf806d6c036ae03b5301da780ed340769603b4901da380ed140768603b410253d0129dc094ec04a6702533012994074be03a5d00d2b8269540749e03a4d01d238129140747e03a3702cbf8065ec092ee0197302cb78165b4032d60196902cb3836594032c60196100caf80656c032ae0195301ca780a534032960194901ca380a514032860194101c9f8064ec0726e0193300c9582649c0b0fe0487702c378161b40b0ce0886501c2f80615c0709e0384d01c238361140707e0383700c0f82605c03cfe03e7d00f3b8079d403ce601d7f00ebf00f5f407af801c7f00e3f0071f4038de01c6e00e3580719c038c605c6200e2f807178038ba01c5c00e2d807164038a605c5200e28817140036fe05b7d00dbd806de4036ee01b7500db980edc40b6de03b6b025b380ed8c0b6be05b5d01dad80ed640b6ae05b5501da980ed440369e01b4b00da3806d0c034fe04a7d00d3b8069d4094d404a670253301295c094ac04a5500d278269340348e01a4501d1f8168dc032fe0197d00cbd8065e4032ee0197500cb98065c4032de0196b00cb380658c032be0195d00cad806564032ae0195500ca98065440329e0194b00ca380650c0327e0193b00c9b8064cc032560192700c3f8461f4030ee0187502c3781219c0b0be0585d02c2b85a1540309e0184701c1f8160dc0303e01817 19 524287 7 127 11 2047 21 2097151
def cc_54_13 : Nat → List (Nat × Nat) := unpackCursorV4 0xcb6bb074dbc0bac8cfa618671cd90586233c814f1dcd16a995942c5ab4d54ac4ad4cfae13258ca1cf1c18c47d10598c002c 0x5d6f02eb70071ac038ce01c6300e2b8071540b6de03b6b025b380ed8c0b6be05b5d01dad80ed640b6ae05b5501da980ed440369e01b4b00da3806d0c032de0196b00cb380658c032be0195d00cad806564032ae0195500ca98065440329e0194b00ca380650c0327e0193b00c9b8064cc110ac0184e00c0b00f5bc07adc04d6702eb180f588038de01c6b00e3380718c038be01c5d00e2d80715c038aa05b6f01db5812d9c076c605b5f02dae80ed6c076b205b5702daa80ed4c076a201b4f00da5806d1c0368605a6f02d3701299c0b4c401a5f00d2f0069740349e01a4a00d238069180747e05a3700cb78065ac032ce0196300caf806574032b60195900cab806554032a60195100ca780652c0328e0194300c9f8064ec0326e0193300c9580649c0b0de0486704c2fed0174130ae4205500c2780611c0707e0583700c0f80605c0bade05d6e00e3580719c038c601c5700e2a816dbc076d604b6701db1816d7c0b6ba03b5b01dac816d5c0b6aa03b5301da8806d3c0369601b4700da18229580349c0196f00cb580659c032c60195f00cae80656c032b20195700caa80654c032a20194f00ca580651c032860193f00c9d8064dc032660192501eb780f5b809ace05d6301eb10071bc038d601c6700e3180717c038ba01c5b00e2b8071540b6de03b6b025b380ed8c0b6be05b5d01dad80ed640b6ae05b5501da980ed440369e01b4b00da3806d0c0b4de04a670952fec8974114ae4225500d2780691c0747e05a3700cb78065ac032ce0196300caf806574032b60195900cab806554032a60195100ca780652c0328e0194300c9f8064ec0326e0193300c9580649c0b0de0586e02433816188030be0185e00c2e80613c030940184700c2300e0fc0b0740583702c1b00607c0302e01d6f01eb70075b4038d604c6a00e3480719c038cc01c6300e3080715c038ac01c5502db780edac096ce03b6300daf806d74036b603b5900dab81ed54036a601b5100da7806d2c0368e01b4302d378129ac094ce05a6300d2f806974034b601a57d992a80694c0349e01a4b00d2380690c0747e05a3b02d1b80e8cc032de0196b00cb380658c032be0195d00cad806564032ae0195500ca98065440329e0194b00ca380650c0327e0193b00c9b8064cc0325e0192b00c9380648c0b0de0486b0243381618c030be0185d00c2d80615f620aa0185300c2780612c0308e0184301c1f8160ec0b06e038333481781a0ac8204e0682300c0f80606c0302e0181300eb780f5ac03ace03d63026378131ac038d401c6700e3300f17c078bc01c5701e2980f148076de03b6b01db380ed8c076be01b5b00dab80ed4c0769e03b4d01da580ed240768e03b4501da180ed04094de04a6a02533812998074be03a5e00d2b80e9480749e03a4e01d2680e8fc0746e0496f00cb581259c032c60195f00cad80655c032a60994f014a680652c0329209947014a280650c032820393f00c9d80e4dc032660192b04c938121bc090ce0385f00c2b81a13c0d09a068470342280e0fc0706e0181f0340b8075bc09adc01d6d00eb380759407ac603d6200e33807198038ca03c5f01e2f00f174076de03b6b01db380ed8c076be01b5b00dab80ed4c0769e03b4d01da580ed240768e03b4501da180ed04094de04a6b0253381298c074be01a5b00d2b80e94c0749e03a4d01d2580e91f5e48a03a4301d1f80e8ec0746e03a33024b78065ac092ce0196300caf80656c032ae0195301ca780a534032960194901ca380a514032860194101c9f8064ec0726e01933760978064adb424e01923024378121ac090ce0486301c2f80616c030ae0385301c2780e13407096038470342280e10c0707e0383b01c1b80e0cc0d05e0682b0341381a08c0303e0681b0340b80604c078be03c5b0262b81314c036be01b5b00dab806d4c0369e01b4b00da3806d0c0b4be07a5b03d2b81694c0949e04a4b0252381290c0347e01a3b00d1b8068cc032be0195b00cab80654c0329e0194b00ca380650c0327e0193b00c9b8064cc0325e0192b00c9380648c0b0be0685b0342b81614c0909e0484b0242381210c0307e0183b00c1b8060cc0d05e0682b0341381a08c0303e0181b00c0b80604c038be01c5b00e2b80714c076be03b5b01dab80ed4c0369e01b4b00da3806d0c094be04a5b0252b81294c0349e01a4b00d2380690c0747e03a3b01d1b80e8cc032be0195b00cab80654c0329e0194b00ca380650c0327e0193b00c9b8064cc0325e0192b00c9380648c090be0485b0242b81214c0309e0184b00c2380610c0707e0383b01c1b80e0cc0d05e0682b0341381a08c0303e0181b00c0b80604c07ade03d6d026b380f59409ac601c6f00e3680719c038ca01c6300e2f80716c038ae01c5304db7816db4076d603b69065b3816d94076c603b61025af80ed6c096ae03b5300da7806d2c0368e01b4300d33806998034ca04a5f0252d01295c094ac01a4f00d2500691c0348c03a3f04d1b8065bc032da0196b00cb480659c032ca0196300cb080657c032b60195700ca980653c032960194700ca18064fc032760193700c998064ac032520192700c9081a1bc0d0da068670343281217c090ae0184f00c2380e0fc0d06e068290341080607c0302e01d6f00eb700f5b4038de01c6e00e3680717c038bc01c5b00e2c80714c098a401c5100db7806db80f6dbad36c00db5806da4036ce01b6500db1806d88076c3ac360025af80ed6c096ae03b5300da7806d2c0368e01b4300d37eac9b4034d601a6700d3280698c094be04a5b0252b81294c0349e01a4b00d2380690c0747e0ca3b0651b80e8cc032de0196d00cb58065a4032ce0196500cb1806584032be0195b00cab80654c0329e0194b00ca380650c0327e0193b00c9b8064cc0325e0192b00c9380648c030de0686d00c3580619c030ca018630242f81216c090ae0485300c2780612c0308e0184301c1f81a0ec0d06e038330341781a0ac0d04e0682300c0f80606c0302e0181300eb780f5ac03ace05c6f02e3700f17c078bc03b6f01db580ed9c076c603b5f00dad806d5c076a603b4f01da680ed2c0769203b4701da280ed0c076820596f00cb581259c032c60195f00cad80655c032a60894f014a680652c0329208947014a280650c032820393f00c9d80e4dc032660884600eb780f5ac03ace03d6300e378071b8098ce05c6300e3100f17c078bc01c5701e2980f148076de03b6b01db380ed8c076be01b5b00dab80ed4c0769e03b4d01da580ed240768e03b4501da180ed040b4de05a6e02533816988074be03a5e00d2b80e9480749e03a4e01d2680e8fc0747403a3701d1b0165bc032d60496700cb180657c032b60195700ca982653c0529a0194b00ca482651c0528a0194300ca080e4fc032760393700c99bac4b403256099276c0928161bc090ce0385f00c2b82613f5209a098472002280e0fc0706e6802d1f81280607c1302e01d6f01eb580759c0b8de05c6e01e2f80f178076de03b6b01db380ed8c076be01b5b00dab80ed4c0769e03b4d01da580ed240768e03b4501da180ed041148c0596f00cb581259c032c60195f00cad80655c032a60994f014a680652c0329209947014a280650c032820393f00c9d80e4dc0326601d6f01eb580759c07ac601c6f00e3701319c0b8c601c6201e2f80f178038ae03c5301e2900edbc076d603b6701db180ed7c036b601b5701da980ed3c0769a03b4b01da480ed1c0768a03b4301da08169bc094ce03a5f00d2b86293f4e49a08a472012280e8fc0746e0596f00cb581259c032c60195f00cad80655c032a61394f014a680652c0329208947014a280650c032820393f00c9d80e4dc032660192b6b8938161bc0b0dc0486702c3100e17c070bc0185701c2900e13c0709c0384d01c1f80e0e80706e03836034150f80980303e0681a0340b83405803ade01d6d01eb580f5a803ace04d6600eb28071bc038dc01c6d01e2f80f178078ba03b6f01db580ed9c076c603b5f00dad806d5c076a603b4f01da680ed2c0769203b4701da280ed0c0768205a6f0253581299c0b4c603a5f00d2d80695c074a603a4f01d2680e92c0748fa824501d2180e8fc0747603a3701d198165bc032d60496700cb180657c032b60195700ca980e53c0529a0194b00ca480e51c0528a0194300ca080e4fc032760393700c99ba44bc03256d612700c918161bc090d60486702c3180e17c030b60185701c2980e13c0709a0384b01c23e98114070860383f01c1d80e0dc070666602f034158f409c0d0460181f0340d83005c0302603d6f01eb700f5b40b8de03c6b0263380f18c0b8be01c5d01e2d80f1640f8ae01c5501e2980f144076d604b6a01db4812d9c096cc03b6301db0812d5c096ac04b5501da781ed380769603b4701da1832d080b4de04a6b0253381698c0b4be07a5d03d2d81e95c194aa05a5301d27db892ece48e03a4301d1f8168ec0b46e03a3302cb78125ac092ce0596302caf80a5740f2b60195903cab80a5540b2a60195101ca782a52e4c28e0394301c9f8164ec0b26e039337409782a4adaa24e0a92302c378121ac090ce0586302c2f81e1740d0b6078570642a81614c0709e0684b4702380e10c0707e0583b02c1b80e0ccca05e0682b1e01381a08c1503e0681b0580b81a04c07ade03d6b01eb380f58c078de03c6b01e3380f18c078be03c5b01e2b80f14c096de04b6b025b5012d9c096cc03b5f01daf00ed6c036b403b5700dab00ed4c076a403b4f01da700ed1c0768603b42025378129a8094ce04a6601d2f80e95c0749e03a4e01d2380e9080747e03a3e01d1e8125bc092d604967024b180e57c072b60395701ca980e53c072960394701ca18164fc0527a0593b00c9c8164dc0526a0593300c988264ac1324e0486f0243380e17c070ae0384f01c2680e11c0b08a0583f0341e8160dc0b06a0681f0340b80f5bc07ad603d6701eb180f1bc098dc03c6d01e3380f194078c603c6201e2f80f16c078ae03c5301db3812d98076ca03b5f01daf00ed6c036b403b5700dab00ed4c076a403b4f01da700ed34094de04a6b0253381298c074be03a5b01d2b80e94c0749e03a4b01d2380e90c0747e03a3d01d1d80e8df4646a03a33024b78125ac092ce0496301caf80e56c072ae0395301ca780e52c0728e0394301c9f80a4f4072760193901c9b80a4d407266019310549782a4ac1524e0a923024378121ac090ce0486301c2f80e16c070ae0385301c2780e13407096038470342280e10c0707e0383d01c1d80e0dc0d06a038330341781a0ac0d04e068230340f81a06c0d02e0681301eb780f5b409ace03d65026b18271bc038da03c6b01e3484719c038ca03c6301e3081317c078b604c5701e29816dbc0b6da05b6702db280ed8c096be03b5b025ab80ed4c0769e03b4b01da380ed0c094ce04a660253281297c094b404a570252b00e93c1348e03a3f02d1d0168dc0b46c0996f014b68265ac032d209967014b282658c032c20495f024ad81255c092a60394f04ca5c8851c072860393f02c9d8164dc072660992b04c9381a1bc0d0da068670343281217c090ae0384f0342380e0fc0d07a058370341a81a0a40d0420681f0340b80f5bc07adc03d6d026378071b4078d603c6902633807194078c603c610262f80f16c098ae03c53025b7812db80f6da04b5f025af00ed6c076b203b53025a900ed440769e03b4b01da380ed0c094dfa126d0253581299c094ca04a630252f81296c094ae04a5301d27db092eca48e03a4301d1f8168ec0b46e03a33024b780a5b4092d601969024b380a594092c601961024af81256c092ae0495301ca782a52e4228e0394301c9f8164ec0b26e039337309782a4ada624e0a9230243781a1b4090d6048670243281218c090be0485b0242b81214c0709e0684b0342380e10c0707e0683d02c1d8160dc0d06a038330341781a0ac0d04e068230340f81a06c0d02e0681301eb780f5ac07ace03d6301e3780f1ac078ce03c5f01e2d80f15c078a605b6f02db700ed7c076bc03b5b00dad00ed5c036ac03b5301da900ed3c0769c0596f024b581259c0b2c60395f01cad80e55c072a60394f01ca580e51c072860893f0149e8224ec03272089370149a8224cc0326208836 18 262143 7 127 11 2047 21 2097151
def cur_54 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_54_13 (Nat.sub p 416)) (cc_54_12 (Nat.sub p 384)) (Nat.blt p 416)) (Bool.rec (cc_54_11 (Nat.sub p 352)) (cc_54_10 (Nat.sub p 320)) (Nat.blt p 352)) (Nat.blt p 384)) (Bool.rec (Bool.rec (cc_54_9 (Nat.sub p 288)) (cc_54_8 (Nat.sub p 256)) (Nat.blt p 288)) (cc_54_7 (Nat.sub p 224)) (Nat.blt p 256)) (Nat.blt p 320)) (Bool.rec (Bool.rec (Bool.rec (cc_54_6 (Nat.sub p 192)) (cc_54_5 (Nat.sub p 160)) (Nat.blt p 192)) (Bool.rec (cc_54_4 (Nat.sub p 128)) (cc_54_3 (Nat.sub p 96)) (Nat.blt p 128)) (Nat.blt p 160)) (Bool.rec (Bool.rec (cc_54_2 (Nat.sub p 64)) (cc_54_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_54_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 224)
def f_54 : Nat → Nat × Nat := unpackForestF 0xda05dd8a55d925dd885500c5fd7a4500c5bd5b6cd5b60d5a6d00c57d484dd3245d3a4dd304500c5300b5fd1a3500b5bd0a6d00b57cf83dcaa35ca838ce23dca835cb12fcb12bcb127cba34cb123ca83400b53c9255c9055c6c6ec804dc6a45c724dc684500b4fc583dc4235c4a3dc403500b4b00b47c283dc1235c1a3dc103500b43bdc5bbdc57bd95bbd957bd857bd85500a5f00a5b00a57bba6e00a53ba855b846eb826fb946cb8267b804500a4fb5c6fb6a7cb5c67b5a6e00a4bb4845b0d62b0b6fb3570b0b67b0a6fb1d60b0a67b085d00a47aea6eae928ae92400a43ad83500a3faca6e00a3bab835aa462aa257aa04d00a3700a33a886da4255a7464a7045a424fa6264a4243a4a5fa4a5da40550095fa31360095b9f26da147ca127c9f24f9fb7c9fa7c9f243009579e136009539ba6f9ba6b9ba679ba630094f9a96495b6f9993495b6b9897c95b679793495b6396a559596e959360094b942459404584d6284b6f9224f92243915709127d84b678fd688f86584a6f8e6708e26c84a6b8d57084a678c26c84a638936f893678926e892628904584a5d8826c84a3b86c608684d84a378526f852558485d00947839647db6f829347db6b8197c7db67809347db637fa557d96e7e26a7e2667d936009437c84d7b2357ba3d7b0350093f7a2557916e791360093b00937779360093376a547156b7535475254715637146f73a7c714677257e722547145f7126e0092f6eb6f6eb676f2656e96e0092b6db586256b6bb586ba546b855625636246f6a370624676857e68358680556245f66d6966825623626226f65360622676225f63d72622476215a6203d009276116e009235ca4f5f85c5ca475c94f5da5d5d85c5c9475c9270085f0085b5426d5a47c5a27c5424f59570542475414f57a4f565705627d5625d5414754b7054a7c54127008575284c528440085351a554ac6e50c644aa6f4fd634aa454e4644e2454a96f4b57e4b3724b3584b2544b03c4a9270084f4904c490440084b4824543d6243b6f46d6843a6f4536f4526e43a5d4446043a37008474202c420240084340a4540a350083f0083b3f23536c623e23536b523cc603c86c36a5736a4d36a3d394603926d3924d3906c3695737d7237b50369273685700837008333526426d6f33b5433a5426d6326c6f31a443184426c633057e3025426c5f2ea442e84426c5b26c572cb442ca4426c5326a6e2b2642696f2695f28e7228a6c2886c2695727a442694f269470082f258542245f248442245b224572294422844224530082b213641256f1f3541f2541f054125631246f1d3441d044124631bd7e1bb541245f1ab441245b12457183441824418044124531236e16b641216f1215f14e7214b6c1215713344130441214f1214700827110540cc5f0f9440f8440cc5b0cc570e0440cc530c84c0c844008230b9640936f0aa550916e09a6e091360081f0805407c5f0081b0685401d6301c6f0557e01c5f01b6f0357e0305401b5f0257201b4700817008130003f 9 11
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV4 fullMask g_54 ep_54 437 bds_54 (dagTraceF fullMask rootStock 11 f_54) (cur_54 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_0 : treeBlockF 0 32 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_1 : treeBlockF 32 64 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_2 : treeBlockF 64 96 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_3 : treeBlockF 96 128 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_4 : treeBlockF 128 160 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_5 : treeBlockF 160 192 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_6 : treeBlockF 192 224 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_7 : treeBlockF 224 256 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_8 : treeBlockF 256 288 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_9 : treeBlockF 288 320 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_10 : treeBlockF 320 352 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_11 : treeBlockF 352 384 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_12 : treeBlockF 384 416 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_13 : treeBlockF 416 437 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
theorem nj_54_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_54_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_54_1 h1 h2)
theorem nj_54_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_1 (fun _ h1 h2 => treeBlockF_at nb_54_2 h1 h2)
theorem nj_54_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_2 (fun _ h1 h2 => treeBlockF_at nb_54_3 h1 h2)
theorem nj_54_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_3 (fun _ h1 h2 => treeBlockF_at nb_54_4 h1 h2)
theorem nj_54_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_4 (fun _ h1 h2 => treeBlockF_at nb_54_5 h1 h2)
theorem nj_54_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_5 (fun _ h1 h2 => treeBlockF_at nb_54_6 h1 h2)
theorem nj_54_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_6 (fun _ h1 h2 => treeBlockF_at nb_54_7 h1 h2)
theorem nj_54_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_7 (fun _ h1 h2 => treeBlockF_at nb_54_8 h1 h2)
theorem nj_54_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_8 (fun _ h1 h2 => treeBlockF_at nb_54_9 h1 h2)
theorem nj_54_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_9 (fun _ h1 h2 => treeBlockF_at nb_54_10 h1 h2)
theorem nj_54_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_10 (fun _ h1 h2 => treeBlockF_at nb_54_11 h1 h2)
theorem nj_54_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_11 (fun _ h1 h2 => treeBlockF_at nb_54_12 h1 h2)
theorem nj_54_13 : ∀ i, 0 ≤ i → i < 437 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_12 (fun _ h1 h2 => treeBlockF_at nb_54_13 h1 h2)
theorem nc_54 : ∀ i, 0 ≤ i → i < 437 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 437 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := nj_54_13
theorem lb_54 : LowerBin fullMask rootStock g_54 12 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_54 kn_54 sub_54 gl_54 rc_54 nc_54

def wg : List Gate := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [5, 8]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.or, [6, 10]⟩, ⟨GateOp.and, [4, 12]⟩, ⟨GateOp.or, [4, 12]⟩, ⟨GateOp.and, [1, 14]⟩, ⟨GateOp.or, [7, 15]⟩, ⟨GateOp.and, [11, 16]⟩, ⟨GateOp.or, [13, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 3968378880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676776 * 2 ^ 32 + 3968378880)) (13 - 1) := by
  rw [show canon fullMask (4276676776 * 2 ^ 32 + 3968378880) = g_54 by decide]
  exact lb_54

end PEqualNP.Outside.L_meta_49381

theorem PEqualNP.Outside.L_meta_49381 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 3968378880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 3968378880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_49381.table2_from_lowerBin (4276676776 * 2 ^ 32 + 3968378880) 13 PEqualNP.Outside.L_meta_49381.root_lb PEqualNP.Outside.L_meta_49381.wg 18 rfl PEqualNP.Outside.L_meta_49381.wfits PEqualNP.Outside.L_meta_49381.weval

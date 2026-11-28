import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49197

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

def m_0 : Nat := 0xaaaa
def s_0 : List Nat := [0x2222, 0xa0a, 0xaa]
def g_0 : Nat := 0x22a
def ep_0 : Nat := 0x28000000000000020800000000000002200000000000000000
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

def m_1 : Nat := 0x3030303000000000
def s_1 : List Nat := [0x1010101000000000, 0x30003000000000, 0x303000000000]
def g_1 : Nat := 0x10103000000000
def ep_1 : Nat := 0x1020000000000010002000000000000000000000000000000000000000000010100000000000
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

def m_2 : Nat := 0x5050505000000000
def s_2 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_2 : Nat := 0x10105000000000
def ep_2 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
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

def m_4 : Nat := 0x3300330000000000
def s_4 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_4 : Nat := 0x100130000000000
def ep_4 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
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

def m_6 : Nat := 0x4444444400000000
def s_6 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_6 : Nat := 0x4044400000000
def ep_6 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_7 : Nat := 0x2222222200000000
def s_7 : List Nat := [0x202020200000000, 0x22002200000000, 0x222200000000]
def g_7 : Nat := 0x2022200000000
def ep_7 : Nat := 0x220000000000002002000000000000202000000000000000000000000000000000000000000
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

def m_8 : Nat := 0xcccc0000
def s_8 : List Nat := [0x44440000, 0xc0c0000, 0xcc0000]
def g_8 : Nat := 0x44c0000
def ep_8 : Nat := 0x480000000000000408000000000000000000000000000004400000
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

def m_9 : Nat := 0xf000f000000000
def s_9 : List Nat := [0x50005000000000, 0x30003000000000, 0xf000000000]
def g_9 : Nat := 0x10007000000000
def ep_9 : Nat := 0x60000000000000000000000000000000000000000000100020000000000010004000000000
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

def m_10 : Nat := 0x5000500050005000
def s_10 : List Nat := [0x1000100010001000, 0x500000005000, 0x50005000]
def g_10 : Nat := 0x100010005000
def ep_10 : Nat := 0x1000400000001000000040000000000000000000000000000000000000001000100000000000000000000000
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

def m_11 : Nat := 0x3333000000000000
def s_11 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_11 : Nat := 0x113000000000000
def ep_11 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
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

def m_12 : Nat := 0x5555000000000000
def s_12 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_12 : Nat := 0x115000000000000
def ep_12 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
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

def m_13 : Nat := 0x4040404040404040
def s_13 : List Nat := [0x40004000400040, 0x404000004040, 0x40404040]
def g_13 : Nat := 0x4000404040
def ep_13 : Nat := 0x40400000000040000040000000004000400000000000000000000000000000000000000000000000000000
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

def m_14 : Nat := 0xff000000000000
def s_14 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_14 : Nat := 0x17000000000000
def ep_14 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_15 : Nat := 0xf0f000000000000
def s_15 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_15 : Nat := 0x107000000000000
def ep_15 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_16 : Nat := 0x4400440044004400
def s_16 : List Nat := [0x400040004000400, 0x440000004400, 0x44004400]
def g_16 : Nat := 0x40004004400
def ep_16 : Nat := 0x400400000000400000040000000000000000000000004000400000000000000000000000000000000000000
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

def m_17 : Nat := 0x5500000055000000
def s_17 : List Nat := [0x1100000011000000, 0x500000005000000, 0x55000000]
def g_17 : Nat := 0x100000015000000
def ep_17 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000000000000000000
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

def m_18 : Nat := 0xf0f000000000
def s_18 : List Nat := [0x505000000000, 0x303000000000, 0xf000000000]
def g_18 : Nat := 0x107000000000
def ep_18 : Nat := 0x6000000000000000000000000000001020000000000000104000000000
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

def m_19 : Nat := 0xff0000000000
def s_19 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_19 : Nat := 0x170000000000
def ep_19 : Nat := 0x6000000000000001200000000000000140000000000
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

def m_20 : Nat := 0x4444000044440000
def s_20 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_20 : Nat := 0x4000004440000
def ep_20 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
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

def m_21 : Nat := 0xc0c00000c0c0000
def s_21 : List Nat := [0x404000004040000, 0xc0000000c0000, 0xc0c0000]
def g_21 : Nat := 0x40000040c0000
def ep_21 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000000
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

def m_22 : Nat := 0x5050000050500000
def s_22 : List Nat := [0x1010000010100000, 0x50000000500000, 0x50500000]
def g_22 : Nat := 0x10000010500000
def ep_22 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000000000000000000
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

def m_23 : Nat := 0xcc000000cc0000
def s_23 : List Nat := [0x44000000440000, 0xc0000000c0000, 0xcc0000]
def g_23 : Nat := 0x40000004c0000
def ep_23 : Nat := 0x48000000000000000000000000000000000000000400000008000000000000000000000004000000400000
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

def m_24 : Nat := 0xff00ff0000000000
def s_24 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_24 : Nat := 0x100170000000000
def ep_24 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
theorem epk_24 : ep_24 = edgePack m_24 g_24 := by decide +kernel
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_19, s_19, 4, g_19), (m_3, s_3, 4, g_3), (m_4, s_4, 4, g_4)]
theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_5
  · exact lb_19
  · exact lb_3
  · exact lb_4
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

def m_25 : Nat := 0xffff000000000000
def s_25 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_25 : Nat := 0x117000000000000
def ep_25 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
theorem epk_25 : ep_25 = edgePack m_25 g_25 := by decide +kernel
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15), (m_14, s_14, 4, g_14), (m_12, s_12, 4, g_12), (m_11, s_11, 4, g_11)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_15
  · exact lb_14
  · exact lb_12
  · exact lb_11
theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_25_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_25_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_25 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_25_1 (Nat.sub p 32)) (cc_25_0 p) (Nat.blt p 32)
def f_25 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV4 m_25 g_25 ep_25 43 bds_25 (dagTraceF m_25 s_25 6 f_25) (cur_25 0) s_25 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_0 : treeBlockF 0 32 (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 43 (dagTraceF m_25 s_25 6 f_25) cur_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_1 : treeBlockF 32 43 (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 43 (dagTraceF m_25 s_25 6 f_25) cur_25) = true := by decide +kernel
theorem nj_25_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 43 (dagTraceF m_25 s_25 6 f_25) cur_25) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_25_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_25_1 h1 h2)
theorem nc_25 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 43 (dagTraceF m_25 s_25 6 f_25) cur_25) i = true := nj_25_1
theorem lb_25 : LowerBin m_25 s_25 g_25 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_25 kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0xffff00000000
def s_26 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_26 : Nat := 0x177700000000
def ep_26 : Nat := 0x6000000000000006000000000000001222000000000000144400000000
theorem epk_26 : ep_26 = edgePack m_26 g_26 := by decide +kernel
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]
theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_18
theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV4 m_26 g_26 ep_26 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_26 g_26 ep_26 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_26 kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0xf0f0f0f000000000
def s_27 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_27 : Nat := 0x10107000000000
def ep_27 : Nat := 0x1060000000000010006000000000000000000000000000101020000000000010104000000000
theorem epk_27 : ep_27 = edgePack m_27 g_27 := by decide +kernel
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9), (m_18, s_18, 4, g_18), (m_2, s_2, 4, g_2), (m_1, s_1, 4, g_1)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_9
  · exact lb_18
  · exact lb_2
  · exact lb_1
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_27_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_27_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_27 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_27_1 (Nat.sub p 32)) (cc_27_0 p) (Nat.blt p 32)
def f_27 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV4 m_27 g_27 ep_27 43 bds_27 (dagTraceF m_27 s_27 6 f_27) (cur_27 0) s_27 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_0 : treeBlockF 0 32 (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 43 (dagTraceF m_27 s_27 6 f_27) cur_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_1 : treeBlockF 32 43 (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 43 (dagTraceF m_27 s_27 6 f_27) cur_27) = true := by decide +kernel
theorem nj_27_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 43 (dagTraceF m_27 s_27 6 f_27) cur_27) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_27_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_27_1 h1 h2)
theorem nc_27 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 43 (dagTraceF m_27 s_27 6 f_27) cur_27) i = true := nj_27_1
theorem lb_27 : LowerBin m_27 s_27 g_27 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_27 kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xcccccccc00000000
def s_28 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_28 : Nat := 0x4044400000000
def ep_28 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
theorem epk_28 : ep_28 = edgePack m_28 g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
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
def g_29 : Nat := 0x113133300000000
def ep_29 : Nat := 0x1220000000000012002000000000010202000000000000000000000000000110100000000000
theorem epk_29 : ep_29 = edgePack m_29 g_29 := by decide +kernel
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_11, s_11, 4, g_11), (m_1, s_1, 4, g_1), (m_7, s_7, 4, g_7)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_4
  · exact lb_11
  · exact lb_1
  · exact lb_7
theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_29_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_29_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
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

def m_30 : Nat := 0xaa00aa00aa00aa
def s_30 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_30 : Nat := 0x20022000a002a
def ep_30 : Nat := 0x800080000002000000020000000000000000000020000000a000800020022000000200000000000000000
theorem epk_30 : ep_30 = edgePack m_30 g_30 := by decide +kernel
def bds_30 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_30 : KnownBin bds_30 := by intro b hb; simp [bds_30] at hb
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp [bds_30] at hb
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_30] at hb
def cur_30 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0xf 2 3 1 1 4 15 5 31
def f_30 : Nat → Nat × Nat := unpackForestF 0xf 1 4
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV4 m_30 g_30 ep_30 1 bds_30 (dagTraceF m_30 s_30 3 f_30) (cur_30 0) s_30 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30 : treeBlockF 0 1 (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 1 (dagTraceF m_30 s_30 3 f_30) cur_30) = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 1 (dagTraceF m_30 s_30 3 f_30) cur_30) i = true := fun _ h1 h2 => treeBlockF_at nb_30 h1 h2
theorem lb_30 : LowerBin m_30 s_30 g_30 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_30 kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0x5050505050505050
def s_31 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_31 : Nat := 0x10105010505050
def ep_31 : Nat := 0x1040400000001040000040000010004000400000000000000000000000101000100000000000000000000000
theorem epk_31 : ep_31 = edgePack m_31 g_31 := by decide +kernel
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_22, s_22, 4, g_22), (m_10, s_10, 4, g_10), (m_13, s_13, 4, g_13)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_2
  · exact lb_22
  · exact lb_10
  · exact lb_13
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_31_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_31_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
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

def m_32 : Nat := 0x5555555500000000
def s_32 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_32 : Nat := 0x115155500000000
def ep_32 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
theorem epk_32 : ep_32 = edgePack m_32 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_12, s_12, 4, g_12), (m_2, s_2, 4, g_2), (m_6, s_6, 4, g_6)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_3
  · exact lb_12
  · exact lb_2
  · exact lb_6
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_32_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_32_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_32 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_32_1 (Nat.sub p 32)) (cc_32_0 p) (Nat.blt p 32)
def f_32 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
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

def m_33 : Nat := 0x3030303030303030
def s_33 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_33 : Nat := 0x10103010101030
def ep_33 : Nat := 0x1000000000001020000000200010002000000020000000000000000000000000000000000010100010101000
theorem epk_33 : ep_33 = edgePack m_33 g_33 := by decide +kernel
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV4 m_33 g_33 ep_33 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_33 g_33 ep_33 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_33 kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0xc0c0c0c0c0c0c0c0
def s_34 : List Nat := [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0]
def g_34 : Nat := 0x4000404040
def ep_34 : Nat := 0x40400000000040000040000000004000400000000000000000000000000000000000000000004000404040
theorem epk_34 : ep_34 = edgePack m_34 g_34 := by decide +kernel
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_13
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV4 m_34 g_34 ep_34 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_34 g_34 ep_34 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_34 kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xcccc0000cccc
def s_35 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_35 : Nat := 0x4440000444c
def ep_35 : Nat := 0x400800000000000000000000004000000008000004000000000800000000000000000000044400004440
theorem epk_35 : ep_35 = edgePack m_35 g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_35 : KnownBin bds_35 := by intro b hb; simp [bds_35] at hb
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp [bds_35] at hb
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_35] at hb
def cc_35_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_35_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cur_35 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_35_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_35_0 p) (Nat.blt p 32)
def f_35 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV4 m_35 g_35 ep_35 64 bds_35 (dagTraceF m_35 s_35 5 f_35) (cur_35 0) s_35 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_0 : treeBlockF 0 32 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 64 (dagTraceF m_35 s_35 5 f_35) cur_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_1 : treeBlockF 32 64 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 64 (dagTraceF m_35 s_35 5 f_35) cur_35) = true := by decide +kernel
theorem nj_35_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 64 (dagTraceF m_35 s_35 5 f_35) cur_35) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_35_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_35_1 h1 h2)
theorem nc_35 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 64 (dagTraceF m_35 s_35 5 f_35) cur_35) i = true := nj_35_1
theorem lb_35 : LowerBin m_35 s_35 g_35 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_35 kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0x5555000055550000
def s_36 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_36 : Nat := 0x115000015550000
def ep_36 : Nat := 0x1440000000000000000000000014000000400000010400000400000001100000100000000000000000000000
theorem epk_36 : ep_36 = edgePack m_36 g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12), (m_17, s_17, 4, g_17), (m_22, s_22, 4, g_22), (m_20, s_20, 4, g_20)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_12
  · exact lb_17
  · exact lb_22
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

def m_37 : Nat := 0x5500550055005500
def s_37 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_37 : Nat := 0x100150015005500
def ep_37 : Nat := 0x1400400000001400000040000000000000000000010004000400000001001000100000000000000000000000
theorem epk_37 : ep_37 = edgePack m_37 g_37 := by decide +kernel
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_17, s_17, 4, g_17), (m_10, s_10, 4, g_10), (m_16, s_16, 4, g_16)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_3
  · exact lb_17
  · exact lb_10
  · exact lb_16
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_37_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_37_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
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

def m_38 : Nat := 0xff000000ff00
def s_38 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_38 : Nat := 0x170000005700
def ep_38 : Nat := 0x400000000000000000000000000000000000000006000000020000001200000002000000140000005400
theorem epk_38 : ep_38 = edgePack m_38 g_38 := by decide +kernel
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 4, g_19)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_19
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV4 m_38 g_38 ep_38 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_38 g_38 ep_38 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_38 kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xf0f00000f0f0
def s_39 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_39 : Nat := 0x107000005070
def ep_39 : Nat := 0x400000000000000000000000006000000020000000000000000000001020000000200000104000005040
theorem epk_39 : ep_39 = edgePack m_39 g_39 := by decide +kernel
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_18
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV4 m_39 g_39 ep_39 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_39 g_39 ep_39 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_39 kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0xcccc0000cccc0000
def s_40 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_40 : Nat := 0x40000044c0000
def ep_40 : Nat := 0x448000000000000000000000004000000480000000400000408000000000000000000000004000004400000
theorem epk_40 : ep_40 = edgePack m_40 g_40 := by decide +kernel
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 4, g_23), (m_8, s_8, 4, g_8), (m_20, s_20, 4, g_20), (m_21, s_21, 4, g_21)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_23
  · exact lb_8
  · exact lb_20
  · exact lb_21
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_40_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_40_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_40 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_40_1 (Nat.sub p 32)) (cc_40_0 p) (Nat.blt p 32)
def f_40 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
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

def m_41 : Nat := 0xaaaa0000aaaa
def s_41 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_41 : Nat := 0x2220000022a
def ep_41 : Nat := 0x800000000000000000000002000000028000002000000020800000222000002200000000000000000
theorem epk_41 : ep_41 = edgePack m_41 g_41 := by decide +kernel
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV4 m_41 g_41 ep_41 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_41 g_41 ep_41 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_41 kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0x3300330033003300
def s_42 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_42 : Nat := 0x100130011001300
def ep_42 : Nat := 0x1000000000001200000002000000000000000000010002000000020000000000000000000100100011001000
theorem epk_42 : ep_42 = edgePack m_42 g_42 := by decide +kernel
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV4 m_42 g_42 ep_42 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_42 g_42 ep_42 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_42 kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xcc00cc00cc00cc00
def s_43 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_43 : Nat := 0x40004004400
def ep_43 : Nat := 0x400400000000400000040000000000000000000000004000400000000000000000000000000040004004400
theorem epk_43 : ep_43 = edgePack m_43 g_43 := by decide +kernel
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_16
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV4 m_43 g_43 ep_43 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_43 g_43 ep_43 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_43 kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xf000f000f000f000
def s_44 : List Nat := [0x5000500050005000, 0x3000300030003000, 0xf0000000f000, 0xf000f000]
def g_44 : Nat := 0x100010005000
def ep_44 : Nat := 0x1000400000001000000040000000000000000000000000000000000000001000100000000000100010005000
theorem epk_44 : ep_44 = edgePack m_44 g_44 := by decide +kernel
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV4 m_44 g_44 ep_44 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_44 g_44 ep_44 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_44 kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0xf000f000f000f00
def s_45 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_45 : Nat := 0x100070005000700
def ep_45 : Nat := 0x400000000000600000002000000000000000000000000000000000001000200000002000100040005000400
theorem epk_45 : ep_45 = edgePack m_45 g_45 := by decide +kernel
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV4 m_45 g_45 ep_45 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_45 g_45 ep_45 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_45 kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0xcc00cc00cc00cc
def s_46 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_46 : Nat := 0x40044004c004c
def ep_46 : Nat := 0x48000800000040000000000000000000000000000400000008000800000000000000000004004400400040
theorem epk_46 : ep_46 = edgePack m_46 g_46 := by decide +kernel
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 4, g_23)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_23
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV4 m_46 g_46 ep_46 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_46 g_46 ep_46 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_46 kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xffff
def s_47 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_47 : Nat := 0x577f
def ep_47 : Nat := 0x28000000000000020800000000000002200000000000005440
theorem epk_47 : ep_47 = edgePack m_47 g_47 := by decide +kernel
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV4 m_47 g_47 ep_47 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_47 g_47 ep_47 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_47 kn_47 sub_47 gl_47 rc_47 nc_47

def m_48 : Nat := 0xff00ff00
def s_48 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_48 : Nat := 0x15005700
def ep_48 : Nat := 0x42000000000000000000000000000400020000000000100002000000000015005400
theorem epk_48 : ep_48 = edgePack m_48 g_48 := by decide +kernel
def bds_48 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_48 : KnownBin bds_48 := by intro b hb; simp [bds_48] at hb
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp [bds_48] at hb
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_48] at hb
def cc_48_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_48_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cur_48 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_48_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_48_0 p) (Nat.blt p 32)
def f_48 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV4 m_48 g_48 ep_48 64 bds_48 (dagTraceF m_48 s_48 5 f_48) (cur_48 0) s_48 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_0 : treeBlockF 0 32 (dagCheckNodeV4 m_48 g_48 ep_48 bds_48 64 (dagTraceF m_48 s_48 5 f_48) cur_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_1 : treeBlockF 32 64 (dagCheckNodeV4 m_48 g_48 ep_48 bds_48 64 (dagTraceF m_48 s_48 5 f_48) cur_48) = true := by decide +kernel
theorem nj_48_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_48 g_48 ep_48 bds_48 64 (dagTraceF m_48 s_48 5 f_48) cur_48) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_48_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_48_1 h1 h2)
theorem nc_48 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_48 g_48 ep_48 bds_48 64 (dagTraceF m_48 s_48 5 f_48) cur_48) i = true := nj_48_1
theorem lb_48 : LowerBin m_48 s_48 g_48 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_48 kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0xf0f0f0f0
def s_49 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_49 : Nat := 0x10505070
def ep_49 : Nat := 0x40200000000000400020000000000000000000000000100000200000000010505040
theorem epk_49 : ep_49 = edgePack m_49 g_49 := by decide +kernel
def bds_49 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_49 : KnownBin bds_49 := by intro b hb; simp [bds_49] at hb
theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by intro b hb; simp [bds_49] at hb
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_49] at hb
def cc_49_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_49_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cur_49 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_49_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_49_0 p) (Nat.blt p 32)
def f_49 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV4 m_49 g_49 ep_49 64 bds_49 (dagTraceF m_49 s_49 5 f_49) (cur_49 0) s_49 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_0 : treeBlockF 0 32 (dagCheckNodeV4 m_49 g_49 ep_49 bds_49 64 (dagTraceF m_49 s_49 5 f_49) cur_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_1 : treeBlockF 32 64 (dagCheckNodeV4 m_49 g_49 ep_49 bds_49 64 (dagTraceF m_49 s_49 5 f_49) cur_49) = true := by decide +kernel
theorem nj_49_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_49 g_49 ep_49 bds_49 64 (dagTraceF m_49 s_49 5 f_49) cur_49) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_49_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_49_1 h1 h2)
theorem nc_49 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_49 g_49 ep_49 bds_49 64 (dagTraceF m_49 s_49 5 f_49) cur_49) i = true := nj_49_1
theorem lb_49 : LowerBin m_49 s_49 g_49 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_49 kn_49 sub_49 gl_49 rc_49 nc_49

def m_50 : Nat := 0xcccccccc
def s_50 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_50 : Nat := 0x44c444c
def ep_50 : Nat := 0x40000000000000480008000000000408000800000000000000000000000004404440
theorem epk_50 : ep_50 = edgePack m_50 g_50 := by decide +kernel
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV4 m_50 g_50 ep_50 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_50 g_50 ep_50 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_50 kn_50 sub_50 gl_50 rc_50 nc_50

def m_51 : Nat := 0xaaaaaaaa
def s_51 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_51 : Nat := 0xa022a
def ep_51 : Nat := 0x22000000000000a002800000000000a020800000000000002200000000000000000
theorem epk_51 : ep_51 = edgePack m_51 g_51 := by decide +kernel
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_51 : KnownBin bds_51 := by
  intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_51 : ∀ b ∈ bds_51, m_51 &&& b.1 = b.1 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_51 : ∀ b ∈ bds_51, canon b.1 g_51 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV4 m_51 g_51 ep_51 0 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) s_51 4 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_51 g_51 ep_51 bds_51 0 (dagTraceF m_51 s_51 4 f_51) cur_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_51 kn_51 sub_51 gl_51 rc_51 nc_51

def m_52 : Nat := 0xff000000ff000000
def s_52 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_52 : Nat := 0x100000015000000
def ep_52 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000100000015000000
theorem epk_52 : ep_52 = edgePack m_52 g_52 := by decide +kernel
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
theorem kn_52 : KnownBin bds_52 := by
  intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_17
theorem sub_52 : ∀ b ∈ bds_52, m_52 &&& b.1 = b.1 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_52 : ∀ b ∈ bds_52, canon b.1 g_52 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV4 m_52 g_52 ep_52 0 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) s_52 4 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_52 g_52 ep_52 bds_52 0 (dagTraceF m_52 s_52 4 f_52) cur_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_52 kn_52 sub_52 gl_52 rc_52 nc_52

def m_53 : Nat := 0xff000000ff0000
def s_53 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_53 : Nat := 0x170000005f0000
def ep_53 : Nat := 0x4800000000000000000000000000000000000000060000000a000000120000000000000014000000500000
theorem epk_53 : ep_53 = edgePack m_53 g_53 := by decide +kernel
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
theorem kn_53 : KnownBin bds_53 := by
  intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_14
theorem sub_53 : ∀ b ∈ bds_53, m_53 &&& b.1 = b.1 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_53 : ∀ b ∈ bds_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV4 m_53 g_53 ep_53 0 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) s_53 4 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_53 g_53 ep_53 bds_53 0 (dagTraceF m_53 s_53 4 f_53) cur_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_53 kn_53 sub_53 gl_53 rc_53 nc_53

def m_54 : Nat := 0xf000f000f000f0
def s_54 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_54 : Nat := 0x10007000500070
def ep_54 : Nat := 0x40000000000060000000200000000000000000000000000000000000100020000000200010004000500040
theorem epk_54 : ep_54 = edgePack m_54 g_54 := by decide +kernel
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_54 : KnownBin bds_54 := by
  intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_54 : ∀ b ∈ bds_54, m_54 &&& b.1 = b.1 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_54 : ∀ b ∈ bds_54, canon b.1 g_54 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV4 m_54 g_54 ep_54 0 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) s_54 4 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_54 g_54 ep_54 bds_54 0 (dagTraceF m_54 s_54 4 f_54) cur_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_54 kn_54 sub_54 gl_54 rc_54 nc_54

def m_55 : Nat := 0xf0f00000f0f00000
def s_55 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_55 : Nat := 0x10000010500000
def ep_55 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000010000010500000
theorem epk_55 : ep_55 = edgePack m_55 g_55 := by decide +kernel
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 4, g_22)]
theorem kn_55 : KnownBin bds_55 := by
  intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_22
theorem sub_55 : ∀ b ∈ bds_55, m_55 &&& b.1 = b.1 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_55 : ∀ b ∈ bds_55, canon b.1 g_55 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_55 : Nat → List (Nat × Nat) := fun _ => []
def f_55 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV4 m_55 g_55 ep_55 0 bds_55 (dagTraceF m_55 s_55 4 f_55) (cur_55 0) s_55 4 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_55 g_55 ep_55 bds_55 0 (dagTraceF m_55 s_55 4 f_55) cur_55 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_55 : LowerBin m_55 s_55 g_55 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_55 kn_55 sub_55 gl_55 rc_55 nc_55

def m_56 : Nat := 0x4444444444444444
def s_56 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_56 : Nat := 0x4044404444444
def ep_56 : Nat := 0x440400000000440000040000004004000400000000404000400000000000000000000000000000000000000
theorem epk_56 : ep_56 = edgePack m_56 g_56 := by decide +kernel
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_20, s_20, 4, g_20), (m_16, s_16, 4, g_16), (m_13, s_13, 4, g_13)]
theorem kn_56 : KnownBin bds_56 := by
  intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_6
  · exact lb_20
  · exact lb_16
  · exact lb_13
theorem sub_56 : ∀ b ∈ bds_56, m_56 &&& b.1 = b.1 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_56 : ∀ b ∈ bds_56, canon b.1 g_56 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_56_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_56_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_56 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_56_1 (Nat.sub p 32)) (cc_56_0 p) (Nat.blt p 32)
def f_56 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV4 m_56 g_56 ep_56 43 bds_56 (dagTraceF m_56 s_56 6 f_56) (cur_56 0) s_56 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_0 : treeBlockF 0 32 (dagCheckNodeV4 m_56 g_56 ep_56 bds_56 43 (dagTraceF m_56 s_56 6 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_1 : treeBlockF 32 43 (dagCheckNodeV4 m_56 g_56 ep_56 bds_56 43 (dagTraceF m_56 s_56 6 f_56) cur_56) = true := by decide +kernel
theorem nj_56_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_56 g_56 ep_56 bds_56 43 (dagTraceF m_56 s_56 6 f_56) cur_56) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_56_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_56_1 h1 h2)
theorem nc_56 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_56 g_56 ep_56 bds_56 43 (dagTraceF m_56 s_56 6 f_56) cur_56) i = true := nj_56_1
theorem lb_56 : LowerBin m_56 s_56 g_56 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_56 kn_56 sub_56 gl_56 rc_56 nc_56

def m_57 : Nat := 0xa0a0a0a0a0a0a0a
def s_57 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_57 : Nat := 0x20202000a020a
def ep_57 : Nat := 0x80008000002000000020000020000000a0008000000000000000000020202000002000000000000000000
theorem epk_57 : ep_57 = edgePack m_57 g_57 := by decide +kernel
def bds_57 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_57 : KnownBin bds_57 := by intro b hb; simp [bds_57] at hb
theorem sub_57 : ∀ b ∈ bds_57, m_57 &&& b.1 = b.1 := by intro b hb; simp [bds_57] at hb
theorem gl_57 : ∀ b ∈ bds_57, canon b.1 g_57 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_57] at hb
def cur_57 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0xf 2 3 1 1 4 15 5 31
def f_57 : Nat → Nat × Nat := unpackForestF 0xf 1 4
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV4 m_57 g_57 ep_57 1 bds_57 (dagTraceF m_57 s_57 3 f_57) (cur_57 0) s_57 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57 : treeBlockF 0 1 (dagCheckNodeV4 m_57 g_57 ep_57 bds_57 1 (dagTraceF m_57 s_57 3 f_57) cur_57) = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_57 g_57 ep_57 bds_57 1 (dagTraceF m_57 s_57 3 f_57) cur_57) i = true := fun _ h1 h2 => treeBlockF_at nb_57 h1 h2
theorem lb_57 : LowerBin m_57 s_57 g_57 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_57 kn_57 sub_57 gl_57 rc_57 nc_57

def m_58 : Nat := 0x5a5a00005a5a
def s_58 : List Nat := [0xa0a00000a0a, 0x121200001212, 0x5a0000005a, 0x5a5a]
def g_58 : Nat := 0x12520000525a
def ep_58 : Nat := 0x400800000000000000000000004000000008000000000000000000001202000002000000000000000000
theorem epk_58 : ep_58 = edgePack m_58 g_58 := by decide +kernel
def bds_58 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_58 : KnownBin bds_58 := by intro b hb; simp [bds_58] at hb
theorem sub_58 : ∀ b ∈ bds_58, m_58 &&& b.1 = b.1 := by intro b hb; simp [bds_58] at hb
theorem gl_58 : ∀ b ∈ bds_58, canon b.1 g_58 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_58] at hb
def cur_58 : Nat → List (Nat × Nat) := unpackCursorV4 0x16ac58b12a44890e8701 0x31343068c4a08121928204928ea11b393a526c80e841b000f 7 127 3 7 10 1023 15 32767
def f_58 : Nat → Nat × Nat := unpackForestF 0xc7463629d64a0a6c43a494209086c00f 3 10
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV4 m_58 g_58 ep_58 10 bds_58 (dagTraceF m_58 s_58 4 f_58) (cur_58 0) s_58 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58 : treeBlockF 0 10 (dagCheckNodeV4 m_58 g_58 ep_58 bds_58 10 (dagTraceF m_58 s_58 4 f_58) cur_58) = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_58 g_58 ep_58 bds_58 10 (dagTraceF m_58 s_58 4 f_58) cur_58) i = true := fun _ h1 h2 => treeBlockF_at nb_58 h1 h2
theorem lb_58 : LowerBin m_58 s_58 g_58 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_58 kn_58 sub_58 gl_58 rc_58 nc_58

def m_59 : Nat := 0xc0c0c0c0c0c0c0c
def s_59 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_59 : Nat := 0x40404040c040c
def ep_59 : Nat := 0x408000800000400000000000004000000080008000000000000000000000000000000000004040404000400
theorem epk_59 : ep_59 = edgePack m_59 g_59 := by decide +kernel
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 4, g_21)]
theorem kn_59 : KnownBin bds_59 := by
  intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_21
theorem sub_59 : ∀ b ∈ bds_59, m_59 &&& b.1 = b.1 := by intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_59 : ∀ b ∈ bds_59, canon b.1 g_59 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_59 : Nat → List (Nat × Nat) := fun _ => []
def f_59 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV4 m_59 g_59 ep_59 0 bds_59 (dagTraceF m_59 s_59 4 f_59) (cur_59 0) s_59 4 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_59 g_59 ep_59 bds_59 0 (dagTraceF m_59 s_59 4 f_59) cur_59 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_59 : LowerBin m_59 s_59 g_59 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_59 kn_59 sub_59 gl_59 rc_59 nc_59

def m_60 : Nat := 0x5555555555555555
def s_60 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_60 : Nat := 0x115155515555555
def ep_60 : Nat := 0x1440400000001440000040000014004000400000010404000400000001101000100000000000000000000000
theorem epk_60 : ep_60 = edgePack m_60 g_60 := by decide +kernel
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 7, g_32), (m_36, s_36, 7, g_36), (m_31, s_31, 7, g_31), (m_37, s_37, 7, g_37)]
theorem kn_60 : KnownBin bds_60 := by
  intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_32
  · exact lb_36
  · exact lb_31
  · exact lb_37
theorem sub_60 : ∀ b ∈ bds_60, m_60 &&& b.1 = b.1 := by intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_60 : ∀ b ∈ bds_60, canon b.1 g_60 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cur_60 : Nat → List (Nat × Nat) := unpackCursorV4 0xe001 0x174fba5dd1ee87e4ff25f91fc8763fb1dd8dec66d4f6a5b51da86d3f69db4dda66d2f695b49da4601f 10 1023 5 31 10 1023 13 8191
def f_60 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV4 m_60 g_60 ep_60 1 bds_60 (dagTraceF m_60 s_60 8 f_60) (cur_60 0) s_60 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60 : treeBlockF 0 1 (dagCheckNodeV4 m_60 g_60 ep_60 bds_60 1 (dagTraceF m_60 s_60 8 f_60) cur_60) = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_60 g_60 ep_60 bds_60 1 (dagTraceF m_60 s_60 8 f_60) cur_60) i = true := fun _ h1 h2 => treeBlockF_at nb_60 h1 h2
theorem lb_60 : LowerBin m_60 s_60 g_60 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_60 kn_60 sub_60 gl_60 rc_60 nc_60

def m_61 : Nat := 0xff00ff00ff00ff00
def s_61 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_61 : Nat := 0x100170015005700
def ep_61 : Nat := 0x1400400000001600000042000000000000000000010006000400020001001200100002000100140015005400
theorem epk_61 : ep_61 = edgePack m_61 g_61 := by decide +kernel
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_24, s_24, 7, g_24), (m_37, s_37, 7, g_37), (m_52, s_52, 5, g_52), (m_44, s_44, 5, g_44), (m_42, s_42, 5, g_42), (m_43, s_43, 5, g_43), (m_45, s_45, 5, g_45), (m_38, s_38, 5, g_38), (m_48, s_48, 6, g_48)]
theorem kn_61 : KnownBin bds_61 := by
  intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_24
  · exact lb_37
  · exact lb_52
  · exact lb_44
  · exact lb_42
  · exact lb_43
  · exact lb_45
  · exact lb_38
  · exact lb_48
theorem sub_61 : ∀ b ∈ bds_61, m_61 &&& b.1 = b.1 := by intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_61 : ∀ b ∈ bds_61, canon b.1 g_61 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_61 : Nat → List (Nat × Nat) := unpackCursorV4 0xacf49ff493338c5b7e39713464345773509b4279357428741bb314db06b900590001 0x1c5f1c5b1c571c531b5f1b5e1b5b1b5a1b571b561b531b523b4f3b4e3b4d1a5f1a5e1a5b1a571a531a523a4b4a4a3a494a474a463a433a414a374a364a35195f195b19571953594f494b49475943593f593d593b29395937793559332931392f692b69273923185e1c5f1c5e1c5b1c571c531c521b5f1b5b1b571b533b4f4b4e3b4d3b473b453b433b421a5f1a5e1a5b1a5a1a571a561a531a523a474a463a453a3f3a3e3a3d195f195b19571953494f494b49474943393f393b39373933392f392d392b29293927792539232921185e1c5f1c5e1c5b1c5a1c571c561c531c521b5f1b5b1b571b533b4f3b4e3b4d1a5f1a5b1a571a534a4f4a4e5a4d4a3f4a3e3a3b3a393a334a323a31c230195f195b19571953494f794d494b29494947494549432941493f493b49374933392f692b69273923185e1b4f1b4e1b4b1b471b431b421a4f1a4b1a471a433a3f4a3e3a3d194f194b19471943493f493b49374933392f392b39273923184e38261c5f1c5e1c5b1c571c531c521b5f1b5e1b5b1b571b531b523b4f3b4d3b4b3b4a3b474b463b45c3441a5f1a5e1a5b1a5a1a571a561a531a523a4f5a4e3a4d3a3f3a3e3a3d195f195b19571953594f494b49475943393f393b39373933392f392d392b29293927792539232921185e382688241c5f1c5b1c571c531b5f1b5e1b5b1b5a1b571b561b531b522b4f2b4e2b4d1a5f1a5b1a571a535a4f4a4b4a475a435a3f5a3d5a3b3a395a376a355a333a31195f195e195b195719531952294b494a29494947494629432941493749364935792f292b79272923185e1c5f1c5e1c5b1c571c531c521b5f1b5b1b571b534b4f4b4b4b474b431a5f1a5b1a571a532a4f4a4e2a4d2a472a452a432a422a3f2a3b2a372a33195f195e195b195a1957195619531952294749462945293f393e293b293a2937693629332932292f292e292d185e1c5f1c5e1c5b1c5a1c571c561c531c521b5f1b5b1b571b532b4f2b4e2b4d1a5f1a5b1a571a534a4f6a4d4a4b3a494a474a454a433a414a3f4a3b4a374a33195f195b19571953494f494e594d493f493e293b29392933493229317130792f292b79272923185e1b4f1b4e1b4b1b471b431b421a4f1a4b1a471a434a3f4a3b4a374a33194f194b19471943293f493e293d292f292b29272923184e28161c5f1c5e1c5b1c571c531c521b5f1b5b1b571b535b4f4b4b4b475b431a5f1a5e1a5b1a571a531a522a4f2a4d2a4b2a4a2a474a462a4572442a3f2a3b2a372a33195f195e195b195a1957195619531952294f594e294d293f393e293b293a2937693629332932292f292e292d185e281688141c5f1c5b1c571c531b5f1b5b1b571b533b4f3b4b3b473b431a5f1a5e1a5b1a5a1a571a561a531a523a4f5a4e3a4b3a4a3a474a463a433a422a3f2a3e2a3d195f195e195b195719531952794f294b79472943293b393a29393937393629332931392739266925185e1c5f1c5b1c571c531b5f1b5e1b5b1b571b531b526b4f3b4b6b473b431a5f1a5b1a571a532a4f2a4b2a472a432a3f3a3e2a3d2a372a352a332a32195f195e195b195a1957195619531952294f594e294b294a2947494629432942293769362935292f292e292d185e1c5f1c5b1c571c531b5f1b5e1b5b1b5a1b571b561b531b526b4f5b4e6b4b4b4a6b474b466b435b421a5f1a5b1a571a536a4f3a4b6a473a432a3f2a3e2a3d195f195b19571953794f294b79472943393f393e393d392f392e292b29292923392229212120185e1b4f1b4b1b471b431a4f1a4e1a4b1a471a431a426a3f6a3b6a376a33194f194b19471943293f293b29372933292f692e292d184e28161c5f1c5b1c571c531b5f1b5e1b5b1b571b531b523b4f3b4b3b473b431a5f1a5e1a5b1a571a531a522a4f2a4b2a472a432a3f2a3d2a3b2a3a2a373a362a352234195f195e195b195a1957195619531952294f594e294b294a2947494629432942293f393e293d292f292e292d185e281688141b4f1b4b1b471b431a4f1a4b1a471a43f23fe23bd237b233194f194b19471943a13f913b81376133512f412b31271123184e001f 16 65535 6 63 11 2047 16 65535
def f_61 : Nat → Nat × Nat := unpackForestF 0x18fc63b18df34418cc53f14ec537791053314bc52b149ca34148c01f 4 10
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV4 m_61 g_61 ep_61 16 bds_61 (dagTraceF m_61 s_61 8 f_61) (cur_61 0) s_61 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61 : treeBlockF 0 16 (dagCheckNodeV4 m_61 g_61 ep_61 bds_61 16 (dagTraceF m_61 s_61 8 f_61) cur_61) = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 16 → (dagCheckNodeV4 m_61 g_61 ep_61 bds_61 16 (dagTraceF m_61 s_61 8 f_61) cur_61) i = true := fun _ h1 h2 => treeBlockF_at nb_61 h1 h2
theorem lb_61 : LowerBin m_61 s_61 g_61 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_61 kn_61 sub_61 gl_61 rc_61 nc_61

def m_62 : Nat := 0xf0f0f0f0f0f0f0f0
def s_62 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_62 : Nat := 0x10107010505070
def ep_62 : Nat := 0x1040400000001060000040200010006000400020000000000000000000101020100000200010104010505040
theorem epk_62 : ep_62 = edgePack m_62 g_62 := by decide +kernel
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_27, s_27, 7, g_27), (m_31, s_31, 7, g_31), (m_55, s_55, 5, g_55), (m_44, s_44, 5, g_44), (m_33, s_33, 5, g_33), (m_34, s_34, 5, g_34), (m_54, s_54, 5, g_54), (m_39, s_39, 5, g_39), (m_49, s_49, 6, g_49)]
theorem kn_62 : KnownBin bds_62 := by
  intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_27
  · exact lb_31
  · exact lb_55
  · exact lb_44
  · exact lb_33
  · exact lb_34
  · exact lb_54
  · exact lb_39
  · exact lb_49
theorem sub_62 : ∀ b ∈ bds_62, m_62 &&& b.1 = b.1 := by intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_62 : ∀ b ∈ bds_62, canon b.1 g_62 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_62 : Nat → List (Nat × Nat) := unpackCursorV4 0xacf49ff493338c5b7e39713464345773509b4279357428741bb314db06b900590001 0x1c5f1c5b1c571c531b5f1b5e1b5b1b5a1b571b561b531b523b4f3b4e3b4d1a5f1a5e1a5b1a571a531a523a4b4a4a3a494a474a463a433a414a374a364a35195f195b19571953594f494b49475943593f593d593b29395937793559332931392f692b69273923185e1c5f1c5e1c5b1c571c531c521b5f1b5b1b571b533b4f4b4e3b4d3b473b453b433b421a5f1a5e1a5b1a5a1a571a561a531a523a474a463a453a3f3a3e3a3d195f195b19571953494f494b49474943393f393b39373933392f392d392b29293927792539232921185e1c5f1c5e1c5b1c5a1c571c561c531c521b5f1b5b1b571b533b4f3b4e3b4d1a5f1a5b1a571a534a4f4a4e5a4d4a3f4a3e3a3b3a393a334a323a31c230195f195b19571953494f794d494b29494947494549432941493f493b49374933392f692b69273923185e1b4f1b4e1b4b1b471b431b421a4f1a4b1a471a433a3f4a3e3a3d194f194b19471943493f493b49374933392f392b39273923184e38261c5f1c5e1c5b1c571c531c521b5f1b5e1b5b1b571b531b523b4f3b4d3b4b3b4a3b474b463b45c3441a5f1a5e1a5b1a5a1a571a561a531a523a4f5a4e3a4d3a3f3a3e3a3d195f195b19571953594f494b49475943393f393b39373933392f392d392b29293927792539232921185e382688241c5f1c5b1c571c531b5f1b5e1b5b1b5a1b571b561b531b522b4f2b4e2b4d1a5f1a5b1a571a535a4f4a4b4a475a435a3f5a3d5a3b3a395a376a355a333a31195f195e195b195719531952294b494a29494947494629432941493749364935792f292b79272923185e1c5f1c5e1c5b1c571c531c521b5f1b5b1b571b534b4f4b4b4b474b431a5f1a5b1a571a532a4f4a4e2a4d2a472a452a432a422a3f2a3b2a372a33195f195e195b195a1957195619531952294749462945293f393e293b293a2937693629332932292f292e292d185e1c5f1c5e1c5b1c5a1c571c561c531c521b5f1b5b1b571b532b4f2b4e2b4d1a5f1a5b1a571a534a4f6a4d4a4b3a494a474a454a433a414a3f4a3b4a374a33195f195b19571953494f494e594d493f493e293b29392933493229317130792f292b79272923185e1b4f1b4e1b4b1b471b431b421a4f1a4b1a471a434a3f4a3b4a374a33194f194b19471943293f493e293d292f292b29272923184e28161c5f1c5e1c5b1c571c531c521b5f1b5b1b571b535b4f4b4b4b475b431a5f1a5e1a5b1a571a531a522a4f2a4d2a4b2a4a2a474a462a4572442a3f2a3b2a372a33195f195e195b195a1957195619531952294f594e294d293f393e293b293a2937693629332932292f292e292d185e281688141c5f1c5b1c571c531b5f1b5b1b571b533b4f3b4b3b473b431a5f1a5e1a5b1a5a1a571a561a531a523a4f5a4e3a4b3a4a3a474a463a433a422a3f2a3e2a3d195f195e195b195719531952794f294b79472943293b393a29393937393629332931392739266925185e1c5f1c5b1c571c531b5f1b5e1b5b1b571b531b526b4f3b4b6b473b431a5f1a5b1a571a532a4f2a4b2a472a432a3f3a3e2a3d2a372a352a332a32195f195e195b195a1957195619531952294f594e294b294a2947494629432942293769362935292f292e292d185e1c5f1c5b1c571c531b5f1b5e1b5b1b5a1b571b561b531b526b4f5b4e6b4b4b4a6b474b466b435b421a5f1a5b1a571a536a4f3a4b6a473a432a3f2a3e2a3d195f195b19571953794f294b79472943393f393e393d392f392e292b29292923392229212120185e1b4f1b4b1b471b431a4f1a4e1a4b1a471a431a426a3f6a3b6a376a33194f194b19471943293f293b29372933292f692e292d184e28161c5f1c5b1c571c531b5f1b5e1b5b1b571b531b523b4f3b4b3b473b431a5f1a5e1a5b1a571a531a522a4f2a4b2a472a432a3f2a3d2a3b2a3a2a373a362a352234195f195e195b195a1957195619531952294f594e294b294a2947494629432942293f393e293d292f292e292d185e281688141b4f1b4b1b471b431a4f1a4b1a471a43f23fe23bd237b233194f194b19471943a13f913b81376133512f412b31271123184e001f 16 65535 6 63 11 2047 16 65535
def f_62 : Nat → Nat × Nat := unpackForestF 0x18fc63b18df34418cc53f14ec537791053314bc52b149ca34148c01f 4 10
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV4 m_62 g_62 ep_62 16 bds_62 (dagTraceF m_62 s_62 8 f_62) (cur_62 0) s_62 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62 : treeBlockF 0 16 (dagCheckNodeV4 m_62 g_62 ep_62 bds_62 16 (dagTraceF m_62 s_62 8 f_62) cur_62) = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 16 → (dagCheckNodeV4 m_62 g_62 ep_62 bds_62 16 (dagTraceF m_62 s_62 8 f_62) cur_62) i = true := fun _ h1 h2 => treeBlockF_at nb_62 h1 h2
theorem lb_62 : LowerBin m_62 s_62 g_62 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_62 kn_62 sub_62 gl_62 rc_62 nc_62

def m_63 : Nat := 0x3333333333333333
def s_63 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_63 : Nat := 0x113133311131333
def ep_63 : Nat := 0x1000000000001220000002200012002000020020010202000002020000000000000000000110100011101000
theorem epk_63 : ep_63 = edgePack m_63 g_63 := by decide +kernel
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_29, s_29, 7, g_29)]
theorem kn_63 : KnownBin bds_63 := by
  intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_29
theorem sub_63 : ∀ b ∈ bds_63, m_63 &&& b.1 = b.1 := by intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_63 : ∀ b ∈ bds_63, canon b.1 g_63 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_63 : Nat → List (Nat × Nat) := fun _ => []
def f_63 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV4 m_63 g_63 ep_63 0 bds_63 (dagTraceF m_63 s_63 7 f_63) (cur_63 0) s_63 7 = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_63 g_63 ep_63 bds_63 0 (dagTraceF m_63 s_63 7 f_63) cur_63 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_63 : LowerBin m_63 s_63 g_63 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_63 kn_63 sub_63 gl_63 rc_63 nc_63

def m_64 : Nat := 0xcccccccccccccccc
def s_64 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_64 : Nat := 0x40444044c444c
def ep_64 : Nat := 0x448400800000440000040000004004000480008000404000408000800000000000000000004044404404440
theorem epk_64 : ep_64 = edgePack m_64 g_64 := by decide +kernel
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_40, s_40, 7, g_40), (m_6, s_6, 4, g_6), (m_46, s_46, 5, g_46), (m_59, s_59, 5, g_59), (m_56, s_56, 7, g_56), (m_43, s_43, 5, g_43), (m_34, s_34, 5, g_34), (m_50, s_50, 5, g_50), (m_35, s_35, 6, g_35)]
theorem kn_64 : KnownBin bds_64 := by
  intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_40
  · exact lb_6
  · exact lb_46
  · exact lb_59
  · exact lb_56
  · exact lb_43
  · exact lb_34
  · exact lb_50
  · exact lb_35
theorem sub_64 : ∀ b ∈ bds_64, m_64 &&& b.1 = b.1 := by intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_64 : ∀ b ∈ bds_64, canon b.1 g_64 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_64 : Nat → List (Nat × Nat) := unpackCursorV4 0xacf49ff493338c5b7e39713464345773509b4279357428741bb314db06b900590001 0x3c5f4c5b3c574c532b5f4b5e2b5b1b5a2b571b562b532b522b4f5b4e2b4d2a5f2a5e2a5b2a572a534a522a4b3a4a2a492a472a462a432a412a372a362a35495e485f485b48574853684f384b38476843283f283d283b18392837783528331831282f282b282728233c5f3c5e3c5b3c573c534c522b5f4b5b2b574b532b4f3b4e2b4d2b472b453b433b423a5f4a5e3a5b1a5a3a571a563a533a522a472a462a453a3f5a3e3a3d495e485f485b48574853384f384b38473843583f283b28375833382f382d382b182938277825382318212c5f2c5e2c5b1c5a2c571c562c534c523b5f3b5b3b573b532b4f2b4e3b4d2a5f2a5b2a572a532a4f2a4e2a4d2a3f2a3e2a3b2a392a333a322a31c230495e485f485b48574853284f784d284b18492847284528431841383f383b38373833282f282b282728232b4f2b4e2b4b2b472b434b424a4f4a4b4a474a432a3f2a3e5a3d494e5926484f484b48474843283f283b28372833582f582b582758233c5f4c5e4c5b3c574c534c522b5f4b5e4b5b2b574b534b522b4f2b4d3b4b3b4a2b473b462b45c3444a5f4a5e4a5b1a5a4a571a564a534a522a4f2a4e2a4d3a3f3a3e3a3d495e59268924485f485b48574853684f384b38476843583f283b28375833582f582d582b182958277825582318213c5f1c5b1c574c534b5f4b5e1b5b1b5a1b571b564b534b521b4f1b4e1b4d4a5f1a5b1a574a536a4f3a4b3a476a436a3f2a3d6a3b5a396a372a356a335a31495e185f485e185b185718534852184b384a18493847384618431841383738363835782f182b782718231c5f1c5e1c5b1c571c531c521b5f1b5b1b571b533b4f3b4b3b473b431a5e195f195b19571953194f394e194d1947194519431942193f193b19371933185f185e185b185a1857185618531852184738461845183f583e183b183a1837283618331832181f181e181d3c5f3c5e1c5b1c5a1c571c563c534c523b5f1b5b1b573b531b4f1b4e1b4d4a5f1a5b1a574a533a4f2a4d3a4b3a493a472a453a435a413a3f3a3b3a373a33495e185f185b18571853384f384e684d383f383e183b18391833383218317030782f182b782718231b4f1b4e1b4b1b471b431b421a4f1a4b1a471a433a3f3a3b3a373a33194e184f184b18471843183f383e183d182f182b1827182318151c5f1c5e1c5b1c571c531c521b5f1b5b1b571b536b4f3b4b3b476b431a5e195f195e195b195719531952194f194d194b194a1947394619457144193f193b19371933185f185e185b185a1857185618531852184f684e184d183f583e183b183a183728361833183218258824181f181e181d4c5f1c5b1c574c532b5f1b5b1b574b532b4f5b4b2b475b434a5f4a5e1a5b1a5a1a571a564a534a525a4f6a4e5a4b3a4a5a473a465a435a421a3f1a3e1a3d495e185f485e185b185718534852784f184b78471843183b283a183928372836183318312827282628251c5f1c5b1c571c531b5f1b5e1b5b1b571b531b522b4f2b4b2b472b431a5e195f195b19571953194f194b19471943193f293e193d1937193519331932185f185e185b185a1857185618531852184f684e184b184a1847384618431842183728361835181f181e181d4c5f1c5b1c574c532b5f2b5e1b5b1b5a1b571b562b534b522b4f2b4e2b4b3b4a2b472b462b436b422a5f1a5b1a572a532a4f2a4b2a472a431a3f1a3e1a3d495e185f185b18571853784f184b78471843283f283e583d282f282e182b182918232822182120201b4f1b4b1b471b431a4f1a4e1a4b1a471a431a422a3f2a3b2a372a33194e184f184b18471843183f183b18371833182f282e182d18151c5f1c5b1c571c531b5f1b5e1b5b1b571b531b522b4f5b4b2b475b431a5e195f195e195b195719531952194f194b19471943193f193d193b193a1937293619352134185f185e185b185a1857185618531852184f684e184b184a1847384618431842183f583e183d18258824181f181e181d4b4f4b4b4b474b434a4f4a4b4a474a43f23fe23bd237b233494e484f484b48474843a03f903b80376033502f402b30271023001f 16 65535 6 63 11 2047 16 65535
def f_64 : Nat → Nat × Nat := unpackForestF 0x18fc63b18df34418cc43f10ec437751043310bc42b109c934108c01f 4 10
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV4 m_64 g_64 ep_64 16 bds_64 (dagTraceF m_64 s_64 8 f_64) (cur_64 0) s_64 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64 : treeBlockF 0 16 (dagCheckNodeV4 m_64 g_64 ep_64 bds_64 16 (dagTraceF m_64 s_64 8 f_64) cur_64) = true := by decide +kernel
theorem nc_64 : ∀ i, 0 ≤ i → i < 16 → (dagCheckNodeV4 m_64 g_64 ep_64 bds_64 16 (dagTraceF m_64 s_64 8 f_64) cur_64) i = true := fun _ h1 h2 => treeBlockF_at nb_64 h1 h2
theorem lb_64 : LowerBin m_64 s_64 g_64 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_64 kn_64 sub_64 gl_64 rc_64 nc_64

def m_65 : Nat := 0xffff0000ffff
def s_65 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_65 : Nat := 0x17770000577f
def ep_65 : Nat := 0x400800000000000000000000006000000028000006000000020800001222000002200000144400005440
theorem epk_65 : ep_65 = edgePack m_65 g_65 := by decide +kernel
def bds_65 : List (Nat × List Nat × Nat × Nat) := [(m_35, s_35, 6, g_35), (m_38, s_38, 5, g_38), (m_26, s_26, 5, g_26), (m_39, s_39, 5, g_39), (m_47, s_47, 5, g_47), (m_41, s_41, 5, g_41), (m_58, s_58, 5, g_58), (m_19, s_19, 4, g_19), (m_0, s_0, 4, g_0)]
theorem kn_65 : KnownBin bds_65 := by
  intro b hb; simp only [bds_65, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_35
  · exact lb_38
  · exact lb_26
  · exact lb_39
  · exact lb_47
  · exact lb_41
  · exact lb_58
  · exact lb_19
  · exact lb_0
theorem sub_65 : ∀ b ∈ bds_65, m_65 &&& b.1 = b.1 := by intro b hb; simp only [bds_65, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_65 : ∀ b ∈ bds_65, canon b.1 g_65 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_65, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_65 : Nat → List (Nat × Nat) := unpackCursorV4 0xd00a18a007187006a3643339038001 0x3c5e3c5d5a5e3a5d5a4e3a493a423a41815d195969551951392d3125685e485d485c28594855685228512850382d48251c5e1c5d625d3a596a553a51595e195d594e194919421941192a2126885e485d485c28594855785228512850181d48151a50195028503a50395028505b5e435a6b565b523a5a32561a3e1a3d195a2156393e193d392e1929192219211920483d28394835283128292821281918115a4f3a4b72473a43594f194b51471943392f192b11271923484f284b48472843382f282b48272823181f281b48171813001f 12 4095 5 31 11 2047 16 65535
def f_65 : Nat → Nat × Nat := unpackForestF 0x215d191da5d151cb5a2958956149c01f 4 10
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV4 m_65 g_65 ep_65 9 bds_65 (dagTraceF m_65 s_65 7 f_65) (cur_65 0) s_65 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65 : treeBlockF 0 9 (dagCheckNodeV4 m_65 g_65 ep_65 bds_65 9 (dagTraceF m_65 s_65 7 f_65) cur_65) = true := by decide +kernel
theorem nc_65 : ∀ i, 0 ≤ i → i < 9 → (dagCheckNodeV4 m_65 g_65 ep_65 bds_65 9 (dagTraceF m_65 s_65 7 f_65) cur_65) i = true := fun _ h1 h2 => treeBlockF_at nb_65 h1 h2
theorem lb_65 : LowerBin m_65 s_65 g_65 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_65 kn_65 sub_65 gl_65 rc_65 nc_65

def g_66 : Nat := 0x1171777155f577f
def ep_66 : Nat := 0x14484008000016600000422000160060004a002801060600040a020801121222100002200114144415505440
theorem epk_66 : ep_66 = edgePack fullMask g_66 := by decide +kernel
def bds_66 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 7, g_32), (m_65, s_65, 8, g_65), (m_25, s_25, 7, g_25), (m_24, s_24, 7, g_24), (m_63, s_63, 8, g_63), (m_27, s_27, 7, g_27), (m_15, s_15, 4, g_15), (m_64, s_64, 9, g_64), (m_51, s_51, 5, g_51), (m_31, s_31, 7, g_31), (m_61, s_61, 9, g_61), (m_48, s_48, 6, g_48), (m_36, s_36, 7, g_36), (m_29, s_29, 7, g_29), (m_53, s_53, 5, g_53), (m_41, s_41, 5, g_41), (m_62, s_62, 9, g_62), (m_10, s_10, 4, g_10), (m_40, s_40, 7, g_40), (m_49, s_49, 6, g_49), (m_37, s_37, 7, g_37), (m_30, s_30, 4, g_30), (m_7, s_7, 4, g_7), (m_28, s_28, 5, g_28), (m_0, s_0, 4, g_0), (m_56, s_56, 7, g_56), (m_45, s_45, 5, g_45), (m_60, s_60, 9, g_60), (m_17, s_17, 4, g_17), (m_35, s_35, 6, g_35), (m_59, s_59, 5, g_59), (m_21, s_21, 4, g_21), (m_43, s_43, 5, g_43), (m_57, s_57, 4, g_57), (m_33, s_33, 5, g_33)]
theorem kn_66 : KnownBin bds_66 := by
  intro b hb; simp only [bds_66, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_32
  · exact lb_65
  · exact lb_25
  · exact lb_24
  · exact lb_63
  · exact lb_27
  · exact lb_15
  · exact lb_64
  · exact lb_51
  · exact lb_31
  · exact lb_61
  · exact lb_48
  · exact lb_36
  · exact lb_29
  · exact lb_53
  · exact lb_41
  · exact lb_62
  · exact lb_10
  · exact lb_40
  · exact lb_49
  · exact lb_37
  · exact lb_30
  · exact lb_7
  · exact lb_28
  · exact lb_0
  · exact lb_56
  · exact lb_45
  · exact lb_60
  · exact lb_17
  · exact lb_35
  · exact lb_59
  · exact lb_21
  · exact lb_43
  · exact lb_57
  · exact lb_33
theorem sub_66 : ∀ b ∈ bds_66, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_66, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_66 : ∀ b ∈ bds_66, canon b.1 g_66 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_66, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_66_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x953348f65d8975f81a7d7c65477c4a75b216fe5d6ca3469931652475f35f5767d522544d84a48b4d409823c1483734e330432e84829a4e25248231211d45d1775d0fb7c0a75405d4a03d200013c00001 0x5d6d06c5f04c5d07c5b07c590bc5704c5506c5307c5105b4f05b4b05b4705b4306a5f0ba5d03a5b03a590ba570ba5503a5303a5107a4f03a4b0ba4703a4305a3f03a3b05a3703a330695f0195d0295b02959069570195502953029510794f0294b0d947029430593f0293b05937029330392f0292b0b92702923098560b8460583e03e7d08d6f04d6d07d6b07d6908d6704d6507d6307d6105c6f08c6e05c6d0bc6c05c6b05c6a05c6905c6805c6708c6605c650bc6405c6305c6205c6105c6005c5f07c5e05c5b04c5a05c5704c5605c5305c5205b6f05b6d05b6b05b6905b6705b6505b6305b6105b5f05b5b05b5705b5303a7103a5f03a5b03a5703a5303a4f03a4d03a4b03a4903a4703a4503a4303a4103a3f03a3b03a3703a330896f0196d0296b02969089670196502963029610795f0295b0d957029530594f0194d0294b02949059470194502943029410593f0293b05937029330392f0292b0392702923088560584e0583e01e7d01d6f01d6d01d6b07d6901d6704d6501d6301d6101c6f01c6e01c6d01c6c01c6b01c6a05c6905c6801c6701c6605c650bc6401c6301c6201c6101c6005c5f07c5e05c5b04c5a05c5704c5605c5305c5201b6f01b6d01b6b05b6901b6705b6501b6301b6105b5f05b5b05b5705b5301a6f01a6d01a6b03a6901a670ca6501a6301a6107a5f03a5b0da5703a5305a4f05a4d03a4b03a4905a4708a4503a4303a4105a3f03a3b05a3703a33019710195f0195e0195b0195701953029520194f0194d0194b01949019470194501943019410193f0193b01937019330192f0192b0192701923088560584e0583e0de7f07e7305d7f0bd7e05d7305d7205d6f07d6e05d6b04d6a05d6704d6605d6305d6205c7f05c7305c6f05c6b05c6705c6301b7f01b7e01b7308b7201b6f01b6e01b6b04b6a01b6701b6601b6307b6201b5f01b5e01b5d01b5c01b5b05b5a01b590bb5801b5701b5601b5501b5401b5305b5201b5105b5001b4f01b4e01b4b05b4a01b4701b4601b4305b4203a7f03a7303a6f03a6b03a6703a6303a5f03a5d03a5b03a5903a5703a5503a5303a5103a4f03a4b03a4703a4301a3f01a3e02a3d0197f019730196f0196b01967019630195f0195d0195b01959019570195501953019510194f0194b0294a0194701946019430193f0193e0193d0192f0192e0192b019290192302922019210286f0286a028670b8660285f0585e0285d0284f0584e028420183f0283d01837018350282f028270181f0181704d6f04d6304c6f04c6305b6f0bb6e05b6305b6204b5f04b5e04b5b04b5904b5704b5304b5205b5105b5004b4f04b4e04b4b04b4904b4704b4304b4205b4105a6f05a6304a5f04a5e04a5b04a5904a5704a5304a5205a5105a5004a4f04a4b04a4704a430896f039630495f0395b04957039530494f0394b04947039430593f0593d0393b059370b935039330592f0392b05927039230886f028630485f0285b04857028530484f0284b04847028430583f0183d0283b0583701835028330582f0282b05827028230381f0281b0b817028130dd6f07d6305c6f1e46e05c6305c6205c5f07c5e05c5b04c5a05c5704c5605c5305c5205b6f05b6305b5f05b5b05b5705b531d26f03a6307a5f03a5b0da5703a5305a4f05a4d03a4b03a4905a471424503a4303a4105a3f03a3b05a3703a331c16f029630795f0295b0d957029530594f0194d0294b02949059470194502943029410593f0293b05937029330392f0292b1b127029230585f0585a058571a0560584f0584e0584d0583f0583e058320382f038270281f0281705c5f05c5b05c5705c5303b5f03b5b03b5703b5303b4f03b4b03b4703b4302a5f02a5b02a5702a5302a4f02a4b02a4702a4302a3f02a3b02a3702a330d9560393e0785e048560584e05846038360282e0182605e7d06d6f04d6d07d6b07d6908d6704d6506d6307d6105c7105c5f05c5b05c5705c5303b6f06b6e03b6d0bb6c03b6b03b6a03b6903b6803b6708b6603b6509b6403b6303b6203b6103b6003b5f07b5e03b5b03b5a03b5704b5603b5303b5203b4f05b4e03b4b03b4a03b4705b4603b4303b4203a6f03a6d03a6b03a6903a6703a6503a6303a6103a5f03a5b03a5703a5303a4f03a4b03a4703a430696f0196d0296b02969069670196502963029610795f0295b0d957029530594f0294b05947029430393f0193d0293b02939039370193502933029310392f0292b0392702923088560383e0382e03d6d08c5f04c5d07c5b07c590bc5704c5507c5307c5108b5f0bb5d05b5b05b590bb5713b5505b5305b5107b4f05b4b0db4705b4303a4f03a4b03a4703a4303a3f03a3b03a3703a330895f0195d0295b029590b9570195502953029510794f0294b0d947029430593f0293b0f937029330392f0292b03927029230b8560b8460382e07d6105c6d05c5f05c5b05c5705c5306b6d07b5f07b5e08b5b04b5a08b5704b5607b5307b5203b4b03b4a03a6d03a5f03a5b03a5703a5303a4f03a4b03a4303a3f03a3d029610795f0295b0d957029530594f0294b05947029430893f0193d0293b02939089370193502933029310392f0292b03927029230885608d6f07d6306c6f0bc6e08c631546206c5f07c5e0bc5b04c5a06c5704c5607c5307c5205b6f05b6305b5f05b5b05b5705b5303b4f03b4e03b4d03a6f03a6303a5f03a5b03a5703a5303a4f05a4e03a4d03a3f03a3b03a3703a330896f029630795f0295b0d957029530694f0194d0294b02949069470194502943029410593f0293b05937029330392f0292b03927029230385f0385a038570b8560384f0b84e0384d0383f038370382f038270281f0281701e7d01d6f01d6d01d6b07d6901d6704d6501d6301d6101c6f01c6d01c6b05c6901c670cc6501c6301c6107c5f05c5b0dc5705c5301b6f01b6e01b6d01b6c01b6b01b6a03b6903b6801b6701b6603b650bb6401b6301b6201b6101b6003b5f07b5e03b5b03b5a03b5704b5603b5303b5203b4f05b4e03b4b03b4a03b4708b4603b4303b4201a6f01a6d01a6b03a6901a6703a6501a6301a6103a5f03a5b03a5703a5303a4f03a4b03a4703a43019710195f0195e0195b0195701953029520194f0194b01947019430193f0193d0193b01939019370193501933019310192f0192b0192701923088560383e0382e0de7f07e7301d7f01d7e01d7308d7201d6f01d6e01d6b04d6a01d6701d6601d6307d6205c7f05c7305c6f05c6b05c6705c6301c5f01c5e02c5d03b7f0fb7e03b7303b7203b6f07b6e03b6b03b6a03b6704b6603b6303b6201b5f01b5e03b5d0bb5c01b5b01b5a01b5901b5801b5701b5601b5501b5401b5301b5203b5103b5003b4f05b4e03b4b03b4a03b4705b4603b4303b4203a7f03a7303a6f03a6b03a6703a6301a5f03a5d01a5b01a5901a5701a5501a5303a5103a4f03a4b03a4703a430197f019730196f0196b01967019630195f0195e0195d0194f0194e0194b019490194302942019410193f0193d0193b01939019370193501933019310192f0192b0292a0192701926019230286f0286a02867138660185f0285d01857018550284f028470283f0383e0283d0282f0382e028220181f0181704d6f04d6304c6f04c6308b6f05b6304b5f04b5b04b5704b5304b4f04b4b04b4704b4303a6f0ba6e03a6303a6203a5f04a5e03a5b03a5903a5703a5303a5203a5103a5003a4f04a4e03a4b03a4903a4703a4303a4203a4103a3f03a3b03a3a03a370ba3603a330396f039630395f0495e0395b0395903957039530395203951039500394f0394b03947039430393f0393b03937039330886f028630485f0285b04857028530484f0284b04847028430583f0283b13837028330382f0182d0282b0382701825028230381f0281b03817028130dd6f07d631746f05c6307c5f05c5b0dc5705c5303b6f1636e03b6303b6203b5f07b5e03b5b03b5a03b5704b5603b5303b5203b4f05b4e03b4b03b4a03b471434603b4303b4203a6f03a6303a5f03a5b03a5703a5303a4f03a4b03a4703a431316f029630795f0295b0d957029530594f0294b12147029430393f0193d0293b02939039370193502933029310392f0292b03927029230385f0385a03857110560384f038470383f0383e0383d0382f0382e038220281f028170cd6f07d6306c6f06c6e06c6308c6206c5f06c5e06c5b04c5a06c5704c5606c5307c5205b6f05b6305b5f05b5b05b5705b5303b4f03b4d02b4b02b4902b4702b4502b4302b4103a6f03a6303a5f03a5b03a5703a5303a4f03a4d02a4b02a4902a4702a4502a4302a4103a3f03a3b02a3703a330196f029630195f0295b01957029530194f0194d0294b01947019450193f0293b01937029330192f0292b01927029230285f028570184f0184d02847018450283f028370282f028270281f018170ce7f07e7306d7f06d7e06d7308d7206d6f06d6e06d6b04d6a06d6704d6606d6307d6205c7f05c7305c6f05c6b05c6705c6303c5f03c5e03c5d03b7f03b7303b6f03b6b03b6703b6303b5f05b5e03b5d03b4f05b4e03b4b03b4903b4303b4203b4103b4001a7f02a7301a6f02a6b01a6702a6301a5f01a5d02a5b02a5901a5701a5502a5302a5101a4f02a4b01a4702a4301a3f02a3b01a3702a330297f0c97e02973029720296f0796e0296b0296a029670496602963029620295f0695e0295d0f15c0295b0295a02959029580295706956029550b154029530295202951029500294f0594e0294d0594c0294b0294a0294705946029450d14402943029420293f0393e0293d0393c0293b0293a0293703936029350a13402933029320286f028670285f0285d02857028550284f028470283f028370182a01827018260181701816018150cd6f07d6306c6f06c6306c5f06c5b06c5706c5306b6f06b6306b5f06b5b06b5706b5303b4f03b4e02b4b02b4902b4702b4302b4202b4102b4003a6f03a6303a5f03a5b03a5703a5303a4f05a4e03a4d03a3f06a3e03a3b03a3902a3703a3303a3203a3103a300196f029630195f0295b01957029530194f0294b029490194702943029410193f01937029330192f0292b01927029230285f028570284f0284d02847028450283f018370282f028270281f018170cd6f07d6306c6f0cc6e0cc630cc6206c5f07c5e0dc5b04c5a06c5704c5607c5307c5205b6f05b6305b5f05b5b05b5705b5302b4f02b4e02b4d0ca6f03a6307a5f03a5b0da5703a5313a4f13a4d03a4b03a4906a470b24503a4303a4105a3f05a3d03a3b05a370d23503a330196f029630195f0295b01957029530194f0194d0194701945029430193f0293b029390193702933029310192f0292b01927029230285f028570284f0184d01847018450283f0283d02837028350282f028270281f018170cd6f07d6306c6f06c6e06c6308c6206c5f06c5e06c5b04c5a06c5704c5606c5307c5205b6f05b6305b5f05b5b05b5705b5305b4f06b4e05b4d03a6f03a6303a5f03a5b03a5703a5303a4f06a4e03a4d03a3f03a3b02a3703a330196f029630195f0295b01957029530194f0194d0194701945029430193f0293b01937029330192f0292b01927029230285f028570284f0184d01847018450283f028370282f028270281f018170cd6f07d6306c6f06c6306c5f06c5b06c5706c5305b6f05b6305b5f05b5b05b5705b5303b4f03b4e03b4d0ba6f0ba6307a5f0ba5b0ba5707a5305a4f05a4e02a4b02a4902a4702a4302a4202a4102a4005a3f05a3e05a3b06a3902a3705a3305a3205a3105a300196f029630195f0295b01957029530194f0294b029490194702943029410193f0293b01937029330192f01927029230285f028570284f0284d02847028450283f028370282f018270281f018170cd6f07d630cc6f05c6307c5f05c5b0dc5705c530bb6f0cb6e0bb630bb6207b5f07b5e0bb5b04b5a0bb5704b5607b5307b5205b4f05b4e0bb4b0bb4a0bb470b34605b4305b4203a6f03a6303a5f03a5b03a5703a5303a4f03a4b03a4a03a470a24603a4302a3f02a3e02a3d0196f029630195f0295b01957029530194f0294b01947029430193f0193d0193701935029330192f0292b029290192702923029210285f028570284f028470283f0183d01837018350282f0282d02827028250281f018170cd6f07d630cc6f05c6307c5f05c5b0dc5705c530cb6f03b6307b5f03b5b0db5703b5305b4f03b4b0e34703b4301a6f02a6301a5f02a5b01a5702a5301a4f02a4b01a4702a4301a3f02a3b01a3702a330296f0c96e02963029620295f0795e0295b0295a029570495602953029520294f0594e0294b0294a029470c14602943029420293f0393e0293b0293a029370913602933029320285f028570284f028470283f028370182a018270182601817018160181505c5f05c5b05c5705c5303b5f03b5b03b5703b5303b4f03b4b03b4703b4301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330d9560192e0785e048560584e058460383e038360182605e7d06d6f04d6d06d6b07d6906d6704d6506d6306d6105c7105c5f05c5b05c5705c5306b6f06b6d03b6b03b6906b6709b6503b6303b6107b5f03b5b0db5703b5305b4f03b4b05b4703b4301a6f01a6e01a6d01a6c01a6b02a6a01a6902a6801a6701a6601a6501a6401a6302a6201a6102a6001a5f01a5e01a5b02a5a01a5701a5601a5302a5201a4f01a4e01a4b02a4a01a4701a4601a4302a4201a3f01a3e01a3b02a3a01a3701a3601a3302a320196f0196d0196b01969019670196501963019610195f0195b01957019530194f0194b01947019430193f0193b0193701933088560182e0181e03e7d08d6f04d6d07d6b07d6908d6704d6507d6307d6108c6f06c6d05c6b05c6908c6706c6505c6305c6107c5f05c5b0dc5705c5303b7103b5f03b5b03b5703b5303b4f03b4b03b4703b4301a6f01a6e01a6d01a6c01a6b02a6a01a6902a6801a6701a6601a6501a6401a6302a6201a6102a6001a5f01a5e01a5b02a5a01a5701a5601a5302a5201a4f01a4e01a4b02a4a01a4701a4601a4302a4201a3f01a3e01a3b02a3a01a3701a3601a3302a320196f0196d0196b01969019670196501963019610195f0195b01957019530194f0194b01947019430193f0193b0193701933088560182e0181e0de7f07e7306d7f06d7e06d7308d7206d6f06d6e06d6b04d6a06d6704d6606d6307d6205c7f05c7305c6f05c6b05c6705c6303c5f03c5e03c5d03b7f03b7303b6f03b6b03b6703b6303b5f05b5e03b5d03b4f05b4e03b4b03b4903b4303b4203b4103b4001a7f01a7e01a7302a7201a6f01a6e01a6b02a6a01a6701a6601a6302a6201a5f01a5e01a5d01a5c01a5b02a5a01a5902a5801a5701a5601a5501a5401a5302a5201a5102a5001a4f01a4e01a4b02a4a01a4701a4601a4302a4201a3f01a3e01a3b02a3a01a3701a3601a3302a320197f019730196f0196b01967019630195f0195d0195b01959019570195501953019510194f0194b01947019430193f0193b01937019330286f0286a028670b8660285f0285d02857028550284f028470283f028370182f0182e0282d0181f0181e0181204d6f04d6304c6f04c6308b6f05b6304b5f04b5b04b5704b5304b4f04b4b04b4704b4308a6f03a6304a5f03a5b04a5703a5304a4f03a4b04a4703a4305a3f03a3b0ba3703a330196f0196e01963029620195f0195e0195b0195901957019530295201951029500194f0194e0194b0194901947019430294201941029400193f0193b0293a0193701936019330192f0192b0292a0192701926019230186f018630185f0185e0185b01859018570185302852018510184f0184b01847018430183f0183b01837018330182f0182b01827018230dd6f07d630646f05c6307c5f05c5b0dc5705c530536f03b6307b5f03b5b0db5703b5305b4f03b4b0434703b4301a6f01a6e01a6302a6201a5f01a5e01a5b02a5a01a5701a5601a5302a5201a4f01a4e01a4b02a4a01a4701a4601a4302a4201a3f01a3e01a3b02a3a01a3701a3601a3302a320196f019630195f0195b01957019530194f0194b01947019430193f0193b01937019330285f0285a02857030560284f028470283f028370182f0182e0282d0181f0181e0181205c5f05c5b05c5705c5303b5f03b5b03b5703b5303b4f03b4b03b4703b4301a5f02a5b01a5702a5301a4f02a4b01a4702a4301a3f02a3b01a3702a33019260785e048560584e058460383e038360282ebb45f07c5b1bc5707c53ba35f10b5b1bb5710b5307b4f10b4bb434707b43b025f0aa5b1ba570aa5307a4f0aa4ba724707a4310a3f0aa3b8a2370aa338415f1b95b1b9577a1530794f7414b70147079431093f6e13b5f137109330a92f5c12b4c1270a9234605f1b85b1b857450530784f4404b20047078431083f1f03b19037108330a82f1802b100270a8230801f0701b02017010130003f 20 1048575 8 255 11 2047 20 1048575
def cc_66_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x7e33277e657512d72b266dd4e6b627651656242d5fd275d7265894e55435552025430f500434aa56425853fc293d3293c01335967303562c73c282451fc861c03c16a561254509f860712e0215000021 0x4d6d098da12d7c25ad84b57096a622d3de1a685b4b0b6930cd1e11a285b430b6821297c1d2d84a57074a62293db92683a4b074930091df92283a4307482168fc1d1db3237074661257c14ad84957052a62253c0ca68294b052923e51c0ca28294305282164fc149d8f937052660e4bc14958f92705246179f426b784d6e09ada135b026b588d6a09ad2275a026b384d6609aca1359026b186d6209ac2f1580263784c6d098d6131a4263384c65098c6131842db884b5f096bc16d75d9ae04b5b096b212d5c25aa84b53096a416d442da804b4f0969612d1c25a186a6f114da0e9ac1d3488a67134ca0e98c1d3084a5f6c4ba0e96c1d2c84a57094aa0e94c1d2884a4f074961291c1d2185a3f07476168dc1d198696f032da0a5ac14b486967032ca0a58c14b08495f032ba0a56c14ac84957032aa0a54c14a88494f052961251c14a18593f05276164dc14998392f052566249c14918886e170d8121782427058361104c22058363684c5f098bc12d6c25ab84b530b68e1ad182da284a5f074b61295c1d2986a4f0d49a0e92c1d2486a471d48a0e90c1d2085a3f07476168dc1d198495f052b61255c14a98694f0329a0a52c14a4869470328a0a50c14a08593f05276164dc14998392f052561a49c149185d6d098be13174262d84c57098aa1adb425af84b5d0969e1a97c1d2d86a57074a61293c1d2584a47074861a8fc1d1d86a37074661a57c14ad86957052a61253c14a584947052861a4fc149d86937052660e4bc14958692705246135bc26b193c6f278dc1b18de23104c5f098bc1315c262984c520b6deecdb82db185b62096be12d6c25ad04b57096ac12d4c25a384b460968ae49bc1d3184a5f074b61295c1d2986a4f6049a0e92c1d2493a472748a0e90c1d2085a3f07476168dc1d19ad16f052c61257c14ad84957052a61a53c0ca68294b052921a51c0ca28294305282164fc149d85937052660e4bc1495a5127052461217c242b8584f0b09a1611c2c228583f0b07a160dc2c1a8382f0704e0a07c140b83e7d09ada135a426b284d61118dc231b4463608c6a0d8d21b1a0463313c65238c823188363086c60098bc16db42db485b650b6c212d6825ab04b460968a0e9c41d2683a490748a0e9040cb682969032ca0a5840ca6829490328a0a5041f3e84d6f09adc135b426b604d6b11ad4135a4a6b404d6709acc1359426b204d6311ac413585bab004c6f098da131ac263484c67098ca1318c263088b6f116da16dac2db488b67296ca16d8c2db084b5f726ba12d6c25ac84b57096aa12d4c2da884b4f0969612d1c25a183a71074be129781d2eb525c074b60e9641d2b83a55074a60e9481d2883a500749e0e92c1d2383a430747e0e8ec1d1b83a33112de065b414b582969112ce0659414b182961092be0657414ad82959092ae0655414a9829510929e0a52c24a3829430b27e0a4ecc49b829330725e0a4ac1c9382923110dc2e1b0242f0484e1106c0e098440b08c6d098be1317825af84b5b096ae12d4c45a786b4d0b69616d2445a386b450b68616d041d2d83a57074a60e91c452303a450747e0e8ec1d1b83a33092be0a56c24ab829531129e0653414a5829491128e0651414a1829410b27e0a4ec749b829330725e0a4ac1c93829230bcfa135b426b484d6509ac21b1b8463686c6c118d4271a44e3408c66138ca27190363108c610d8c00f1782db885b4d0b69216d142da083a6d074d20e9941d3083a5a094ac129181d228196d052d20659414b08194d052920651414a083d6d098be13174262d84c57098aa22db425af84b5d0769e2297c2d2d88a570b4a61293c252584a47094862e8fc2d1d8ba370b4662257c14ad88957052a61253c14a584947052862e4fc149d8b93705266164bc14958e92705246135bc26b18bc6f178dc2f18dba3103c5f078bc0f15c1e2983c526c6de16d8c25af84b5b096ae12d4c5da7b034d0b69616d245da38bb450b68616d041d37b526e074c60e9881d2f83a5b074b40e95c252b03a530748e129181d2283a3f074760e8dc1d19ac16f052c61257c14ad84957052a62e53c0ca68294b052922e51c0ca28294305282164fc149da8137052660e4bc149583927052460e17c1c2b8384f0709a0e11c1c228383f0706e0e0bc1c16838270704a0a07c140b84e7d09afa571c4463804c6e098d413198263108c5e0d8ba1b170ae2d11c59238b057158362a86c54118a447144462805b5d0b6b416d642dac15b560b6aa1ad502da883b4e0769a0e9741d2d03a59074b0569581d2a8ea54074a2169381d2685a3e074720e8c81d1883a30032ba0a5640caa829510329a0a5240ca282941098a80e8c0afc006d8c0daf8135e026ba11d70646f812de025ba11b700f6d812d901d200885417068135bc26b186c6f118dc1b18c363104c5f098bc0f15c1e2983c520b6de16d8c1daf84b5b096ae12d4c2da386b460b68a0e9bc1d3183a5f074b60e95c1d2983a470d48c0e9141d1f83a3b0746e0e8cc34b782963092be0a56c24ab829530d29e0653414a5829490d28e0651414a1829410b27e0a4ec2c9b829330725e0a4ac1c9382923070be0e15c1c278384d0708e0e1141c1f838370705e0e09c140f8281709ade1358c2e3785c63098be1316c262b83c53236de22db88db188b62096be12d781dab83b53076a412d3c25a703b4b076940ed1c1da303b43076840e9bc1d3183a5f074b60e95c1d2983a4f074960e91c1d2183a3f0747a0e8ec1d1c83a370746a0e8cc1d189196f052c61257c14ad84957052a61653c14a58594705286464fc0c9e8293b05272464dc0c9a82933052620e4bc149583927052462e1b81c310385f070ae0e13c1c25038470b08c0e0fc1c1e8383a0706e1e0d81c1a878340705e0e0a81c13838260503e0a05c273f84e7e09ce6cd9c826bf84d730d8fe231f98a3988c72098de131b83636b046c098d6131a8263484c68098ce13198263284c64098c6131888e30af460098be13178262d84c5a098ae13158262984c520b6fe16dcc25b785b6d096d612da425b384b65096c616d8425af84b5b096ae12d4c1da783b4e0769a0e9fc1d3983a6f074da0e9ac1d3483a67074ca0e98c1d3083a5f074b60e95c1d2983a4f0b49c0e9341d1f85a3e074760e8e41d1983a32074620e8c158bf82973092de065b414b582969092ce0659414b182961092be0a56c24ab829530d29e0653414a5829490d28e0651414a1829410b27e0a4ec2c9b829330725e0a4ac1c9382923170fc0e1c81c378486e070da0e17c242f038520709e0e1341c25038471708c0e1145c220383f070740e0dc2c1b0382f070540e09c1c130281f070340a05c5c0b01e7d03ada135a426b281d61038dc071b40e3601c6a0d8d21b1a00e3306c65198c8071880e3081c60098bc06db42db485b65036c212d6825ab04b460968a069b41d348ca65034c21a9341d248ea4507482065c40caf029520329a065240ca28194103cfa075b426b484d6503ac2071b80e3681c6c038d42f1a4663401c66178ca2f1900e3101c61038c00f1780db685b69196ca06d8435a685b490d68a16d040d3683a69074ca069841d2d04a560948c0e9140cb88195e052a4065340ca48194503282079f0673c04e7403ce0071f0663c06c74038e01b1b0263404c64238c00e8c00cb602960032980a5000c3e0884403cfa075bc0eb701d6d03ad8075ac0eb504d6919ad00759c0eb304d6509ac80758c0eb101d6103ac0071bc0e3681c6b098d20719c263281c63038c206dbc0db681b6b0b6d206d9c65b281b63036c212d7d69ae84b5b096b212d5c25aa84b530b6a212d3c25a584b4709686069bc0d3681a6b074d20699c653281a63034c21297d612e83a5b074b21295c252a83a53074a21293c1d2584a4707486168fc1d1dab23707466065c40caf8195e032ba065700cad81959032ae065540ca982952032a20a5400ca78194e032960651c0ca1829420327e064ec0c9b819330325e064ac0c9381923030dc061b0242f0484e1106c220980c0b04d6f09ac6171bc2e3184c5f098b61315c162997b6f116dc5ed8c45b101b5f036bc06d5c0da981b520969e12d3815a582b4a0568e0ad1815a182b42314de0e98c252f83a5b094ae0e94c2d2783a4b0b48e0e90cbd1f8ea3d074760e8e4bd1b8ea35074660e8c40cb781963032be0656c0cab819530329e0652c0ca3819430327e064f40c9d819390326e064d40c99819310325e064ac0c9381923270dc0a188142f818570509e0a1281423858460507e0a0f40c1d018370306c060d40c1a0282f0504e0607c0c0d018170302c2f5f876b903d6e05ac4071f8463901c6e098d407198263101c5e038ba071705e2d01c59178b0071580e2a81c54178a407144762805b5d0b6b216d542da881b4e0569a3a9f81d3903a6a094cc129581d2a81a4e0749a3a9300d2481a45034840e9041d200195d032b2065540ca88194e0329a064f80c9c82932032620a4a80c930285d050aa0a1340c228282d0504a139f87f3905c6d098d2131942e3088b7e116e412db8d5b697b6c096d412da425b404b66096ca12d9025b10eb611d6c012d7825ad04b56096a40ed3815a502b4605684629f81d3904a6e074da3a9b01d3483a65074c40e9841d3003a4a0b48c068d80d1a8196d032d2065940cb08193d03272064d40c988192d0324a2e1f814390486e050da1217814290284a0b08c0a0f4141d0b8360506a220d01415038260303406058273f84e7e09ce63f9c826bf84d73038fe071f80e3988c72038de071b80e3681c6c038d6131a80e3484c68038ce071980e3281c64038c6131880e30a9460038be071780e2d84c5a038ae071580e2984c520b6fe16dcc25b785b6d096d612da425b384b65096c616d8425af84b5b096ae12d4c0da781b4e0569a629fc1d3984a6f504da0e9ac1d3484a67094ca0e98c1d3084a5f074b61295c1d2981a4f4e49a0692c0d2481a470348a0690c1d2085a3f07476168dc1d198197f032e6065bc0cb68196b032d20659c0cb281963032c20657c0cad81957032a60653c0ca70194d0327e064f80c9d81939032660a4c80c988192f032560a4a80c9381926032464e1f814390286f090dc0a1b4142f8485e050a40613c14268184a0308e061180c22818440507e0a0e8141b858360505e0a0a81413938260303e060680c0b818161fafc1b5c826b702d620d8fc171c8263504c66098ac131540dbf08b72036dc12da80db304b62036bc06d740dae06b5a036b24ed600dab01b55036a81ad480da886b500369c16d280da486b480368c16d080da085b40074ba0e9641d2a83a510347c0a8f40cae81959032aa0654414a5019460327c064f40c97019290524406484142e828550509a0a114141e8183509ade1358cc63785c63098be1316c262b84c53076de0ed8c1daf83b5b076ae0ad4c1da783b4b0768e0ed0cbd3788a6e2f4c6229880d2f81a5e034ae0694c0d2905a4f0b49c5e92c352517a470d48c1690c2d2103a3f0747c0a8ec151d02a370546c0a8cc15190196f032c60657c0cad81957032a60653c0ca58194703286064fc0c9d8193703266064bc0c968192b032520649c0c9281923032422e1b814310285f030ae0a13c14238283f050740a0dc1c1b0282f0505a060a80c13818260304a060900c0f8181a0302e06058273f0fe720d8fc171c8263705c6d0d8d8131a4263284c620b8c2171801db683b69076ca0ed841da683b45114fc1a9c8253706a6d2f4d8129a8253484a68094cc12994253204a620d4c21a980252f04a5a094ac129480d2301a450747c0a8e8151b02a32032da065a40cb2819610329a065140c96819290324a064845c3f02872090dc0a1b4242f028520509416118141d038360505a0a0a834130282511048060680c0b04e7f09cfc139cc7f3904d7f09ae6631fc2e3984c6f4a8da131ac263484c67098ca1318c2e3084c5f098b61315c262981b7f036fc06dcc45b901b6f036dc06db40db601b6b096d406da425b401b67036cc06d940db201b63096c406d8521b001b5f036bc06d6c25ad01b57036ac06d4c25a901b4f0369c06d2d19a501b470368c06d0c2da103a7f074e60e9bc1d3683a6b074d20e99c1d3283a63074c20e97c1d2d83a57074a60e93c1d2583a4707486068fc0d1f02a3d032fe065cc0cb78196d032d6065a40cb381965032c6065840caf8195b032ae0654c0ca78194b052940651c0ca3019430327e064f80c9e8192f0325c064ac0c948192305244064845c3f02872050de121b814368285f090bc0a14814278284a0508e2e1180c1f8283d03074060dc0c1b01835030680a0bc1415028270704c0607c0c0d018170302c13184262884b51174ba1293c252584a490948e1290c2d2084a3f09476128dc25198b95d0929e0e52c1ca484947072860e504249f8393b0926e0e4cc2c978392b1724e0e48c0c2e8484f050961211c14218483f05076120dc14198582f050564e09c14118381f050362e05c140984d6f09adc1358df2b104c6f098c6f4dbc2db184b5f746ba12d6c25ac84b57096aa12d4c2da884b4f0969612d1c25a1b826f074c61297da12e83a5b074b21295c252a83a53074a21293c1d2584a4707486168fc1d1dae23707466a85bc14b18495f032ba0a56c14ac84957032aa0a54c14a88494f052961251c14a18593f05276984dc14998392f052568849c1491a106e1b0c41217c242f0785d0909e1213824210583f1b074160dcd01b0382f1b0540e09c88130281f1b0340a05c180b05c5f0b8b61715c2e2983b5f076b60ed5c1da983b4f076960ed1c1da182a5f054b60a95c152982a4f054960a91c152182a3f054760a8dc15198d9560b29c1e178242b058460707c0e0d8141701826 20 1048575 8 255 11 2047 19 524287
def cc_66_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x86f55808677a5637267f6a77f63d6a5a5985753052a4b4dd4d4a736463444154e3cb4a3626930d552e12c2924f22f631ec431c923185441622311e440fb230d8230b5230902505f31056090312500031 0x19ade1f5ac4eb387d63038de071ac0e3381c63038be0716c0e2b81c530d6de16dac35b385b630d6be16d6c35ab85b530369e06d3815a68aa6f074d62699c1d3187a5f074b62a95c1d2981a4f03496069240d2381a4307482168fc1d1d86a37074660a5bc14b582967052c60a57c14ad82957052a60653c0ca70294d0527e164f8149d82937052660a4c80c93819260324a0a1bc143582867050c60a17c142d82857050a60613c0c2581847030860a0fc141d82837050660a0bc141582827050460a07c140d8281705026335bc3eb589d670fac61b1bc663709c6b0d8ce3318c663106c5f0f8bc4b16c262d06c57098ac1f14c3e2906b6f0b6d61ad9c2db186b5f0b6b61ad5c2da982b4f0569c0ad34553783a6b134ce0e98c3d2f83a5b154ae0e94c552781a4d074960e9240d2381a45074860e9042d1f8aa3d074761a8dc551a83a33032de0a5ac0cb382963032be0a56c0cab829530329e0653414a5829490328e0651414a1829410327e0a4ec149c81937052660a4c40c978292b0324e0a48c14378286b050ce0a18c142f8285b050ae0a14c14278284d050960a11c1422828430507e0a0ec141b828330505e0a0ac1413828230503e0606c0c0b8281319ade1f5ac66b387d63198de331ac66338cc630f8be4316c962b87c53156de0edac55b383b630f6be0ed6c55ab83b531569e0ed2c55a383b43034de0a9ac0d3382a63034be0a96c0d2b82a530349e0a92c152501a47bc48c0a90c0d1f83a3e0347a068dc0d1a82a33054640a5bc64b70296b052ce0a58c14b10295f0f2bc0a56c14ad02957092ac0a54c14a90294f0b29c0a52c14a502947ba28c0a50c14a1019370326c064d414978292e0525a0a1bc143582867050c60a17c142d82857050a60a13c142582847050860a0fc141d82837050660a0bc0c1581827050460a07c140e8281b0502e0a054140984e7f0fcfc139f426bc84d7309ae2271fc4e3984c6f098da131ac2e3484c67338ca1318c263084c5f098b61315c262981b7f036fc06dcc45b901b6f036dc06db40db601b6b096d406da4cdb401b67036cc06d940db201b63096c406d8425b001b5f036bc06d6c25ad01b59096b006d5c0dab01b53096a406d443da801b4f0369c06d2ea1a501b470368c06d0c2da10aa7f074e6129bc253683a6b074d21299c553283a63074c21297c1d2d84a57074a62693c1d258aa4707486068fc0d1f02a3d032fe065cc0cb78196d032d6065a40cb381965032c6065840caf8195b032ae0654c0ca78194b192940651c0ca3019430327e064f80c9e8192f0325c064ac0c9481923072440648424378486d090ce2e194242f848571309e3611c0c1f8883d0306e060d41c17838270303e0605c2f3f85e7e0bcfa275fc3eb986d6f09ada1f5ac3eb489d6709aca1b58c3eb085c790b8e6171c4362f85c5b0d8ae1714c0dbf81b7e036e622dc80db781b6e036da06db00db589b6a036d226da00db381b66036ca06d900db186b62036c344d800daf81b5e036b612d680dab81b56036a61ed480da781b4e036961ad280da4d33480368e06d180da185b420368216d004d3f83a730d4de2a9b41d3583a69134ce269941d3183a610f4be0e96c552b83a530b49e0e92c352383a430347e068f8151e8197f032e6065bc0cb68196b032d20659c0cb281963032c20657c0cad81957032a60653c0ca58994a0328e065180ca18193f0327c064f40c978192e03256064a40c9183922032421a1bc5c3686867130ca1e17cc42b8584f0b08e060fc441e818370306a0e0bc1c138181f0302e135bc26b584d6709ac61b1bc2e3586c670b8c61317c262d81c57098a62adbc1db589b67076c612d7c1dad84b57076a616d3c1da586b4707686729bc453709a6b134ce7298c453101a5f034bc1296c252d01a57034ac0694c0d2901a4f0349c1a92c352501a470348c0690c0d2103a3f0747c0a8ec151d04a370546c0e8cc1d190196f032d60659c0cb18195f032b60655c0ca98194f03296425280ca38194603286064fc0c9d8193703266064bc0c968192b032520649c0c928192303242361bc143589867050c61217c142d84857050a61613c142585847050860e0fc141d8383705066360bc44168282b1b04e2209414118181f030360605c0c0984e7f09cfc139ec273b84e731fce4135fc26bd84d7709ae6135bc26b704d6d0d8fe171ec363b85c73098de131b83e3684c5f098bc1316c262c84c53098a4171440dbf81b7e036f606ddc0db996b72036de06db80db681b6c036d612da80db484b68036ce06d980db281b64036c612d880db0d9360036be06d780dad84b5a036ae06d580da984b520369e06d380da586b4a0368e06d180da185b42154fe0e9ec4d3b83a73094de2a9b41d3583a69094ce129941d3183a61094be0e96c252b83a530b49e0e92c352383a430347e068f8151e8197f032f6065dc0cb98196f032da065ac0cb481967032ca0658c0cb08195f032b60655c0ca98194f03296425280ca38194603286064fc0c9f0193d0325e064b80c9581929032460e4880c908d87f050f6261dc14398486f170da0a1ac243384865050c61217c142d84857050a61613c14258584705086060fc6c1e8183b0306e060d40c198382f050560e09c14118181f030360605c0c0981d7e03ae41f5b826b504d660fac4231f8463909c6a2d8cc23178462e88b7d136ea2ad744daa81a7e034fa1e9b8453516a660f4c4169782d2e85a5c0b49c1a928452486a480b48422904452002a3a0d46c0e8c80cbe81975032ba065540c96819250324222174442a8884d1108a220b4441288d6f0fac6071bc0e3701c63038c41b17c362f06c5b098b41b15c262b06c530f8a41adbc35b705b63116c41ad7c2dad89b5a0d6ae1ad582da986b4f0d69c1ad34453783a630f4be0e96c552b83a530d49e2a934352386a4507486168fc1d1d86a3707466065bc0cb18195f032b60655c0ca98194f0329a0651c0ca2819430327e064ec0c9b819330325e064ac0c93819230d0be1a15c34278684d0d08e1a1142c1f8683d0b06e1a0d41c17838270303e0605c46b787d63118de2318c3e2f89c5b2d8ae1f14c45b78ab6d156ca0ed8c3daf83b5b156ae0ed4c4da783b4b1568e0ed0c0d3781a6e034da1e97c3d2f08a5b094b45a95c252b07a530f4a42693c2d2708a4ba24955c91eb12308a430b4840a8ec151d0aa370546c0e8cc0cb78196d032ca0658c0caf8195b032ae0654c0ca78194b0328e0650c0c9f8193b0326e064cc0c978192d0324e064940c918785f110ae2213c44238383f0706e220bc5c16888271704a0607c0c0b87e7e09cfa135e426b889c7e138e4131b42e3486c65098c212db41db48ab65076c226d3455a288a7e114e4129b8253684a6c094d41a9a4353404a66334ca66990253104a61094c012978252d04a56094a4069180d2283a3e054740a8d81d190196d032d2065940cb08194d0328a064b40c948192503242121b45c328882d1104a175bc2eb705d6d138de1f18c362f86c5b0d8ae1b14c4db783b630d6be1ad741dad86b57136aa0ed4c3da783b4b1568e0ed0c353786a6d0d4ca0698c0d2f81a5d034ae069540d2986a4f0d4961a91c352183a3f054761a8dc1d198196f032c60657c0cae8195b032ae065540ca98194f032960651c0ca18193f03276064dc0c998192f032560649c0c918685f0d0ae1a13c34238383f0706e1a0bc34138181f0302e1b5bc36b706d6d118de1f18c462f84c5d0f8b61f164462b84c550f8a61f14435b786b6d0d6ca06d8c0daf81b5d036ae06d540da986b4f0b6961ad1c2da188a6f074c62297c452e83a5b074b22295c552a83a53074a21e93c1d258aa4707486168fc1d1d86a3707466065bc0cb18195f032ba0656c0cac81957032aa0654c0ca88194f032960651c0ca18193f03276064dc0c998192f032560649c0c918885f110ba2215c442a8784f1108e160fc2c1b8382f0704e0607c0c0b88d6f0fac6071bc2e3186c5f0b8b61b15c2e2988b6f076c61ed7c1dad8ab57076a616d3c1da586b47076861a9bc453706a6d0d4be1e978352d84a5a0d4ae12958352986a520d48e1a918352283a3f0747c0a8ec151d06a370546c0e8cc1d190196f032c60657c0cad81957032a60653c0ca58194703286064fc0c9d8193703266064bc0c968192b032520649c0c9281923032421a17c342b8584f0b08e0e0fc1c1b8682f0d05a1a09c34128181f0302f515bc3eb589d670fac61b1be9a3705c6b0d8ce1718c863106c5f0b8b61b15c2e298ab6f076d626d9c1db187b5f076b62ad5c1da985b4f1569a0ed2c35a38ab4507686729be913706a6b134ce1a98e893107a5f0f4bc1a96c252d1ea57094ac1a94c3d2901a470348c069141d1f83a3e054760a8e8551b82a36074660e8c80cb78196b032ce0658c0caf8195b032ae0654c0ca78194d032960651c0ca2819430327e064ec0c9b819330325e064b40c95819290324e064940c9181921900de0a1ac4c33828630f0be0a16d182b828530b09e0a12c2c23828430707e0a0ec1c1b828330d05e2e0b41415868271704a0a08c0c0f8181b0302e0604c66b787d6b13ace1f58c4e3785c6b138ce1718c3e2f85c5b218ae1714c0db781b6b036ce06d8c0daf81b5b036ae06d4c0da781b4e0369606d1c0da185b42154de0e9ac4d3383a630f4be0e96c552b83a530b49e0e92c552383a430347e068f8151e8296f052d60a59c14b18295f052b60a55c14a9819470328c065140c9f8193e0527a0a4bc1c970292b0524e0a48c14910286f050d60a19c14318285f050b60a15c14298284f050960a11c14218183f03076060dc0c198282f050560a09c14118281f050360a05c140988d6d118be131743e2d87c59118ae131543e2987c51116be1ad742dad85b59116ae1ad542da985b510f69e16d2c6da385b43074ae0e9541d2783a4b0748e0e90c1d1f83a3b0746e0e8cc0cab819550329e0652c0ca3819430327e064ec0c9b819330325e064ac0c9188d6f0fac6231bc2e3187c5f0b8b63715c2e2988b6f9c6dc22d8c5db107b5f0f6bc22d6c25ad0bb57096ac1ed4c3da905b4f0b69c22d2c5da50bb472768c16d0c2da103a6f074c60e97c1d2d83a57074a60e93c1d2583a47074860a8fc151e82a370546a0a8cc0cb781963032be0656c0cab819530329e0652c0ca3819430327e064f40c9b8193503266064bc0c9581927032462e1b814310285f050ae0a13c1423818370306c060d414178282a0504e0e0980c0f8181a0302e0605adab787d6b19ace1f58ed2378cc6b198ce4318c3e2f90c5bb08ae1f14c0db781b6e036d606d9c0db1d5362036be06d780dad84b5a036ae06d580da987b520369e06d380da5d034a0368e06d180da185b42154de0e9ac553383a630f4be0e96c552b83a531549e0e92c552383a430347e068f8151e8196f032d60659c0cb18195f032b60655c0ca98194f032973c5280ca38194603286064fc0c9f0193d0325e064b80c9581929032460e4880c90c706f050d63219c14318785f050b68815c14299084f050966c11c14218183f9a07a060ec0c1b81835030660e0bc141583827050460607c0c0d8181703026135b43eb086c6d178d82f1845e3006c5f0f8bc3716c262d06c57098ac1f14c3e2905b6d0b6c216d7c2dad85b570b6a60ed3c1da703b4d074da0e9841d2f83a5b074ae0e94c1d2785a4e0749a0e8fc2d1f03a3b074720e8cc1d1903a3107460065b414b08795f052b63655c14a98694f0329a0a52c14a4869470328a0a50c14a08593f05276164dc14998392f052560e49c14918b8561709c2e1302c1f0382e09ada1f5842e3685c61176da22db05db088b600f6bc12d6825ab07b520769c0ad2815a302b42074da0e9841d2505a460346c068d40cb6819610327a064e40c9a819310325a064945c2b0584e1706c220d01c1704d6d0fac2071b40e3601c61178c00717c0e2f01c5b098b40715c0e2b01c530f8a416db42db085b5f0b6b616d5c2da981b4f0369c0ad347d3683a610f4be0e96c6d2b83a530349f289340d2581a490348e069140d2183a410b47e0e8ec2d1b83a33032da065840caf8195b032ae0654c0ca78194e0329a064fc0c9f0193b03272064cc1499019310325e064ac1495019270324c0648c9c2b0184e17098160f8541704d6d0fac2171b42e3083b6d076c20ed341da286a6d114d81a984353007a5e094b412958352901a460348a0e8f8151d02a3605464065b40cb08194d0328a064b40c9481925032422e1582c270383e0d04c2209026b687d61178da171843e2f85c5b1b8ae1714c0db681b6c036c22ed800daf81b5e036b612d680dab81b56036a61ed480da781b4e0369720d280da381b460368616d081d3683a61074be0e96c1d2b83a530749e0e92c1d2383a430347e068f8151e8196d032c20657c0cad81957032a60653c0ca58294a0328e065180ca18193f0327c064f40c978192e03256064a40c9182922032422e1584c270183e170780e0b8262e87c513c6ba16d443da785b4b1b68e16d0cb12e83a510f49e0e92c6d2383a430b47e0e8ee591b83a33032ba0a5443ca78294b1b28e0a50c2c9f8293b9226e0a4cc1c978292b8e24e0a48d08230983e1505c1717c2e2d85c570b8a60ed7c1dad83b57076a60ed3c1da583b47076860a97c152d82a57054a60a93c152582a47054860a8fc151d82a3705466365582ca70393e0f0bc121582c27058460707c0e0d8141701826098be1316c262b84c53076be0ed6c1dab83b530769e0ed2c1da383b43054be0a96c152b82a530549e0a92c152382a430547e0a8ec151b82a33092bc165181c9b02926090ac161382c230383e0706c0a0b80c1304e7d09ad4131f42e2f05c5d0b8b822d782dae88b4e0b69a1ad302da485b420b68216d00ad2e83a592b4aa0e944452683a498248a0e9042d1e95a35032ba0a5640caa829511129a0a5247ca2829410b27a3e4d4442f0885c098b61316825af84b5b096a616d3c35a705b4d094be0e96c252b83a530d49e3a9341d2583a490d48e1a9141d2183a410b47e168f41d1d85a370d46a0e8cc24af8295b092ae0a54c34a78194d052960a52434a381945052860a5042c9f8593d05276164dc349a829330725e0a4ac3493829230d09c171701e2c03c54078a01ad302da00ea5c074a0568d0273e83d6a098fa0f1781e2e83c5c436ba16d64adaa85b511169a16d2609a285b41114bc0e974452703a4d114980e9241d2103a41074800e8e8ad1b0195d052b20655414a88894d052923e51414a08392d1f24a22178442e03c5b078b412d7c25ad84b57096a63ad3c35a685b4b0b6923ad1c35a285b430b6820e97c1d2d83a530749e229381d2683a3f074760e8e81d1b8ea36074661257c14ad84957052a63a53c0ca68294b052923a51c0ca28294305282164fc149d8e937052660e4bc1c968292b0724e3a49414918b84e 20 1048575 8 255 11 2047 19 524287
def cc_66_3 : Nat → List (Nat × Nat) := unpackCursorV4 0xb954db5045b014faaf52a654a9ce97969659026789d65836677d56175c796e37964c975eb6158467521634a27f472304274b3da4d35b7f2f16a25998223361d54e18b4a147440de690b22c0634f00063 0x9d6f07d6306c6f05c6306c5f05c5b06c5705c5309b6f03b6307b5f03b5b0ab5703b5305b4f09b4d02b4b06b4706b4503b4306a6f08a6e06a6306a6206a5f07a5e06a5b04a5a06a5704a5606a5306a5206a4706a4606a4503a3f03a3e02a3b02a3a02a3702a3602a3302a320196f029630195f0295b01957029530194f0294b01947029430193f0293b01937029330192f0192d0292b02929019270192502923029210285f028570284f028470283f028370282f0282d02827028250281f0181709d6f07d6301c6f01c6e06c6301c6206c5f06c5e06c5b04c5a06c5704c5606c5307c5206b6f05b6306b5f05b5b06b5705b5306b4f06b4e06b4d09a6f03a6307a5f03a5b0aa5703a5306a4f06a4e0aa4d05a3f03a3b02a3703a330196f029630195f0295b01957029530194f0694e0194d019470194502943029420193f0293b01937029330192f0292b01927029230285f028570284f0284d02847028450283f028370282f028270281f0181709d6f07d6306c6f06c6e06c6308c6206c5f06c5b04c5a06c5704c5606c5306b6f05b6306b5f05b5b06b5705b5303b4f03b4e03b4d01a6f09a6307a5f0ea5b0ea5707a5305a4f05a4e02a4b02a4902a4702a4302a4202a4102a4005a3f05a3e06a3b06a3902a3705a3305a3209a3105a300196f029630195f0295b01957029530194f0694e0294b0294901947029430294202941029400193f0293b01937029330192f01927029230285f028570284f0284d02847028450283f028370282f028270281f018170cd6f07d6309c6f09c6307c5f09c5b12c5707c5301b6f01b6e0ab6301b6207b5f07b5e12b5b04b5a0eb5704b5607b5307b5209b4f05b4e1cb4b7e34a0eb477d34609b4305b420aa6f0ca6e03a630aa6207a5f03a5b0aa5a0aa5712a5603a5309a4f03a4b0aa4a0aa477c24603a4302a3f02a3e02a3d0196f029630195f0295b01957029530194f0294b01947029430193f0193d0193701935029330192f0292b029290192702923029210285f028570284f028470283f0283d02837028350282f0282d02827028250281f018170cd6f07d6309c6f09c6307c5f09c5b12c5707c530cb6f0ab6307b5f0ab5b12b5707b5309b4f0ab4b8234709b4301a6f01a6d01a6501a5f07a5e02a5b01a5702a5302a5201a4f02a4b01a4702a4301a3f02a3b01a3702a330196f0196e0196d0295f0795e0295b0295a029570495602953029520294f0594e0294b0294a029477f14602943029420293f0393e0293b0293a029377b13602933029320285f028570284f028470283f028370282f018270281f0281d028170281504e7f04e7b04e7704e7306d7f06d7e06d7b06d7706d730cd7204d6f04d6e04d6b04d6a04d6704d6604d6304d6206c7f05c7b06c7705c7304c6f04c6b04c6704c6303c5f03c5e03c5d0ab7f03b7b09b7703b7304b6f03b6b04b6703b6305b5f05b5e05b5d05b4f05b4e03b4b03b4903b4305b4203b410ab4001a7f02a7b01a7702a7301a6f04a6e01a6d01a6701a6502a6302a6201a5f01a5d02a5b02a5901a5701a5502a5302a5101a4f02a4b01a4702a4301a3f02a3b01a3702a330297f0c97e0297b0297702973029720196701966019650295f0695e0295d1d95c0295b0295a02959029580295706956029551d954029530295202951029500294f0594e0294b0294a029470694602943029420293f0393e0293b0293a029370a93602933029320292f0292e0292d0287f0287b02877028730286f0286b02867028630285f0285d0285b0285702855028530284f0284b02847028430283f0283b02837028330282f0182b01827028230281f0281d0281b02817028150281304d6f04d6b04d6704d6306c6f05c6b06c6705c6304c5f04c5b04c5704c530cb6f08b6e09b6b09b670cb6308b6204b5f04b5e04b5b04b5a04b5704b5604b5304b5203b4f03b4e02b4b02b4a02b4702b4602b4302b420aa6f03a6b09a6703a6304a5f03a5b04a5703a5302a4f03a4b06a4a06a4706a4603a4306a3706a3606a350196f0296b01967029630195f0295b01957029530194f0294b01947029430193f0193d0293b02939019370193502933029310192f0292b01927029230286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283d0283b0283702835028330282f0282b02827028230281f0181b018170281304d6f04d6b04d6704d6306c6f0cc6e09c6b06c670cc630cc6204c5f04c5e04c5b01c5a01c5701c5604c5304c5206b6f05b6b06b6705b6304b5f04b5b04b5a04b5704b5604b5302b4f02b4e02b4d0ca6f09a6b09a670aa6304a5f04a5b04a5704a531aa4f7824d06a4b03a4906a471da450aa4303a4105a3f06a3b06a3705a330196f0296b01967029630195f0295b01957029530194f0194d0294b02949019470194502943029410193f0293b029390193702933029310192f0292b01927029230286f0286b02867028630285f0285b02857028530284f0284d0284b0284702845028430283f0283b02837028330282f0282b02827028230281f0181b018170281304d6f04d6b04d6704d6306c6f05c6b06c6705c6304c5f04c5b04c5704c530ab6f03b6b09b6703b6304b5f03b5b04b5703b5305b4f0ab4d02b4b06b4706b4503b4306a6f08a6e06a6b06a6706a6306a6204a5f03a5e04a5b04a5a04a5704a5603a5303a5206a4706a4606a4503a3f03a3e02a3b02a3a02a3702a3602a3302a320196f0296b01967029630195f0295b01957029530194f0294b01947029430193f0293b01937029330192f0192d0292b02929019270192502923029210286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283b02837028330282f0282d0282b0282702825028230281f0181b018170281304d6f04d6b04d6704d630cc6f0cc6b0cc670cc6304c5f04c5b04c5704c530cb6f0cb6e0cb6b0cb670cb630cb6204b5f03b5e04b5b01b5a01b5701b5603b5303b520eb4f05b4e1cb4b7634a0eb471db4610b4305b420aa6f03a6b0aa6703a6304a5f03a5b04a5a04a5704a5603a530aa4f03a4b0aa4703a4302a3f02a3e02a3d0196f0296b01967029630195f0295b01957029530194f0294b01947029430193f0193d0293b02939019370193502933029310192f0292b029290192702923029210286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283d0283b0283702835028330282f0282b02827028230281f0181b018170281304d6f04d6b04d6704d630cc6f0cc6b0cc670cc6304c5f04c5b04c5704c530cb6f0ab6b0cb670ab6304b5f04b5b04b5704b5310b4f0ab4b793470ab4301a6f02a6b01a6702a6301a5f04a5e01a5d01a5701a5502a5302a5201a4f02a4b01a4702a4301a3f02a3b01a3702a330296f0c96e0296b0296702963029620195701956019550294f0594e0294b0294a029477714602943029420293f0393e0293b0293a029377513602933029320292f0292e0292d0286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283b02837028330282f0182b01827028230281f0281d0281b02817028150281305e7f05e7e05e7d01d7f01d7e01d7308d7201d6f01d6e01d6d01d6c01d6b09d6a01d6909d6801d6701d6601d6501d6401d6306d6201d6112d6004c7f04c7304c6f04c6d04c6b04c6904c6704c6504c6304c6101c5f01c5e02c5d05b7905b7305b7101b5f06b5d01b5b01b5901b5701b5501b5305b5104b4f04b4b04b4704b4309a7f09a7306a6f0fa6d09a6b03a6909a6709a6506a6303a6101a5f12a5d01a5b01a5901a5701a5501a5303a5104a4f04a4b04a4704a4305a3f06a3b06a3705a330197f019730196f0196d0196b01969019670196501963019610195f0195e0195d0194f0194e0194b019490194304942019410193f0193b01937019330192f0192b01927019230686f0d86d06867098650185f0885d01857018550484f048470583f058370a82f0d8270181f0181703e7f03e7e03e7d01d7f01d7e01d7308d7201d6f01d6e01d6d01d6c01d6b0fd6a01d6912d6801d6701d6601d6501d6401d6308d6201d6112d6004c7f04c7304c6f04c6d04c6b04c6904c6704c6504c6304c6101c5f01c5e02c5d09b7f09b730eb6f0fb6d09b6b05b690fb6714b6509b6305b6101b5f12b5d01b5b01b5901b5701b5501b5305b5104b4f04b4b04b4704b4303a7903a7303a7101a5f0aa5d01a5b01a5901a5701a5501a5303a5104a4f03a4b04a4703a4309a3f03a3b0aa3703a330197f019730196f0196d0196b01969019670196501963019610195f0195e0195d0194f0194e0194b019490194304942019410193f0193b01937019330192f0192b01927019230d86f0d86d0d8670d8650185f0885d01857018550484f048470983f0d8370382f038270181f0181701e7f01e7e01e7b01e7701e7312e7204d7f04d7b04d7704d7301d6f01d6e02d6d06c7f0fc7e09c7b06c771fc730fc7201c6f01c6e06c6d12c6c01c6b01c6a01c6901c6801c6701c6601c6501c6401c6301c6211c6112c6004c5f04c5e04c5b04c5a04c5704c5604c5304c5206b7f05b7b06b7705b7301b6f06b6d01b6b01b6901b6701b6501b6305b6104b5f04b5b04b5704b5303b4f03b4e03b4d0aa7f03a7b09a7703a7301a6f0aa6d01a6b01a6901a6701a6501a6303a6104a5f03a5b04a5703a5305a4f05a4e05a4d05a3f05a3e03a3b03a3903a3305a3203a310aa300197f0197b01977019730196f0196e0196d0195f0195e0195b019590195304952019510194f0194d0194b01949019470194501943019410193f0193b01937019330192f0192b01927019230d87f0287b09877028730186f0b86d0186b0186701865018630485f0285b04857028530684f0d84d0284b068470d845028430583f0283b05837028330382f0282b03827028230181f0181b018170181301d6f01d6e01d6b01d6701d6312d6204c6f04c6b04c6704c6301c5f01c5e02c5d7336f0cb6b0cb6710b6301b5f12b5d01b5b01b5901b5701b5501b5305b5104b4f04b4b04b4704b437226f0aa6b0ca670aa6301a5f12a5d01a5b01a5901a5701a5501a5303a5104a4f04a4b04a4704a4310a3f0aa3b712370aa330196f0196b01967019630195f0195e0195d0194f0194e0194b019490194304942019410193f0193b01937019330192f0192b01927019230d86f0286b0c867028630185f0d85d0185b0185701855018530484f0284b04847028430d83f0283b0d837028330a82f0282b0d827028230181f0181b01817018130cd6f07d6b09d6707d6309c6f05c6b09c6705c6307c5f05c5b10c5705c530cb6f0cb6e09b6b09b670cb630cb6207b5f07b5e12b5b04b5a0eb5704b5607b5307b5205b4f03b4e0ab4b01b4a01b4701b4603b4303b420aa6f03a6b09a6703a6307a5f03a5b0aa5703a5305a4f03a4b0aa4a0aa4710a4603a4302a3f02a3e02a3d0196f0296b01967029630195f0295b01957029530194f0294b01947029430193f0193d0293b02939019370193502933029310192f0292b029290192702923029210286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283d0283b0283702835028330282f0282b02827028230281f0181b01817028130cd6f07d6b09d6707d6309c6f05c6b09c6705c6307c5f05c5b10c5705c530cb6f09b6b09b670ab6307b5f0ab5b12b5707b5305b4f0ab4b10b4705b4301a6f02a6b01a6702a6301a5f02a5b01a5702a5301a4f05a4e01a4d01a4701a4502a4302a4201a3f02a3b02a3a01a374f23602a330296f0c96e0296b0296702963029620295f0795e0295b0295a029570495602953029520194701946019450293f0393e0293b0293a029376f13602933029320292f0292e0292d0286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283b02837028330282f0182b01827028230281f0281d0281b02817028150281304e7f07e7e04e7d04d7904d7304d7101c7f01c7e01c7308c7201c6f01c6e01c6d01c6c01c6b04c6a01c6919c6801c6701c6601c6501c6401c6304c6201c6104c6001c5f01c5e01c5b04c5a01c5904c5801c5701c5601c5304c5201c5107c5009b7f05b7304b6f04b6d04b6b05b6904b6706b6504b6304b6104b5f04b5b04b5704b5301b4f01b4e02b4d09a7f09a7304a6f04a6d04a6b03a6904a6719a6504a6303a6104a5f04a5b04a5704a5301a4f6624d01a4b01a4901a4701a4501a4303a4105a3f09a3b09a3705a330197f019730196f0196d0196b01969019670196501963019610195f0195b01957019530194f0194e0194d0193f0193e0193b019390193305932019310192f0192b0c92a0192701926019230486f0486d048670d8650485f048570184f0884d01847018450583f058370a82f0d8270181f0181708d7d09d7501c7e01c7207c6e04c6a04c6607c6206c5a06c5601b7e01b7d07b6e08b6a16b6607b6202b5a09b5605b5203b4e03b4d03b4c08a7e08a720aa6a15a6608a4e08a4d08a3e08a3d08a3c03a3908a3203a3108a300197d019750194d019450193d01935019310884d088450883d088350882d0882508d6f07d6308c6f05c6307c5f05c5b09c5705c5301b6f01b6e01b6301b6207b5f07b5e0eb5b04b5a0eb5704b5607b5307b5209b4b06b4a09b4706b4605b4308a6f08a6e03a6308a6207a5f03a5b0aa5a0aa570ea5603a5305a4f03a4b09a4703a4308a3f08a3e08a3d0196f019630195f0195b01957019530194f0194b01947019430193f0193d0193701935019330192f0192b01927019230785f088570584f058470883f0883d08837088350382f0882d03827088250181f0181708d6f07d6308c6f09c6d09c6505c6307c5f05c5b09c5705c5301b6f01b6e01b6d07b5f07b5e08b5b04b5a16b5704b5607b5307b5202b4b02b4a09b4702b4605b4308a6f08a6307a5f0aa5b16a5707a5305a4f09a4b09a4705a4308a3f6423d0aa3b03a396c2376b23508a3303a310196f0196d01965019630195f0195b01957019530194f0194b01947019430193f0193d0193701935019330192f0192b01927019230785f088570584f058470883f0b83d088370b8350882f088270181f0181703e7f03e7e03e7d09d7f07d730ed6f04d6d07d6b07d690fd6704d6507d6307d6101c7f01c7e01c7308c7201c6f01c6e01c6d01c6c01c6b0fc6a01c6914c6801c6701c6601c6501c6401c6308c6201c616446001c5f01c5e01c5b04c5a01c5701c5601c5307c5209b7f05b7309b6f06b6d05b6b05b6909b6706b6505b6305b6107b5f05b5b09b5705b5301b4f01b4e02b4d03a7903a7303a7107a5f03a5b0aa5703a5301a4f01a4e0aa4d6324c01a4b01a4901a4701a4501a4301a4203a4103a4005a3f03a3b09a3703a330197f019730196f0196d0196b01969019670196501963019610195f0195b01957019530194f0194e0194d0193f0193e0193b019390193305932019310192f0192b0a92a0192701926019230e86f0f86d0f867138650785f188570184f0884d01847018450583f058370382f038270181f0181704d6f04d6b04d6704d6309c6f05c6b09c6705c6304c5f04c5b04c5704c5320b6f08b6e09b6b09b6720b6308b6201b5f01b5e03b5b03b5a01b5701b5601b5301b5204b4f04b4e02b4b02b4a04b4702b4604b4304b420aa6f03a6b09a6703a6304a5f03a5b01a5703a5305a4f03a4b0aa4703a4307a3f07a3d01a3b01a3901a3701a3501a3301a310196f0196b01967019630195f0195b01957019530194f0194b01947019430193f0193d0193b01939019370193501933019310192f0192b0a92a0192701926019230d86f0286b09867028630485f0285b04857028530584f0284b05847028430d83f0883d0283b0d83708835028330382f0282b03827028230181f0181b018170181304e7f04e7e04e7b04e7704e730fe7204d7f04d7b04d7704d7303d6f03d6e03d6d01c7f01c7e01c7b01c7701c7316c7201c6f01c6e01c6d01c6c01c6b04c6a01c6904c6801c6701c6601c6501c6401c6304c6201c616846001c5f01c5e01c5b04c5a01c5701c5601c5304c5209b7f05b7b09b7705b7304b6f06b6d04b6b04b6904b6704b6504b6305b6104b5f04b5b04b5704b5301b4f01b4e02b4d0aa7f03a7b09a7703a7304a6f04a6e07a6d04a5f04a5e03a5b03a5903a5304a5203a5101a4f0aa4d01a4b01a4901a4701a4501a4303a4105a3f03a3b0aa3703a330197f0197b01977019730196f0196d0196b01969019670196501963019610195f0195b01957019530194f0194e0194d0193f0193e0193b019390193305932019310192f0192b0a92a0192701926019230d87f0287b09877028730486f0d86d0286b0486704865028630485f0285b04857028530184f0b84d0184b0184701845018430583f0283b05837028330382f0282b03827028230181f0181b018170181307e7e04e7d04d7904d7104c6d05c6906c6504c6108b7e08b7204b6e04b6d04b6c04b6a0eb690eb6804b6615b6519b6404b6204b6104b6004b5e04b5a04b5604b5203b4e02b4a02b4603b4209a7e09a7204a6d03a690aa6503a6109a4a09a4601a3601a350196d0196901965019610193d0193901935019310192d019250486d0b8650883d0883508d6f08d6e08d6d08c6f07c6308c5f04c5d07c5b07c5908c5704c5507c5307c5108b6f05b6308b5f06b5d05b5b03b5908b5706b5503b5303b5107b4f05b4b09b4705b4308a6f08a6d09a6501a6301a5f01a5d01a5701a5501a5307a4f03a4b0aa4703a4305a3f03a3b09a3703a330196f019630195f0195d0195b01959019570195501953019510194f0194b01947019430193f0193b01937019330192f0192b01927019230885f0885d08857088550784f088470583f058370382f038270181f0181708d6f07d6308c6f05c6307c5f05c5b09c5705c5308b6f08b6e08b6d07b5f07b5e08b5b04b5a08b5704b5607b5307b5205b4f05b4e02b4b02b4a08b4702b4605b4305b4201a6f03a6307a5f03a5b0aa5703a5305a4f03a4b09a4703a4308a3708a360aa350196f019630195f0195b01957019530194f0194b01947019430193f0193d0193b01939019370193501933019310192f0192b01927019230785f088570584f058470883f0883d08837088350382f038270181f0181703d6f03d6e03d6d09c6f07c630ec5f07c5b0ec5707c5309b6f05b6309b5f06b5d05b5b09b5706b5505b5307b4f05b4b09b4705b4309a6f0ea6d09a6501a6301a5f01a5d01a5701a5501a5307a4f0ea4b0ea4707a4303a3f02a3b09a3705a330196f019630195f0195d0195b0195701955019530194f0194b01947019430193f0193b01937019330192f0192b01927019230e85f0e8570784f188470583f058370e82f0e8270181f018176656f07d6b09d6707d6309c6f05c6b09c6705c6307c5f05c5b10c5705c531ab6f6536e09b6b09b670eb636436207b5f07b5e0eb5b04b5a1ab5704b5607b5307b5203b4f03b4e02b4b02b4a0ab4702b4605b4303b420aa6f6326e03a6b09a6703a630aa6207a5f03a5b0aa5703a5305a4f03a4b0aa4a0aa4710a4603a4301a3701a3601a350196f0196b01967019630195f0195b01957019530194f0194b01947019430193f0193d0193b01939019370193501933019310192f0192d0192b0192701925019234a06f0286b09867028630785f0285b27057028530584f0284b05847028430e83f0b83d0283b1a8370b835028330382f0282b03827028230181f0181b018170181306d6d06c5f04c5d06c5b07c5906c5704c5506c5306c5105b5705b5505b4f05b4b05b4705b4306a5f06a5d03a5b03a5906a570ba5503a5303a5107a4f03a4b0ba4703a4305a3f03a3b05a3703a3301957019550194f0194b01947019430193f0193b019330192f0192b019270192308d6f07d6306c6f6146e08c630bc6206c5f07c5e08c5b04c5a06c5704c5607c5307c5205b6f05b6305b5f05b5b05b5705b5302b4f02b4d02b4702b4502b4308a6f03a6307a5f03a5b0ba5703a5308a4f0ba4d03a4b03a4906a470ba4503a4303a4105a3f03a3b05a3703a330196f019630195f0195b01957019530194f0194d0194701945019430193f0193b01937019330192f0192b01927019230b86e028620285f028570184701846018450283f0283a02837058360282f028270181f0181a01817018166d56f07d6b09d6707d6301c6f01c6e01c6b01c6701c636a46201c5f01c5e01c5b04c5a01c5701c5601c5307c5209b6f05b6b09b6705b6307b5f05b5b10b5705b5301b4f01b4e02b4d6926f09a6b09a670aa6307a5f0aa5b6725707a5301a4f6224d01a4b01a4901a4701a4501a4303a4105a3f0aa3b10a3705a330196f0196b01967019630195f0195b01957019530194f0194e0194d0193f0193e0193b019390193305932019310192f0192b5e12a0192701926019234906f0286b09867028630785f0285b26057028530184f6004d0184b0184701845018430583f0283b05837028330a82f0282b12027028230181f0181b0181701813 20 1048575 8 255 11 2047 20 1048575
def cc_66_4 : Nat → List (Nat × Nat) := unpackCursorV4 0xbbc61b5b61ad08ba37999e35498360923608988b85a3e7f9617986170d8b6d13c678595df9956a7553e2c4ef4f4ca2545d6d3fb623c3383447f30c3828d7f20d801c34a1764d0ee880a14d0524f00052 0x4d6f04d6b04d6704d6306c6f06c6b06c6706c6304c5f03c5b04c5704c5306b6f06b6e06b6b06b6706b6316b6204b5f04b5b04b5a04b5904b5704b5604b5306b5104b4f04b4b04b4a04b4704b4603b4303b410aa6f03a6b09a6703a6304a5f03a5b04a5703a5304a4f03a4b05a4a03a4903a4806a4706a4603a4303a4105a3f05a3e05a3d0696f0696b06967069630495f0495b04957049530694f0694b06947069430693f0693b06937069330392f0692b06927039230686f0386b06867038630485f0385b04857038530684f0384b06847038430683f0383b06837038330382f0382b03827038230681f0381b06817038130ed6f09d6b09d670ed6304c6f04c6b04c6704c6304c5f03c5b04c5704c5306b6f06b6e06b6b06b6706b6316b6204b5f03b5b03b5a04b5704b5605b5303b5104b4f04b4b04b4a04b4904b4704b4604b4306b4106a6f05a6b06a6705a6304a5f03a5b03a5a03a5903a5806a5706a5605a5303a5104a4f04a4b04a4704a4303a3f03a3e03a3d0696f0696b06967069630695f0695b06957069530494f0494b04947049430693f0693b06937069330592f0692b06927059230686f0386b06867038630685f0385b06857038530484f0384b04847038430683f0383b06837038330582f0382b05827038230681f0381b068170381304e7f04e7e04e7b04e7704e739f67204d7f04d7b04d7704d7304d6f04d6e04d6d06c7f06c7e06c7b09c7a06c7706c7606c7316c7204c6f04c6e06c6d07c6c04c5f04c5e04c5b04c5a04c5904c5804c5304c5206c5107c5006b7f05b7b06b7705b7304b6f04b6e06b6d9e36c04b5f04b5b04b5704b5303b4f03b4e03b4d0aa7f03a7b09a7703a7304a6f04a6e0aa6d9d26c04a5f03a5b04a5703a5305a4f05a4e05a4d05a3f05a3e03a3b03a3903a3305a3203a310aa300697f0697b06977069730496f0196d0496b02969049670196504963029610495f0495b04957049530694f0694d0694b06949069470694506943069410593f0693b06937059330392f0692b06927039230687f0387b06877038730486f0686d0386b0486704865038630485f0385b04857038530684f0684d0384b03849068470684503843038410583f0383b05837038330382f0382b03827038230681f0381b068170381311e7f07e7b09e7707e7306d7f06d7e06d7b09d7a06d7706d7606d730fd7206d6f06d6e06d6b11d6a06d6706d6606d6307d6201c7f06c7e01c7b01c7701c7301c7201c6f06c6e01c6b01c6a01c6704c6601c6301c6201c5f02c5e01c5d02c5c06b7f05b7b06b7705b7306b6f05b6b06b6705b6303b5f03b5e03b5d01b4f01b4d01b4b02b4901b4703b4501b4301b410aa7f03a7b09a7703a7307a6f03a6b0aa6703a6305a5f05a5e05a5d01a4f01a4d01a4b02a4901a4705a4501a4301a4105a3f05a3e03a3b03a3903a3305a3203a310aa300197f0197e0197b0197701973069720196f0196b01967019630195b0695a019599a1580195701956019550195401953019510194701946019450193f0193b0693a0193701936019330192f0192b0692a0192701926019230687f0287b06877028730686f0286b06867028630685f0685d0285b02859068570685502853028510184f0184d0184b0184706845018430583f0283b05837028330382f0282b03827028230181f0181b01817018130cd6f07d6b09d6707d6301c6f01c6b01c6701c6301c5f01c5b01c5701c5306b6f05b6b06b6705b6306b5f05b5b06b5705b5301b4f01b4b01b4701b430aa6f03a6b09a6703a6307a5f03a5b0aa5703a5301a4f01a4b01a4701a4305a3f03a3b01a3703a330296f0c96e0296b0296702963029620295f0295b029570295301947019460294592144029370693602935029270a926029250286f0286b02867028630285f0285b02857028530184f0184b01847018430283f0283b02837028330282f0282b02827028230281f0281b02817028130cd6f07d6b09d6707d6306c6f06c6b06c6706c6306c5f06c5b06c5706c5306b6f06b6b06b6706b6306b5f06b5b06b5706b5303b4f03b4e02b4b02b4901b4702b4302b410aa6f03a6b09a6703a6307a5f03a5b0aa5703a5305a4f05a4e05a4d06a3f06a3e03a3b03a3901a3703a3305a3203a3103a300196f0296b01967029630195f0295b01957029530194f0694e0294b0294901947029430294202941029400193f0293b01937029330192f0292b01927029230286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283b02837028330282f0282b02827028230281f0181b01817028130cd6f07d6b09d6707d6306c6f06c6b06c6706c6306c5f06c5b06c5706c5306b6f05b6b06b6705b6306b5f05b5b06b5705b5303b4f03b4e03b4d0ca6f09a6b09a670ca6307a5f0ea5b0ea5707a5305a4f03a4e02a4b02a4901a4702a4302a4105a3f03a3e06a3b06a3901a3703a3303a3203a3103a300196f0296b01967029630195f0295b01957029530194f0694e0294b0294901947029430294202941029400193f0293b01937029330192f0292b01927029230286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283b02837028330282f0282b02827028230281f0181b01817028130ce7f07e7b09e7707e7306d7f06d7e06d7b09d7a06d7706d7606d730cd7206d6f06d6e06d6b12d6a06d6706d6606d6307d6206c7f05c7b06c7705c7306c6f05c6b06c6705c6303c5f03c5e03c5d0ab7f03b7b09b7703b7307b6f03b6b0ab6703b6305b5f05b5e05b5d05b4f05b4e03b4b03b4903b4305b4203b410ab4001a7f02a7b01a7702a7301a6f02a6b01a6702a6301a5f06a5e01a5d9a25c01a5701a5502a5302a5202a5102a5001a4f02a4b01a4702a4301a3f02a3b01a3702a330297f0c97e0297b0297702973029720296f0796e0296b0296a029670496602963029620195701956019550195402947069460294599144029370a93602935981340292f0292e0292d0287f0287b02877028730286f0286b02867028630285f0285d0285b02859028570285502853028510284f0284b02847028430283f0283b02837028330282f0182b01827028230281f0281d0281b02817028150281307e7907e7106d7e06d7d06d7c06d7506d7408d7206d6e11d6a06d6607d6206c7d06c7503c5e03c5d01b7e01b7d07b6e04b6a04b6607b6202b5a02b5902b5806b5606b5506b5406b5208b5108b5006b4a06b460aa7d09a7505a5e05a5d05a4e03a4905a4203a4109a400aa3d09a350197d019750195e0195d0195c019590195506952019510c9500193d0193502879028710685d068550683d0683515d6f07d6b09d6707d6306c6f06c6e06c6b06c6706c630fc6206c5f06c5b06c5706c530ab6f03b6b09b6703b6307b5f03b5b0ab5703b5305b4f05b4e05b4d06a6f06a6b06a6706a6306a5f06a5b06a5706a5301a4f01a4d01a4b01a4701a4503a4303a4203a3f03a3e05a3d03a3c01a3b06a3706a3503a3303a320196f0196b01967019630195f0195b01957019530194f0194e0194d0194b019470194501943069420193f0193b01937019330192f0192b01927019230686f0286b06867028630685f0285b06857028530684f0284b06847028430383f0283b03837028330682f0282b06827028230181f0181b018170181315d6f07d6b09d6707d6306c6f06c6e06c6b06c6706c630fc6206c5f06c5b06c5706c5306b6f05b6b06b6705b6306b5f05b5b06b5705b5303b4f03b4e03b4d0ea6f09a6b09a670ea6307a5f0ea5b0ea5707a5301a4f01a4d01a4b01a4701a4505a4303a4203a3f03a3e03a3d03a3c01a3b06a3706a3505a3303a320196f0196b01967019630195f0195b01957019530194f0194e0194d0194b019470194501943069420193f0193b01937019330192f0192b01927019230686f0286b06867028630685f0285b06857028530684f0284b06847028430583f0283b05837028330682f0282b06827028230181f0181b018170181315e7f07e7b09e7707e7301d7f01d7e01d7b01d7701d739657201d6f01d6e01d6b04d6a01d6701d6601d6307d6206c7f06c7e06c7b09c7a06c7706c7606c730fc7206c6f06c6e06c6b1ec6a06c6706c6606c6307c6201c5f01c5e02c5d02c5c06b7f05b7b06b7705b7306b6f05b6b06b6705b6301b5f01b5e06b5d9535c03b4f03b4e03b4d0aa7f03a7b09a7703a7307a6f03a6b0aa6703a6301a5f01a5e0aa5d9425c05a4f05a4e05a4d05a3f05a3e03a3b03a3903a3305a3203a310aa300197f0197b01977019730196f0196b01967019630195f0195e0195d0194f0194e0194d0194c0194b01949019430694201941911400193f0193b01937019330192f0192b01927019230687f0287b06877028730686f0286b06867028630185f0685d0185b0185701855018530684f0684d0284b02849068470684502843028410583f0283b05837028330382f0282b03827028230181f0181b01817018130cc5f07c5b09c5707c5306b5f06b5b06b5706b5306b4f06b4b06b4706b4306a5f05a5b06a5705a5306a4f05a4b06a4705a4301a3f01a3b02a3701a330a95f0395b09957039530794f0394b0a947039430193f0193b02937019330592f0392b01927039230285f0285b02857028530284f0284b02847028430283f0283b02837028330282f0282b02827028230281f0281b02817028130cd6f07d6b09d6707d6301c6f01c6e01c6b01c6701c630cc6201c5f01c5b01c5701c5306b6f05b6b06b6705b6306b5f05b5b06b5705b5301b4f01b4e06b4d0aa6f03a6b09a6703a6307a5f03a5b0aa5703a5301a4f01a4e0aa4d05a3f05a3e03a3b03a3901a3703a3305a3203a310aa300296f0296b02967029630295f0295b02957029530194f0194e0294d9214c0193f0293b01937019330192f0292b01927019230286f0286b02867028630285f0285b02857028530184f0184b01847018430283f0283b02837028330282f0282b02827028230281f0281b02817028130ce7f07e7b09e7707e7306d7f06d7e06d7b09d7a06d7706d7606d730cd7206d6f06d6e06d6b11d6a06d6706d6606d6307d6206c7f05c7b06c7705c7306c6f05c6b06c6705c6303c5f03c5e03c5d0ab7f03b7b09b7703b7307b6f03b6b0ab6703b6305b5f05b5e05b5d05b4f05b4e03b4b03b4903b4305b4203b410ab4001a7f0ca7e02a7b01a7702a7302a7201a6f02a6b01a6702a6301a5f01a5d02a5b02a5a02a5902a5801a5706a5601a559125401a4f02a4b02a4a01a4706a4602a4301a3f02a3b02a3a01a370aa3602a330297f0c97e0297b0297702973029720296f0796e0296b0296a029670496602963029620195f0195e0195d0195c0194f0194e0294b0294a029470394602943029420193f0193e0293b0293a029370593602933029320292f0292e0292d0287f0287b02877028730286f0286b02867028630285f0285d0285b02859028570285502853028510284f0284b02847028430283f0283b02837028330282f0182b01827028230281f0281d0281b0281702815028130de7f07e7306d7f06d7e06d7308d7206d6f06d6e06d6b0dd6a06d6706d6606d6307d6206c7f06c7e06c730bc7206c6f06c6e06c6b04c6a06c6704c6606c6307c6205b7f05b7305b6f05b6b05b6705b6303b5f03b5e03b5d03b4f03b4d03b4703b4503b4303b4103a7f03a7303a6f03a6b03a6703a6303a5f05a5e03a5d03a4f03a4d03a4703a4503a4303a4103a3f05a3e03a3b03a3903a3303a3203a3103a300697f029730696f0296b06967029630695f0695d0295b02959069570695502953029510694f0194d0294b02949069470194502943029410593f0293b05937029330392f0292b03927029230b87e038720386f038670385a038580385706856038550b8540384706846038450383f0383a03837058360382f0382a03827038260281f0281706d6d06c5f04c5d06c5b07c5906c5704c5506c5306c5105b5705b5505b4f05b4b05b4705b4303a5703a5503a4f03a4b03a4703a4303a3f03a3b03a330695f0195d0295b02959069570195502953029510694f0294b06947029430593f0293b05937029330392f0292b039270292308d6f07d6306c6f8e46e08c630bc6206c5f07c5e08c5b04c5a06c5704c5607c5307c5205b6f05b6305b5f05b5b05b5705b5303b4f03b4d03b4703b4503b4303a6f03a6303a5f03a5b03a5703a5303a4f03a4d03a4703a4503a4303a3f03a3b03a3703a330896f029630795f0295b0d957029530694f0194d0294b02949069470194502943029410593f0293b05937029330392f0292b03927029230b86e038620385f03857038470b846038450383f0383a03837058360382f0382a03827038260281f0281707e7106d7d06d7c06d6e0dd6a06d6607d6205c7d03c5e03c5d06b7d07b6e04b6a04b6607b6203b4a03a7d05a5e03a5d05a4e03a4903a4203a4103a4003a3d029710695d0295906955029510193d0293901935029310b8660685e0885c0de7f07e7306d7f06d7e06d738c57206d6f06d6e06d6b04d6a06d6704d6606d6307d6206c7f06c7e06c7308c7206c6f06c6e06c6b0dc6a06c6706c6606c6307c6205b7f05b7305b6f05b6b05b6705b6303b5f03b5e03b5d03b5c03b4f03b4e03b4d03a7f03a7303a6f03a6b03a6703a6303a5f05a5e03a5d05a5c03a4f05a4e03a4d03a3f05a3e03a3b03a3903a3303a3203a3103a300697f029730696f0296b06967029630695f0195d0295b02959069570195502953029510694f0694d0294b02949069470694502943029410593f0293b05937029330392f0292b03927029230386f0386a038670b8660385f0685e0385d0384f0684e0384d0b84c03842038400383f038370382f038270281f02817a656f07d6b09d6707d63a546fa446e09c6b09c67a3463a146207c5f07c5ea045b04c5a9c45704c5607c5307c5209b6f05b6b09b6705b6307b5f05b5b10b5705b5303b4f03b4e03b4d0aa6f03a6b09a6703a6307a5f03a5b0aa5703a5305a4f05a4e05a4d05a3f05a3e03a3b03a3903a3305a3203a310aa308516f0996b09967821630795f7915b71157079539b14f0194d9714b02949931470194590143029410593f1093b10937059330392f0a92b0a927039234b06f0386b09867038630785f0385b2e057038538f04f8d04d0384b8b04714045038430583f0383b05837038330382f0382b03827038230e01f0381b040170381302e7e01e7d08d7e08d7201d6e01d6d01d6c01d6a0cd690cd6801d660cd650cd6401d6201d6101d6001c6d04c6904c6501c6104c5d03c5904c5503c5101b6d05b6906b6501b6106b5d03b5906b5503b5109a7e09a7201a6d03a690aa6501a6104a5604a5504a4a04a4606a3a06a3601979019710195d0195901955019510194e049420186d0b8650885d0885501e7f02e7e01e7d04d7f04d7e04d7308d7201d6f01d6e01d6d01d6c01d6b01d6a04d690cd6801d6701d6604d6504d6401d6301d6201d6101d6004c7f04c7301c6f01c6d01c6b04c6901c6704c6501c6301c6104c5f04c5e04c5d06b7f05b7301b6f01b6d01b6b05b6901b6706b6501b6301b6104b5f04b5e07b5d04b4f04b4e04b4b04b4904b4304b4205b4109a7f09a7301a6f01a6d01a6b03a6901a670ca6501a6301a6104a5f8925d04a5b03a5904a5704a5504a5303a5104a4f04a4b04a4704a4305a3f06a3b06a3705a330197901973019710195f0195e0195d0195c0195b019590195701955019530495201951029500194f0194e0194b0194701943049420193f0193b01937019330192f0192b01927019230186f0186d018670c8650485f0885d04857048550484f048470583f058370a82f0d8270181f0181702e7e01e7d01d6d04d6904d6501d6108c7e06c7201c6e01c6d01c6c01c6a06c6906c6801c6606c650cc6401c6201c6101c6004c5e03c5a03c5604c5206b7e09b7201b6d05b6906b6501b6104b5a04b5604b4604b4501a6d03a690aa6501a6106a4d03a4907a4503a4109a3d06a3501979019710195e049520194d0194901945019410186d068650684d0684501e7f02e7e01e7d04d7f04d7e04d7308d7201d6f01d6e01d6d01d6c01d6b01d6a04d690cd6801d6701d6604d6504d6401d6301d6201d6101d6004c7f04c7301c6f01c6d01c6b04c6901c6704c6501c6301c6103c5f03c5e03c5d09b7f09b7301b6f01b6d01b6b05b6901b670cb6501b6301b6104b5f8735d04b5b04b5904b5704b5504b5305b5104b4f04b4b04b4704b430aa7f03a7301a6f01a6d01a6b03a6901a670aa6501a6301a6104a5f04a5e07a5d04a4f04a4e03a4b03a4903a4304a4203a4109a3f03a3b0aa3703a330197901973019710195f0195e0195d0195c0195b019590195701955019530495201951029500194f0194e0194b0194701943049420193f0193b01937019330192f0192b01927019230186f0186d018670b8650485f0885d04857048550484f048470983f0d8370382f038270181f0181701e7f02e7e01e7d09d7f07d7301d6f01d6d01d6b07d6901d6704d6501d6301d6106c7f08c7e09c7308c7201c6f01c6e01c6d01c6c01c6b01c6a0cc690cc6801c6701c6606c650cc6401c6301c6201c6101c6006c5f07c5e11c5b04c5a06c5704c5607c5307c5206b7f05b7301b6f01b6d01b6b05b6901b6706b6501b6301b6106b5f05b5b06b5705b5303b4f03b4e03b4d09a7f03a7301a6f01a6d01a6b03a6901a670aa6501a6301a6107a5f03a5b0aa5703a5305a4f05a4e05a4d05a3f05a3e03a3b03a3903a3305a3203a3109a300197901973019710195f0195e0195b0195701953079520194f0194e0194d0194c0194b019490194701945019430c94201941029400193f0193b01937019330192f0192b01927019230186f0186d018670b8650785f2b0570684f0884d06847088450583f058370382f038270181f0181701d6f02d6e01d6d0cc6f07c6301c5f01c5d01c5b07c5901c5704c5501c5301c5109b6f09b6301b5f01b5d01b5b05b5901b570cb5501b5301b5107b4f09b4b8834707b430ca6f0aa6301a5f01a5d01a5b03a5901a570ca5501a5301a5107a4f0aa4b8624707a4309a3f0aa3b8523709a330196901963019610194f0194e0194b0194701943079420193f0193b01937019330192f0192b01927019230185f0185d018570c8550784f2a0470983f1c0370a82f130270181f0181709d6f07d6306c6f01c6e01c6301c6206c5f06c5e06c5b04c5a06c5704c5606c5307c5206b6f05b6306b5f05b5b06b5705b5303b4f03b4d02b4b02b4902b4702b4502b4302b4109a6f03a6307a5f03a5b0aa5703a5305a4f05a4d02a4b02a4902a4702a4502a4302a4105a3f03a3b02a3703a330196f029630195f0295b01957029530194f0194d0294b01947019450193f0293b01937029330192f0292b01927029230285f028570284f0284d02847028450283f028370282f028270281f0181709e7f07e7306d7f06d7e06d7308d7206d6f06d6e06d6b04d6a06d6704d6606d6307d6206c7f05c7306c6f05c6b06c6705c6303c5f03c5e03c5d09b7f03b7307b6f03b6b0ab6703b6305b5f05b5e05b5d05b4f05b4e03b4b03b4903b4305b4203b4109b4001a7f01a7d01a7501a6f07a6e02a6b01a6702a6302a6201a5f06a5e01a5d01a5c02a5b02a5901a5701a5502a5302a5202a5102a5001a4f02a4b01a4702a4301a3f02a3b01a3702a330197f0197e0197d0296f0796e0296b0296a029670496602963029620295f0695e0295d8315c0295b0295a02959029580295706956029557d154029530295202951029500294f0594e0294d0594c0294b0294a0294706946029458014402943029420293f0393e0293d0393c0293b0293a029370a936029357c13402933029320286f028670285f0285d02857028550284f028470283f028370282f018270281f0281d028170281509d6f07d6306c6f05c6306c5f05c5b06c5705c5309b6f08b6e09b6308b6207b5f07b5e0eb5b04b5a0eb5704b5607b5307b5203b4f03b4e02b4b02b4a02b4702b4602b4302b4209a6f03a6307a5f03a5b0aa5703a5302a4f03a4b06a4a06a4706a4603a4306a3706a3606a350196f029630195f0295b01957029530194f0294b01947029430193f0193d0293b02939019370193502933029310192f0292b01927029230285f028570284f028470283f0283d02837028350282f028270281f0181709d6f07d6306c6f06c6e06c6308c6206c5f06c5b04c5a06c5704c5606c5301b6f06b6306b5f06b5b06b5706b5303b4f03b4e02b4b02b4902b4702b4302b4202b4102b4009a6f03a6307a5f03a5b0aa5703a5305a4f05a4e05a4d06a3f06a3e03a3b03a3902a3703a3306a3203a3103a300196f029630195f0295b01957029530194f0694e0294b0294901947029430294202941029400193f01937029330192f0292b01927029230285f028570284f0284d02847028450283f028370282f028270281f0181709d6f07d6301c6f01c6e09c6301c6206c5f07c5e12c5b04c5a06c5704c5607c5307c5206b6f09b6e05b6309b6206b5f05b5b09b5a06b5712b5605b5302b4f02b4e02b4d09a6f09a6307a5f0aa5b12a5707a531aa4f8124d06a4b03a4906a477d2450aa4303a4105a3f09a3d06a3b06a378023505a330196f029630195f0295b01957029530194f0194d0194701945029430193f0293b029390193702933029310192f0292b01927029230285f028570284f0284d02847028450283f0283d02837028350282f028270281f01817 20 1048575 8 255 11 2047 20 1048575
def cc_66_5 : Nat → List (Nat × Nat) := unpackCursorV4 0x96b48923488f3308a84b85b4d80d4e7a469743616f94a6b5446387d5f0485c0305754b5284d4ab7d45d4e4134a3cf4436669305612877e21c6b1d74516473124400d74d03e990003e 0x4d6f07d6e04d6d04c6904c6304c6109b6f09b6304b5f04b5d04b5b05b5904b5719b5504b5304b5104b4f04b4b04b4704b4314a6f0aa6304a5f04a5d04a5b03a5904a5719a5504a5303a5104a4f04a4b04a4704a4309a3f0aa3ba623709a330c96f0c9630495f0195d0495b02959049570195504953029510494f0494b04947049430993f0c93b6d137099330a92f0c92b5b1270a9230485f0485d048570d8550484f048470983f0d8370a82f0d8270c81f0d81705d6f05d6e05d6d09c6f07c6309c5f04c5d07c5b07c5909c5704c5507c5307c5105b6905b6305b6107b4f05b4b09b4705b4309a6f09a6309a5fa425d09a5b03a5909a5709a5509a5303a5107a4f0aa4bac24707a4305a3f09a3b09a3705a330996f099630995f0195d0995b02959099570195509953029510794f0c94b73147079430593f0993b09937059330a92f0c92b5a1270a9230985f1e05d09857098550784f3d0470583f058370a82f170270c81f0601704e7d04e7504d7e04d7204d6a04d6604c7e04c7d04c6a04c6604c6203c5e03c5d03c5c08b7d09b7506b5d06b5507b4d07b4505b4108a7e08a7208a5e08a5d08a4e08a4d08a4c03a4908a4203a4108a400195d0295901955029510894d0c9490f945089410a92d0f9250885d088550884d088450882d0882504d6f04d6304c6f04c6e04c6304c6204c5b04c5a04c5704c5604c5308b6f05b6304b5f04b5b04b5704b5309b4f06b4d09b4706b4505b4308a6f08a6e03a6308a6204a5f03a5b04a5703a5308a4f08a4e08a4d05a3f03a3b09a3703a330896f089630495f0495b04957049530e94f0194d0c94b029490e947019450c943029410593f0993b09937059330392f0a92d0a92b0a9270e925039230485f048570884f0884d08847088450583f058370382f0882d03827088250881f0881704d6f04d6d04d6504d6304c6f04c6e04c6d04c5b04c5a04c5704c5604c5308b6f09b6d09b6505b6304b5f04b5b04b5704b5307b4f07b4d07b4707b4505b4308a6f08a6304a5f04a5b04a5704a5308a4fb324d0aa4b03a49b9247b824508a4303a4105a3f09a3b09a3705a330896f089630495f0495b04957049530894f0194d0c94b029490f9470194508943029410593f0993b09937059330a92f0c92b0f9270a9230485f048570884f0b84d088470b8450583f058370882f088270881f0881708d6f08d6e08d6d04c6f04c6304c5f04c5d04c5b03c5904c5704c5503c5303c5108b6f05b6308b5f06b5d05b5b03b5908b5706b5503b5303b5104b4f04b4b04b4704b4308a6f08a6d09a6503a6304a5f04a5d04a5704a5503a5304a4f03a4b04a4703a4305a3f03a3b09a3703a330896f089630895f0195d0895b02959089570195508953029510494f0494b04947049430593f0993b09937059330392f0a92b0a927039230885f0885d08857088550484f048470583f058370382f038270881f088171ad6fb656e09d6b09d670ed63b356204c6f04c6b04c6704c6304c5f04c5d03c5b03c5904c5704c5504c5303c5109b6f05b6b09b6705b6307b5f07b5d03b5b03b5907b5707b5505b5303b5104b4f04b4b04b4704b430aa6fb226e03a6b09a6703a630aa6204a5704a5604a5504a4f03a4b04a4a04a4704a4603a4305a3f03a3b0aa3a0aa3710a3603a338916f0996b099670e9630e95f0195d0e95b029590e957019550e953029510494f0494b04947049430593f0e93b10937059330392f0a92b0a927039230d86f0386b09867038630d85f0b85d0385b0d8570b855038530484f0384b04847038430583f0383b05837038330382f0382b03827038230d81f0381b0d8170381304d6f04d6e04d6b04d6704d63b756204c6f04c6b04c6704c6304c5f04c5e04c5d09b6f05b6b09b6705b6304b5f04b5e07b5d04b4f04b4e04b4b04b4904b4304b4205b41b126f09a6b09a670aa6304a5fb525d04a5b03a5904a5704a5504a5303a5104a4f04a4b04a4704a4305a3f0aa3b10a3705a338816f0996b09967129630495f0195d0495b02959049570195504953029510494f0494b04947049430593f1093b10937059330a92f1292b581270a9230d86f0586b09867058630485f0d85d0485b0485704855048530484f0484b04847048430583f0583b05837058330a82f0582b0d827058230d81f0581b0d8170581304d6f04d6308c6f08c6e08c6d04c5f04c5e04c5b04c5a04c5704c5604c5304c5208b6f05b6304b5f04b5b04b5704b5307b4f06b4d05b4b05b4907b4706b4505b4305b4104a6f03a6304a5f03a5b04a5703a5308a4708a460aa4505a3f03a3b09a3703a330896f089630495f0495b04957049530894f0194d0894b02949089470194508943029410593f0993b09937059330392f0a92b0a927039230485f048570884f0884d08847088450583f058370382f038270881f0881703d6f03d6e03d6d09c6f0ec6d09c6504c6304c5f04c5d04c5704c5504c5304b6f04b6304b5f04b5d04b5b04b5704b5504b5304b4f03b4b04b4704b4309a6f05a6309a5f06a5d05a5b09a5706a5505a5307a4f03a4b07a4705a4304a3f04a3b04a3704a330996f099630e95f0c95b0e9570c9530e94f0c94b0e9470c9430493f0493b04937049330592f0992b09927059230d85f0d8570d84f0d8470483f048370582f058270c81f0d81703e7f03e7e03e7d04d7f04d7e04d7308d7204d6f04d6e04d6d04d6c04d6b11d6a04d6914d6804d6704d6604d6504d6404d6308d6204d61b356004c7f04c7304c6f04c6d04c6b04c6904c6704c6504c6304c6104c5f04c5e04c5d09b7f05b7309b6f06b6d05b6b05b6909b6706b6505b6305b6104b5f04b5e07b5d04b4f04b4e04b4b04b4904b4304b4205b4103a7903a7303a7104a5f04a5e0aa5db225c03a5b03a5904a5704a5503a5304a5203a5103a5004a4f03a4b04a4703a4305a3f03a3b09a3703a330997f099731496f0196d0c96b0296911967019650c963029610495f0195d0495b02959049570195504953029510494f0494b04947049430593f0993b09937059330392f0a92b0a927039230d86f0d86d0d8670d8650485f0885d04857048550484f048470583f058370382f038270c81f0d81703d6f03d6e03d6d14c6f07c6314c5f04c5d07c5b07c5914c5704c5507c5307c5109b6f09b6314b5fa435d09b5b05b5914b5714b5509b5305b5107b4f09b4bb134707b4303a6903a6303a6107a4f03a4b0aa4703a4309a3f03a3b0aa3703a330c96f0c9631495f0195d0c95b0295914957019550c953029510794f0c94b72147079430993f0c93b69137099330392f0a92b0a927039231485f1605d14857148550784f380470983f1d0370382f038270c81f0501704e7d04e7504d7e04d7204d6a04d6604c7e04c7d03c6a04c6604c6205c5e05c5d05c5c08b7e08b7208b5e08b5d08b4e06b4d06b4c05b4908b4205b4108b4008a7d09a750aa5d09a5507a4d07a4503a410195d0295901955029510894d069490f945069410993d0f9350885d088550884d088450883d0883504d6f04d6304c6f04c6e04c6304c6204c5b04c5a04c5704c5604c5306b6f06b6e05b6308b6204b5f04b5b04b5704b5306b4f06b4e06b4d08a6f03a6304a5f03a5b04a5703a5306a4f0aa4d06a4706a4503a4305a3f03a3b06a3703a330696f069630495f0495b04957049530694f0194d0694b02949069470194506943029410593f0693d0693b0693706935059330392f0692b06927039230485f048570684f0684d06847068450583f0683d05837068350382f038270681f0681704d6f04d6d04d6504d6304c6f04c6e04c6d03c5b03c5a04c5703c5604c5308b6f08b6304b5f04b5b04b5704b5308b4faa34d09b4b05b49af347ae34508b4305b4108a6f0aa6d0aa6503a6304a5f03a5b04a5703a5307a4f07a4d07a4707a4503a4309a3f03a3b0aa3703a330896f089630495f0495b04957049530894f0194d0c94b029490f9470194508943029410993f0c93b0f937099330392f0a92b0a927039230485f048570884f0b84d088470b8450883f088370382f038270881f0881705e7f05e7e05e7d04d7f04d7e04d7308d7204d6f04d6e04d6d04d6c04d6b09d6a04d6909d6804d6704d6604d6504d6404d6306d6204d61aa56004c7f04c7304c6f04c6d04c6b04c6904c6704c6504c6304c6103c5f03c5e03c5d05b7905b7305b7104b5f04b5e06b5da935c04b5b04b5904b5704b5504b5304b5205b5105b5004b4f04b4b04b4704b4309a7f03a7309a6f0aa6d03a6b03a6909a6709a6503a6303a6104a5f04a5e07a5d04a4f04a4e03a4b03a4903a4304a4203a4105a3f03a3b09a3703a330997f099730996f0196d0996b02969099670196509963029610495f0195d0495b02959049570195504953029510494f0494b04947049430593f0993b09937059330392f0a92b0a927039230986f0b86d09867098650485f0885d04857048550484f048470583f058370382f038270c81f0d81706d6f06d6e06d6d04c6f04c6304c5f04c5d04c5b04c5904c5704c5504c5304c5106b6f06b6d06b6504b6304b5f04b5d04b5704b5504b5304b4f04b4b04b4704b4308a6f03a6308a5f08a5d03a5b03a5908a570aa5503a5303a5104a4f03a4b04a4703a4305a3f03a3b06a3703a330896f069630895f0195d0695b02959089570195506953029510494f0494b04947049430593f0693b06937059330392f0692b0a927039230885f0885d08857088550484f048470583f058370382f038270681f0681704d6f04d6306c6f08c6e06c6d04c5f04c5e03c5b03c5a04c5703c5604c5304c5204b6f05b6304b5f04b5b04b5704b5306b4706b4606b4508a6f03a6304a5f03a5b04a5703a5306a4f06a4d03a4b03a4906a4707a4503a4303a4105a3f03a3b06a3703a330696f069630495f0495b04957049530694f0194d0694b02949069470194506943029410593f0693b06937059330392f0692b06927039230485f048570684f0684d06847068450583f058370382f038270681f0681705d6f05d6e05d6d04c6f04c6304c5f04c5d04c5b04c5704c5504c5306b6f06b6d06b6504b6304b5f04b5d04b5704b5504b5304b4f03b4b04b4704b4309a6f03a6306a5f06a5d03a5b06a5709a5503a5304a4f03a4b04a4703a4306a3f03a3b06a3703a330696f069630695f0695b06957069530494f0494b04947049430693f0693b06937069330392f0692b06927039230685f068570484f048470683f068370382f038270681f0681704d6f04d6b04d6704d6322c6fab46e06c6b09c6706c63aa46204c5f04c5e03c5b03c5a04c5703c5604c5304c5206b6fa936e05b6b06b6705b6310b6204b5f04b5b04b5a04b5704b5604b5304b4704b4604b450aa6f03a6b09a6703a6304a5f03a5b04a5703a5306a4f07a4d03a4b03a4907a4707a4503a4303a4105a3f0aa3d03a3b06a370aa3503a338716f0696b09967069630495f0495b04957049530694f0194d0694b02949069470194506943029410593f0693b06937059330392f0692b0a927039230d86f0386b09867038630485f0385b04857038530684f0b84d0384b068470b845038430583f0383b05837038330382f0382b03827038230681f0381b068170381304d6f04d6e04d6b04d6704d63ad56204c6f04c6b04c6704c6303c5f03c5e03c5dac36f10b6b14b6710b6304b5fa835d04b5b04b5904b5704b5504b5305b5104b4f04b4b04b4704b430aa6f03a6b0aa6703a6304a5f04a5e07a5d04a4f04a4e03a4b03a4903a4304a4203a410aa3f03a3b0aa3703a338616f1296b14967129630495f0195d0495b02959049570195504953029510494f0494b04947049431093f1293b67137109330392f0a92b0a927039230d86f0386b0d867038630485f0d85d0385b0485704855038530484f0384b04847038430d83f0383b0d837038330382f0382b03827038230d81f0381b0d8170381304e7f07e7e04e7d04d7904d7304d7109c7f08c7e09c7308c7204c6f04c6e04c6d04c6c04c6b04c6a11c6919c6804c6704c6606c6519c6404c6304c6204c6104c6004c5f04c5e04c5b04c5a04c5904c5804c5704c5604c5304c5207c5107c5009b7f05b7304b6f04b6d04b6b05b6904b6706b6504b6304b6104b5f04b5b04b5704b5303b4f03b4e03b4d09a7f03a7304a6f04a6d03a6b03a6904a670aa6503a6303a6104a5f03a5b04a5703a5305a4f05a4e05a4d05a3f05a3e03a3b03a3903a3305a3203a3109a300997f099730496f0196d0496b02969049670196504963029610495f0495b04957049531194f0194d0c94b0294915947019450c943029410593f0993b09937059330392f0a92b0a927039230486f0486d048670b8650485f048570d84f0884d0d847088450583f058370382f038270c81f0d81706e7f09e7e06e7d09d7f07d7306d6f04d6d06d6b07d6906d6704d6506d6306d6106c7909c7806c7308c7206c71a247006c5f06c5e06c5b11c5a06c5706c5606c5307c5206b7f05b7306b6706b6606b6514b6406b5f05b5b06b5705b5303b4f03b4e03b4d09a7f03a7306a6706a6609a6509a6407a5f03a5b0aa5703a5305a4f05a4e05a4d05a3f05a3e03a3b03a3903a3305a3203a3109a300697f069730696f0196d0696b02969069670196506963029610695f0695b06957069530694f0694d0694b06949069470694506943069410593f0693b06937059330392f0692b06927039230686f0686d06867068650685f068570684f0684d06847068450583f058370382f038270681f0681708d6f09d6ea256d08c6f07c6306c5f04c5d07c5b07c5911c5704c5506c5307c5106b6f05b6306b5714b5609b5506b4f05b4b06b4705b4308a6f03a6309a5709a5609a5507a4f03a4b0aa4703a4305a3f03a3b06a3703a330896f069630695f0195d0695b02959069570195506953029510794f0694b0f947069430593f0693b06937059330392f0692b0a927039230685f0b85d068570b8550784f088470583f058370382f038270681f0681709e7f07e7306d7f08d7e06d7da257c06d7509d7406d6f07d6e11d6b11d6a06d6716d6607d6307d6206c7f06c7d06c7505c7306c6f05c6b06c6705c6303c5f03c5e03c5d06b7f06b7e06b7d07b6f07b6e11b6b04b6a11b6704b6607b6307b6203b4b03b4a06b4703b4605b4305b4209a7f0aa7d09a7503a7307a6f03a6b0aa6703a6305a5f05a5e05a5d05a4f05a4e03a4b03a4903a4305a4203a4109a4005a3f05a3d09a3705a3503a3303a310997f069730796f0696b1f967069630695f0f95d0695b0c959069570f955069530c9510594f0694b06947059431193f0193d0693b02939119370193506933029310392f0692b0a927039230786f310670685f0885d06857088550584f058471183f0b83d118370b8350382f038270681f0681706d6f06d6b06d6706d6306c6706c6606c6506c5f05c5b06c5705c5307b5f08b5b08b5707b5303b4b06b4705b4306a6706a6609a6507a5f03a5b0aa5703a5305a4f03a4b06a4703a4305a3f08a3703a330696f0696b06967069630695f0695b06957069530594f0694b06947059430693f0693b06937069330392f0692b06927039230686f068670685f068570584f058470683f068370382f038270681f0681708d6f07d6308c6f09c6d09c6505c6307c5f05c5b09c5705c5308b6f09b6ea236d07b5f07b5e08b5b04b5a16b5704b5607b5307b5203b4b03b4a09b4703b4605b4308a6f0aa6d09a6503a6307a5f03a5b0aa5703a5305a4f03a4b09a4703a4305a3f05a3d09a3705a3503a330896f089630795f0c95b0f957079530594f0994b09947059430893f0193d0c93b029390f9370193508933029310392f0a92b0a927039230785f088570584f058470883f0b83d088370b8350382f038270881f0881704e7f04e7e04e7b04e7704e7307e7206d7f11d7e09d7b09d7a06d7709d7611d7311d7204d6f04d6e06d6d07d6c04d6704d6604d6504d6404d6304d6206c7f05c7b06c7705c7304c6f06c6d04c6b04c6704c6504c6303c5f03c5e03c5d04b7f11b7e04b7b04b7704b7304b7204b6704b6604b6504b5f07b5e04b5d07b5c04b4f05b4e03b4b03b4a04b4703b4604b4304b420aa7f03a7b09a7703a7304a6f07a6d03a6b04a6704a6503a6305a5f05a5e05a5d05a4f05a4e03a4b03a4903a4305a4203a410aa4004a3f04a3d03a3b03a3904a3705a3503a3303a311197f0697b09977069730496f0496b04967049630695f1195d0695b12959069571e95506953119510594f0694b06947059430493f0193d0493b02939049370193504933029310392f0692b0a927039230d87f0387b09877038730486f0386b04867038630685f0d85d0385b03859068570d85503853038510584f0384b05847038430483f0483d0383b048370b835038330382f0382b03827038230681f0381b068170381304e7d04e7504d7e04d7d04d6a04d6606c7e06c7d06c7c06c7506c7407c7204c6e04c6a04c6904c6804c6604c6206c6107c6006c5e06c5d06c5c06c5606c5506c5407c5206c5107c5006b7d06b7506b5d06b5503b4e03b4d0aa7d09a750aa5d09a5505a4e05a4d05a3e03a3905a3203a3109a3006979069710195d0295901955029510694d06949069450694103879038710685d068550684d06845 20 1048575 8 255 11 2047 20 1048575
def cur_66 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_66_5 (Nat.sub p 160)) (cc_66_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_66_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_66_2 (Nat.sub p 64)) (cc_66_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_66_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_66 : Nat → Nat × Nat := unpackForestF 0x18be02d7ee123dc245b5ac56d5bad52e80b47b2ac164972c5a380a5fae68f5cd16a2b15436fa98dd5318aa5b75435d0148f175be2e37c5c6e8b8c744db62e3145c5b9dce53adb2753645c578b29f3097260a24c1348b297295ca51ae4a25c8b28f24532452a459438b09f1d1ba2c26c65728b08e028de252ec2b47876bb0a91e151b8095f832b8f6d1e0126c02357b28cf8d29f1a33e2467b26c0254dd5a3bc24d7528cecd29d49b0094b716dee29bdc51b809476f26c024ed82b7b5a376b46ac11898137b4460604aec75bd8db731b62634dcc093586373004d0126eba91974a30092b4dade9b1bd65b026c575648eac91935b128d6f518dca29b9453126b4a4d2949cdb9341e809274746e949351c9ba434a4724e0217c04298084b3f68e7ed1505a29fa473f48a4358885b79dc623b6dc42d74e5ae90a6f358c46adbcd53710a5d2fce464df0be3997c6c2f8c0428dcadae95a5d2b46e425bc9e3013a6d2749a424dc8e3691b60236944249c84370084701076351b869378d16f1a24e34158041b8082b118de22db8563108b46112de2251c442b008270f2b812d1c351a849460a68c14918249b0081f01036071bc0db781b47030ac0205c04098003f 8 11
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV4 fullMask g_66 ep_66 188 bds_66 (dagTraceF fullMask rootStock 11 f_66) (cur_66 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_0 : treeBlockF 0 32 (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 188 (dagTraceF fullMask rootStock 11 f_66) cur_66) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_1 : treeBlockF 32 64 (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 188 (dagTraceF fullMask rootStock 11 f_66) cur_66) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_2 : treeBlockF 64 96 (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 188 (dagTraceF fullMask rootStock 11 f_66) cur_66) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_3 : treeBlockF 96 128 (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 188 (dagTraceF fullMask rootStock 11 f_66) cur_66) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_4 : treeBlockF 128 160 (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 188 (dagTraceF fullMask rootStock 11 f_66) cur_66) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_5 : treeBlockF 160 188 (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 188 (dagTraceF fullMask rootStock 11 f_66) cur_66) = true := by decide +kernel
theorem nj_66_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 188 (dagTraceF fullMask rootStock 11 f_66) cur_66) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_66_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_66_1 h1 h2)
theorem nj_66_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 188 (dagTraceF fullMask rootStock 11 f_66) cur_66) i = true := block_join nj_66_1 (fun _ h1 h2 => treeBlockF_at nb_66_2 h1 h2)
theorem nj_66_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 188 (dagTraceF fullMask rootStock 11 f_66) cur_66) i = true := block_join nj_66_2 (fun _ h1 h2 => treeBlockF_at nb_66_3 h1 h2)
theorem nj_66_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 188 (dagTraceF fullMask rootStock 11 f_66) cur_66) i = true := block_join nj_66_3 (fun _ h1 h2 => treeBlockF_at nb_66_4 h1 h2)
theorem nj_66_5 : ∀ i, 0 ≤ i → i < 188 → (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 188 (dagTraceF fullMask rootStock 11 f_66) cur_66) i = true := block_join nj_66_4 (fun _ h1 h2 => treeBlockF_at nb_66_5 h1 h2)
theorem nc_66 : ∀ i, 0 ≤ i → i < 188 → (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 188 (dagTraceF fullMask rootStock 11 f_66) cur_66) i = true := nj_66_5
theorem lb_66 : LowerBin fullMask rootStock g_66 12 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_66 kn_66 sub_66 gl_66 rc_66 nc_66

def wg : List Gate := [⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.or, [2, 9]⟩, ⟨GateOp.and, [7, 12]⟩, ⟨GateOp.and, [3, 13]⟩, ⟨GateOp.or, [3, 13]⟩, ⟨GateOp.and, [8, 11]⟩, ⟨GateOp.or, [14, 16]⟩, ⟨GateOp.and, [15, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 3936397440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676744 * 2 ^ 32 + 3936397440)) (13 - 1) := by
  rw [show canon fullMask (4276676744 * 2 ^ 32 + 3936397440) = g_66 by decide]
  exact lb_66

end PEqualNP.Outside.L_meta_49197

theorem PEqualNP.Outside.L_meta_49197 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676744 * 2 ^ 32 + 3936397440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 3936397440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_49197.table2_from_lowerBin (4276676744 * 2 ^ 32 + 3936397440) 13 PEqualNP.Outside.L_meta_49197.root_lb PEqualNP.Outside.L_meta_49197.wg 18 rfl PEqualNP.Outside.L_meta_49197.wfits PEqualNP.Outside.L_meta_49197.weval

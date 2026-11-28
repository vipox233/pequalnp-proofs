import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48849

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

theorem dagRefF_eq (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (parent token : Nat)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    dagRefF count states links parent token state = dagRef count states links parent token state := by
  unfold dagRefF dagRef
  cases links parent token with
  | none => rfl
  | some dest =>
    dsimp only
    cases Nat.blt dest count
    · rfl
    · dsimp only
      cases states dest with
      | none => rfl
      | some saved =>
        dsimp only
        rw [eqListN_eq]; cases Nat.beq saved.1 state.1 <;> rfl

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

def dagCheckChildrenF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, hist) := state
  let n := lenN ws
  Bool.rec
    (Bool.rec
      (Bool.rec false
        (treeBlockF 0 n (fun a =>
          let x := getDN ws a
          treeBlockF (Nat.add a 1) n (fun b =>
            let y := getDN ws b
            treeBlockF 0 4 (fun op =>
              forceW (binOpF mask op x y) (fun z =>
                Bool.rec
                  (Bool.rec
                    (treeBlockF 0 4 (fun keep =>
                      let keepA := Nat.beq (Nat.land keep 1) 1
                      let keepB := Nat.beq (Nat.land (Nat.shiftRight keep 1) 1) 1
                      let newLen := Nat.add (Nat.add (Nat.sub n 1) (Bool.rec 0 1 keepA)) (Bool.rec 0 1 keepB)
                      Bool.rec
                        (forceWs (insertSortedF z (dropValF (Bool.rec true false keepA) x (dropValF (Bool.rec true false keepB) y ws))) (fun ws' =>
                          let ch := (Nat.sub fuel 1, ws', (z, x, y) :: hist)
                          let tok := Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) op) 2) keep
                          Bool.rec (dagLocalF mask goal bounds ch) true (ref tok ch)))
                        true (Nat.blt fuel newLen)))
                    true (memN z ws))
                  true (Nat.beq z 0))))))
        (Nat.blt n 17))
      true (Nat.beq fuel 0))
    false (memN goal ws)

theorem makeTokenF_eq (a b op keep : Nat) :
    Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) op) 2) keep =
    makeToken a b op keep := by
  unfold makeToken
  change ((((a <<< 4) + b) <<< 2) + op) <<< 2 + keep = _
  simp only [Nat.shiftLeft_eq]

theorem dagCheckChildrenF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    dagCheckChildrenF mask goal bounds ref state = dagCheckChildren mask goal bounds ref state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold dagCheckChildrenF dagCheckChildren; dsimp only
  simp only [lenN_eq, memN_eq, treeBlockF_eq]
  cases ws.contains goal
  · cases Nat.beq fuel 0
    · cases Nat.blt ws.length 17
      · rfl
      · dsimp only
        simp only [Bool.not_false, Bool.true_and, Bool.false_or]
        congr 1; funext a
        simp only [getDN_eq]
        congr 1; funext b
        congr 1; funext op
        simp only [binOpF_eq, forceW_eq]
        cases Nat.beq (binOp mask op (ws.getD a 0) (ws.getD b 0)) 0
        · cases ws.contains (binOp mask op (ws.getD a 0) (ws.getD b 0))
          · dsimp only; simp only [Bool.false_or]
            congr 1; funext keep
            simp only [insertSortedF_eq, dropValF_eq, forceWs_eq, makeTokenF_eq, dagLocalF_eq hgoals]
            cases Nat.beq (keep &&& 1) 1 <;> cases Nat.beq ((keep >>> 1) &&& 1) 1
            all_goals dsimp only
            all_goals simp only [Bool.false_eq_true, ite_true, ite_false, Bool.not_true, Bool.not_false]
            all_goals cases Nat.blt fuel _
            all_goals try rfl
            all_goals cases ref (makeToken a b op keep) _ <;> cases dagLocal mask goal bounds _ <;> rfl
          · rfl
        · rfl
    · rfl
  · rfl

def dagCheckNodeF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildrenF mask goal bounds (dagRefF count states links (Nat.add i 1)) st

theorem dagCheckNodeF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (i : Nat) :
    dagCheckNodeF mask goal bounds count states links i = dagCheckNode mask goal bounds count states links i := by
  unfold dagCheckNodeF dagCheckNode
  cases states i with
  | none => rfl
  | some st =>
    have href : dagRefF count states links (Nat.add i 1) = dagRef count states links (i + 1) := by
      funext tok s; exact dagRefF_eq count states links (i + 1) tok s
    rw [href]; exact dagCheckChildrenF_eq hgoals _ st

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
    LowerBin mask stock goal (fuel + 1) := by
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr] at hroots hnodes
  have hr : dagCheckRoots mask goal bounds (dagRef count (dagTrace mask stock fuel forest) links 0) stock fuel = true := by
    have href : dagRefF count (dagTrace mask stock fuel forest) links 0 = dagRef count (dagTrace mask stock fuel forest) links 0 := by
      funext t s; exact dagRefF_eq count _ links 0 t s
    rw [href, dagCheckRootsF_eq hgoals] at hroots; exact hroots
  have hn : ∀ i, 0 ≤ i → i < count → dagCheckNode mask goal bounds count (dagTrace mask stock fuel forest) links i = true := by
    intro i h1 h2
    have h := hnodes i h1 h2
    rwa [dagCheckNodeF_eq hgoals] at h
  exact lowerDag hgm hgnz hcs snd hknown hsub hr hn

theorem treeBlockF_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlockF lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  rw [treeBlockF_eq] at h; exact treeBlock_at h

def m_0 : Nat := 0x4400440044004400
def s_0 : List Nat := [0x400040004000400, 0x440000004400, 0x44004400]
def g_0 : Nat := 0x40004004400
def bds_0 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_0 : KnownBin bds_0 := by intro b hb; simp [bds_0] at hb
theorem sub_0 : ∀ b ∈ bds_0, m_0 &&& b.1 = b.1 := by intro b hb; simp [bds_0] at hb
theorem gl_0 : ∀ b ∈ bds_0, canon b.1 g_0 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_0] at hb
def f_0 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_0 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_0 : dagCheckRootsF m_0 g_0 bds_0 (dagRefF 1 (dagTraceF m_0 s_0 3 f_0) l_0 0) s_0 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_0_0 : treeBlockF 0 1 (dagCheckNodeF m_0 g_0 bds_0 1 (dagTraceF m_0 s_0 3 f_0) l_0) = true := by decide +kernel
theorem nc_0 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_0 g_0 bds_0 1 (dagTraceF m_0 s_0 3 f_0) l_0) i = true := fun _ h1 h2 => treeBlockF_at nb_0_0 h1 h2
theorem lb_0 : LowerBin m_0 s_0 g_0 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_0 sub_0 gl_0 rc_0 nc_0

def m_1 : Nat := 0x5000500050005000
def s_1 : List Nat := [0x1000100010001000, 0x500000005000, 0x50005000]
def g_1 : Nat := 0x100010005000
def bds_1 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_1 : KnownBin bds_1 := by intro b hb; simp [bds_1] at hb
theorem sub_1 : ∀ b ∈ bds_1, m_1 &&& b.1 = b.1 := by intro b hb; simp [bds_1] at hb
theorem gl_1 : ∀ b ∈ bds_1, canon b.1 g_1 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_1] at hb
def f_1 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_1 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_1 : dagCheckRootsF m_1 g_1 bds_1 (dagRefF 1 (dagTraceF m_1 s_1 3 f_1) l_1 0) s_1 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_1_0 : treeBlockF 0 1 (dagCheckNodeF m_1 g_1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) l_1) = true := by decide +kernel
theorem nc_1 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_1 g_1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) l_1) i = true := fun _ h1 h2 => treeBlockF_at nb_1_0 h1 h2
theorem lb_1 : LowerBin m_1 s_1 g_1 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1 sub_1 gl_1 rc_1 nc_1

def m_2 : Nat := 0xa0a00000a0a
def s_2 : List Nat := [0x20200000202, 0xa0000000a, 0xa0a]
def g_2 : Nat := 0x20000020a
def bds_2 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_2 : KnownBin bds_2 := by intro b hb; simp [bds_2] at hb
theorem sub_2 : ∀ b ∈ bds_2, m_2 &&& b.1 = b.1 := by intro b hb; simp [bds_2] at hb
theorem gl_2 : ∀ b ∈ bds_2, canon b.1 g_2 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_2] at hb
def f_2 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_2 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_2 : dagCheckRootsF m_2 g_2 bds_2 (dagRefF 1 (dagTraceF m_2 s_2 3 f_2) l_2 0) s_2 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_2_0 : treeBlockF 0 1 (dagCheckNodeF m_2 g_2 bds_2 1 (dagTraceF m_2 s_2 3 f_2) l_2) = true := by decide +kernel
theorem nc_2 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_2 g_2 bds_2 1 (dagTraceF m_2 s_2 3 f_2) l_2) i = true := fun _ h1 h2 => treeBlockF_at nb_2_0 h1 h2
theorem lb_2 : LowerBin m_2 s_2 g_2 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2 sub_2 gl_2 rc_2 nc_2

def m_3 : Nat := 0x5500000055000000
def s_3 : List Nat := [0x1100000011000000, 0x500000005000000, 0x55000000]
def g_3 : Nat := 0x100000015000000
def bds_3 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_3 : KnownBin bds_3 := by intro b hb; simp [bds_3] at hb
theorem sub_3 : ∀ b ∈ bds_3, m_3 &&& b.1 = b.1 := by intro b hb; simp [bds_3] at hb
theorem gl_3 : ∀ b ∈ bds_3, canon b.1 g_3 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_3] at hb
def f_3 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_3 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_3 : dagCheckRootsF m_3 g_3 bds_3 (dagRefF 1 (dagTraceF m_3 s_3 3 f_3) l_3 0) s_3 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_3_0 : treeBlockF 0 1 (dagCheckNodeF m_3 g_3 bds_3 1 (dagTraceF m_3 s_3 3 f_3) l_3) = true := by decide +kernel
theorem nc_3 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_3 g_3 bds_3 1 (dagTraceF m_3 s_3 3 f_3) l_3) i = true := fun _ h1 h2 => treeBlockF_at nb_3_0 h1 h2
theorem lb_3 : LowerBin m_3 s_3 g_3 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_3 sub_3 gl_3 rc_3 nc_3

def m_4 : Nat := 0x22222222
def s_4 : List Nat := [0x2020202, 0x220022, 0x2222]
def g_4 : Nat := 0x20222
def bds_4 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_4 : KnownBin bds_4 := by intro b hb; simp [bds_4] at hb
theorem sub_4 : ∀ b ∈ bds_4, m_4 &&& b.1 = b.1 := by intro b hb; simp [bds_4] at hb
theorem gl_4 : ∀ b ∈ bds_4, canon b.1 g_4 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_4] at hb
def f_4 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_4 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_4 : dagCheckRootsF m_4 g_4 bds_4 (dagRefF 1 (dagTraceF m_4 s_4 3 f_4) l_4 0) s_4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_4_0 : treeBlockF 0 1 (dagCheckNodeF m_4 g_4 bds_4 1 (dagTraceF m_4 s_4 3 f_4) l_4) = true := by decide +kernel
theorem nc_4 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_4 g_4 bds_4 1 (dagTraceF m_4 s_4 3 f_4) l_4) i = true := fun _ h1 h2 => treeBlockF_at nb_4_0 h1 h2
theorem lb_4 : LowerBin m_4 s_4 g_4 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_4 sub_4 gl_4 rc_4 nc_4

def m_5 : Nat := 0xa0a0a0a
def s_5 : List Nat := [0x2020202, 0xa000a, 0xa0a]
def g_5 : Nat := 0x2020a
def bds_5 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_5 : KnownBin bds_5 := by intro b hb; simp [bds_5] at hb
theorem sub_5 : ∀ b ∈ bds_5, m_5 &&& b.1 = b.1 := by intro b hb; simp [bds_5] at hb
theorem gl_5 : ∀ b ∈ bds_5, canon b.1 g_5 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_5] at hb
def f_5 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_5 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_5 : dagCheckRootsF m_5 g_5 bds_5 (dagRefF 1 (dagTraceF m_5 s_5 3 f_5) l_5 0) s_5 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_5_0 : treeBlockF 0 1 (dagCheckNodeF m_5 g_5 bds_5 1 (dagTraceF m_5 s_5 3 f_5) l_5) = true := by decide +kernel
theorem nc_5 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_5 g_5 bds_5 1 (dagTraceF m_5 s_5 3 f_5) l_5) i = true := fun _ h1 h2 => treeBlockF_at nb_5_0 h1 h2
theorem lb_5 : LowerBin m_5 s_5 g_5 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_5 sub_5 gl_5 rc_5 nc_5

def m_6 : Nat := 0x3030303000000000
def s_6 : List Nat := [0x1010101000000000, 0x30003000000000, 0x303000000000]
def g_6 : Nat := 0x10103000000000
def bds_6 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_6 : KnownBin bds_6 := by intro b hb; simp [bds_6] at hb
theorem sub_6 : ∀ b ∈ bds_6, m_6 &&& b.1 = b.1 := by intro b hb; simp [bds_6] at hb
theorem gl_6 : ∀ b ∈ bds_6, canon b.1 g_6 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_6] at hb
def f_6 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_6 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_6 : dagCheckRootsF m_6 g_6 bds_6 (dagRefF 1 (dagTraceF m_6 s_6 3 f_6) l_6 0) s_6 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_6_0 : treeBlockF 0 1 (dagCheckNodeF m_6 g_6 bds_6 1 (dagTraceF m_6 s_6 3 f_6) l_6) = true := by decide +kernel
theorem nc_6 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_6 g_6 bds_6 1 (dagTraceF m_6 s_6 3 f_6) l_6) i = true := fun _ h1 h2 => treeBlockF_at nb_6_0 h1 h2
theorem lb_6 : LowerBin m_6 s_6 g_6 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_6 sub_6 gl_6 rc_6 nc_6

def m_7 : Nat := 0x5500550000000000
def s_7 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_7 : Nat := 0x100150000000000
def bds_7 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_7 : KnownBin bds_7 := by intro b hb; simp [bds_7] at hb
theorem sub_7 : ∀ b ∈ bds_7, m_7 &&& b.1 = b.1 := by intro b hb; simp [bds_7] at hb
theorem gl_7 : ∀ b ∈ bds_7, canon b.1 g_7 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_7] at hb
def f_7 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_7 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_7 : dagCheckRootsF m_7 g_7 bds_7 (dagRefF 1 (dagTraceF m_7 s_7 3 f_7) l_7 0) s_7 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_7_0 : treeBlockF 0 1 (dagCheckNodeF m_7 g_7 bds_7 1 (dagTraceF m_7 s_7 3 f_7) l_7) = true := by decide +kernel
theorem nc_7 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_7 g_7 bds_7 1 (dagTraceF m_7 s_7 3 f_7) l_7) i = true := fun _ h1 h2 => treeBlockF_at nb_7_0 h1 h2
theorem lb_7 : LowerBin m_7 s_7 g_7 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_7 sub_7 gl_7 rc_7 nc_7

def m_8 : Nat := 0x5555000000000000
def s_8 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_8 : Nat := 0x115000000000000
def bds_8 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_8 : KnownBin bds_8 := by intro b hb; simp [bds_8] at hb
theorem sub_8 : ∀ b ∈ bds_8, m_8 &&& b.1 = b.1 := by intro b hb; simp [bds_8] at hb
theorem gl_8 : ∀ b ∈ bds_8, canon b.1 g_8 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_8] at hb
def f_8 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_8 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_8 : dagCheckRootsF m_8 g_8 bds_8 (dagRefF 1 (dagTraceF m_8 s_8 3 f_8) l_8 0) s_8 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_8_0 : treeBlockF 0 1 (dagCheckNodeF m_8 g_8 bds_8 1 (dagTraceF m_8 s_8 3 f_8) l_8) = true := by decide +kernel
theorem nc_8 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_8 g_8 bds_8 1 (dagTraceF m_8 s_8 3 f_8) l_8) i = true := fun _ h1 h2 => treeBlockF_at nb_8_0 h1 h2
theorem lb_8 : LowerBin m_8 s_8 g_8 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_8 sub_8 gl_8 rc_8 nc_8

def m_9 : Nat := 0x3333000000000000
def s_9 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_9 : Nat := 0x113000000000000
def bds_9 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_9 : KnownBin bds_9 := by intro b hb; simp [bds_9] at hb
theorem sub_9 : ∀ b ∈ bds_9, m_9 &&& b.1 = b.1 := by intro b hb; simp [bds_9] at hb
theorem gl_9 : ∀ b ∈ bds_9, canon b.1 g_9 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_9] at hb
def f_9 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_9 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_9 : dagCheckRootsF m_9 g_9 bds_9 (dagRefF 1 (dagTraceF m_9 s_9 3 f_9) l_9 0) s_9 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_9_0 : treeBlockF 0 1 (dagCheckNodeF m_9 g_9 bds_9 1 (dagTraceF m_9 s_9 3 f_9) l_9) = true := by decide +kernel
theorem nc_9 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_9 g_9 bds_9 1 (dagTraceF m_9 s_9 3 f_9) l_9) i = true := fun _ h1 h2 => treeBlockF_at nb_9_0 h1 h2
theorem lb_9 : LowerBin m_9 s_9 g_9 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_9 sub_9 gl_9 rc_9 nc_9

def m_10 : Nat := 0xf0f000000000000
def s_10 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_10 : Nat := 0x107000000000000
def bds_10 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_10 : KnownBin bds_10 := by intro b hb; simp [bds_10] at hb
theorem sub_10 : ∀ b ∈ bds_10, m_10 &&& b.1 = b.1 := by intro b hb; simp [bds_10] at hb
theorem gl_10 : ∀ b ∈ bds_10, canon b.1 g_10 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_10] at hb
def f_10 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_10 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_10 : dagCheckRootsF m_10 g_10 bds_10 (dagRefF 1 (dagTraceF m_10 s_10 3 f_10) l_10 0) s_10 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_10_0 : treeBlockF 0 1 (dagCheckNodeF m_10 g_10 bds_10 1 (dagTraceF m_10 s_10 3 f_10) l_10) = true := by decide +kernel
theorem nc_10 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_10 g_10 bds_10 1 (dagTraceF m_10 s_10 3 f_10) l_10) i = true := fun _ h1 h2 => treeBlockF_at nb_10_0 h1 h2
theorem lb_10 : LowerBin m_10 s_10 g_10 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_10 sub_10 gl_10 rc_10 nc_10

def m_11 : Nat := 0xff000000000000
def s_11 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_11 : Nat := 0x17000000000000
def bds_11 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_11 : KnownBin bds_11 := by intro b hb; simp [bds_11] at hb
theorem sub_11 : ∀ b ∈ bds_11, m_11 &&& b.1 = b.1 := by intro b hb; simp [bds_11] at hb
theorem gl_11 : ∀ b ∈ bds_11, canon b.1 g_11 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_11] at hb
def f_11 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_11 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsF m_11 g_11 bds_11 (dagRefF 1 (dagTraceF m_11 s_11 3 f_11) l_11 0) s_11 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_11_0 : treeBlockF 0 1 (dagCheckNodeF m_11 g_11 bds_11 1 (dagTraceF m_11 s_11 3 f_11) l_11) = true := by decide +kernel
theorem nc_11 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_11 g_11 bds_11 1 (dagTraceF m_11 s_11 3 f_11) l_11) i = true := fun _ h1 h2 => treeBlockF_at nb_11_0 h1 h2
theorem lb_11 : LowerBin m_11 s_11 g_11 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_11 sub_11 gl_11 rc_11 nc_11

def m_12 : Nat := 0xff0000
def s_12 : List Nat := [0x550000, 0x330000, 0xf0000]
def g_12 : Nat := 0x170000
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_12 : KnownBin bds_12 := by intro b hb; simp [bds_12] at hb
theorem sub_12 : ∀ b ∈ bds_12, m_12 &&& b.1 = b.1 := by intro b hb; simp [bds_12] at hb
theorem gl_12 : ∀ b ∈ bds_12, canon b.1 g_12 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_12] at hb
def f_12 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_12 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsF m_12 g_12 bds_12 (dagRefF 1 (dagTraceF m_12 s_12 3 f_12) l_12 0) s_12 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12_0 : treeBlockF 0 1 (dagCheckNodeF m_12 g_12 bds_12 1 (dagTraceF m_12 s_12 3 f_12) l_12) = true := by decide +kernel
theorem nc_12 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_12 g_12 bds_12 1 (dagTraceF m_12 s_12 3 f_12) l_12) i = true := fun _ h1 h2 => treeBlockF_at nb_12_0 h1 h2
theorem lb_12 : LowerBin m_12 s_12 g_12 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_12 sub_12 gl_12 rc_12 nc_12

def m_13 : Nat := 0x4444444444444444
def s_13 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_13 : Nat := 0x4040404044444
def bds_13 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_13 : KnownBin bds_13 := by
  intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_13 : ∀ b ∈ bds_13, m_13 &&& b.1 = b.1 := by intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_13 : ∀ b ∈ bds_13, canon b.1 g_13 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_13 : Nat → Nat × Nat := fun _ => (0, 0)
def l_13 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsF m_13 g_13 bds_13 (dagRefF 0 (dagTraceF m_13 s_13 4 f_13) l_13 0) s_13 4 = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_13 g_13 bds_13 0 (dagTraceF m_13 s_13 4 f_13) l_13 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_13 : LowerBin m_13 s_13 g_13 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_13 sub_13 gl_13 rc_13 nc_13

def m_14 : Nat := 0x2222222222222222
def s_14 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_14 : Nat := 0x2002200020222
def bds_14 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_14 : KnownBin bds_14 := by
  intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_14 : ∀ b ∈ bds_14, m_14 &&& b.1 = b.1 := by intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_14 : ∀ b ∈ bds_14, canon b.1 g_14 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_14 : Nat → Nat × Nat := fun _ => (0, 0)
def l_14 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsF m_14 g_14 bds_14 (dagRefF 0 (dagTraceF m_14 s_14 4 f_14) l_14 0) s_14 4 = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_14 g_14 bds_14 0 (dagTraceF m_14 s_14 4 f_14) l_14 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_14 : LowerBin m_14 s_14 g_14 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_14 sub_14 gl_14 rc_14 nc_14

def m_15 : Nat := 0x5050505050505050
def s_15 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_15 : Nat := 0x10101010105050
def bds_15 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_15 : KnownBin bds_15 := by
  intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_15 : ∀ b ∈ bds_15, m_15 &&& b.1 = b.1 := by intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_15 : ∀ b ∈ bds_15, canon b.1 g_15 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_15 : Nat → Nat × Nat := fun _ => (0, 0)
def l_15 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsF m_15 g_15 bds_15 (dagRefF 0 (dagTraceF m_15 s_15 4 f_15) l_15 0) s_15 4 = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_15 g_15 bds_15 0 (dagTraceF m_15 s_15 4 f_15) l_15 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_15 : LowerBin m_15 s_15 g_15 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_15 sub_15 gl_15 rc_15 nc_15

def m_16 : Nat := 0xa0a0a0a0a0a0a0a
def s_16 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_16 : Nat := 0x200020002020a
def bds_16 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_16 : KnownBin bds_16 := by
  intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_16 : ∀ b ∈ bds_16, m_16 &&& b.1 = b.1 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_16 : ∀ b ∈ bds_16, canon b.1 g_16 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_16 : Nat → Nat × Nat := fun _ => (0, 0)
def l_16 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsF m_16 g_16 bds_16 (dagRefF 0 (dagTraceF m_16 s_16 4 f_16) l_16 0) s_16 4 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_16 g_16 bds_16 0 (dagTraceF m_16 s_16 4 f_16) l_16 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_16 : LowerBin m_16 s_16 g_16 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_16 sub_16 gl_16 rc_16 nc_16

def m_17 : Nat := 0x3030303030303030
def s_17 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_17 : Nat := 0x10103010101030
def bds_17 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_17 : KnownBin bds_17 := by
  intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_17 : ∀ b ∈ bds_17, m_17 &&& b.1 = b.1 := by intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_17 : ∀ b ∈ bds_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_17 : Nat → Nat × Nat := fun _ => (0, 0)
def l_17 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsF m_17 g_17 bds_17 (dagRefF 0 (dagTraceF m_17 s_17 4 f_17) l_17 0) s_17 4 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_17 g_17 bds_17 0 (dagTraceF m_17 s_17 4 f_17) l_17 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_17 : LowerBin m_17 s_17 g_17 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_17 sub_17 gl_17 rc_17 nc_17

def m_18 : Nat := 0xc0c0c0c0c0c0c0c
def s_18 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_18 : Nat := 0x404040404040c
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_18 : KnownBin bds_18 := by intro b hb; simp [bds_18] at hb
theorem sub_18 : ∀ b ∈ bds_18, m_18 &&& b.1 = b.1 := by intro b hb; simp [bds_18] at hb
theorem gl_18 : ∀ b ∈ bds_18, canon b.1 g_18 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_18] at hb
def f_18 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_18 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsF m_18 g_18 bds_18 (dagRefF 64 (dagTraceF m_18 s_18 5 f_18) l_18 0) s_18 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18_0 : treeBlockF 0 32 (dagCheckNodeF m_18 g_18 bds_18 64 (dagTraceF m_18 s_18 5 f_18) l_18) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18_1 : treeBlockF 32 64 (dagCheckNodeF m_18 g_18 bds_18 64 (dagTraceF m_18 s_18 5 f_18) l_18) = true := by decide +kernel
theorem nj_18_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_18 g_18 bds_18 64 (dagTraceF m_18 s_18 5 f_18) l_18) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_18_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_18_1 h1 h2)
theorem nc_18 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_18 g_18 bds_18 64 (dagTraceF m_18 s_18 5 f_18) l_18) i = true := nj_18_1
theorem lb_18 : LowerBin m_18 s_18 g_18 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_18 sub_18 gl_18 rc_18 nc_18

def m_19 : Nat := 0x5500550055005500
def s_19 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_19 : Nat := 0x100150015005500
def bds_19 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1), (m_3, s_3, 4, g_3), (m_7, s_7, 4, g_7)]
theorem kn_19 : KnownBin bds_19 := by
  intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_0
  · exact lb_1
  · exact lb_3
  · exact lb_7
theorem sub_19 : ∀ b ∈ bds_19, m_19 &&& b.1 = b.1 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_19 : ∀ b ∈ bds_19, canon b.1 g_19 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_19 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def l_19 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c1fc3f07c2f81b43606c0d45a0b40662cc15c2b0542a8148a18420841009f13e0784f01d12b0540a814128050098921222440809001e21e00b001 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d347d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 11 4 10 6 5
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsF m_19 g_19 bds_19 (dagRefF 43 (dagTraceF m_19 s_19 6 f_19) l_19 0) s_19 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_0 : treeBlockF 0 32 (dagCheckNodeF m_19 g_19 bds_19 43 (dagTraceF m_19 s_19 6 f_19) l_19) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_1 : treeBlockF 32 43 (dagCheckNodeF m_19 g_19 bds_19 43 (dagTraceF m_19 s_19 6 f_19) l_19) = true := by decide +kernel
theorem nj_19_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_19 g_19 bds_19 43 (dagTraceF m_19 s_19 6 f_19) l_19) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_19_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_19_1 h1 h2)
theorem nc_19 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_19 g_19 bds_19 43 (dagTraceF m_19 s_19 6 f_19) l_19) i = true := nj_19_1
theorem lb_19 : LowerBin m_19 s_19 g_19 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_19 sub_19 gl_19 rc_19 nc_19

def m_20 : Nat := 0xcc00cc00cc00cc00
def s_20 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_20 : Nat := 0x40004004400
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_20 : KnownBin bds_20 := by
  intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_20 : ∀ b ∈ bds_20, m_20 &&& b.1 = b.1 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_20 : Nat → Nat × Nat := fun _ => (0, 0)
def l_20 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsF m_20 g_20 bds_20 (dagRefF 0 (dagTraceF m_20 s_20 4 f_20) l_20 0) s_20 4 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_20 g_20 bds_20 0 (dagTraceF m_20 s_20 4 f_20) l_20 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0x3300330033003300
def s_21 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_21 : Nat := 0x100110011001300
def bds_21 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_21 : KnownBin bds_21 := by intro b hb; simp [bds_21] at hb
theorem sub_21 : ∀ b ∈ bds_21, m_21 &&& b.1 = b.1 := by intro b hb; simp [bds_21] at hb
theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_21] at hb
def f_21 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_21 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsF m_21 g_21 bds_21 (dagRefF 64 (dagTraceF m_21 s_21 5 f_21) l_21 0) s_21 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_0 : treeBlockF 0 32 (dagCheckNodeF m_21 g_21 bds_21 64 (dagTraceF m_21 s_21 5 f_21) l_21) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_1 : treeBlockF 32 64 (dagCheckNodeF m_21 g_21 bds_21 64 (dagTraceF m_21 s_21 5 f_21) l_21) = true := by decide +kernel
theorem nj_21_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_21 g_21 bds_21 64 (dagTraceF m_21 s_21 5 f_21) l_21) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_21_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_21_1 h1 h2)
theorem nc_21 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_21 g_21 bds_21 64 (dagTraceF m_21 s_21 5 f_21) l_21) i = true := nj_21_1
theorem lb_21 : LowerBin m_21 s_21 g_21 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0xf000f000f000f000
def s_22 : List Nat := [0x5000500050005000, 0x3000300030003000, 0xf0000000f000, 0xf000f000]
def g_22 : Nat := 0x100010005000
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_22 : KnownBin bds_22 := by
  intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_22 : ∀ b ∈ bds_22, m_22 &&& b.1 = b.1 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
def l_22 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsF m_22 g_22 bds_22 (dagRefF 0 (dagTraceF m_22 s_22 4 f_22) l_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_22 g_22 bds_22 0 (dagTraceF m_22 s_22 4 f_22) l_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0xf000f000f000f00
def s_23 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_23 : Nat := 0x100050005000700
def bds_23 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_23 : KnownBin bds_23 := by intro b hb; simp [bds_23] at hb
theorem sub_23 : ∀ b ∈ bds_23, m_23 &&& b.1 = b.1 := by intro b hb; simp [bds_23] at hb
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_23] at hb
def f_23 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_23 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsF m_23 g_23 bds_23 (dagRefF 64 (dagTraceF m_23 s_23 5 f_23) l_23 0) s_23 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23_0 : treeBlockF 0 32 (dagCheckNodeF m_23 g_23 bds_23 64 (dagTraceF m_23 s_23 5 f_23) l_23) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23_1 : treeBlockF 32 64 (dagCheckNodeF m_23 g_23 bds_23 64 (dagTraceF m_23 s_23 5 f_23) l_23) = true := by decide +kernel
theorem nj_23_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_23 g_23 bds_23 64 (dagTraceF m_23 s_23 5 f_23) l_23) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_23_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_23_1 h1 h2)
theorem nc_23 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_23 g_23 bds_23 64 (dagTraceF m_23 s_23 5 f_23) l_23) i = true := nj_23_1
theorem lb_23 : LowerBin m_23 s_23 g_23 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0x5555000055550000
def s_24 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_24 : Nat := 0x115000015150000
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_24 : ∀ b ∈ bds_24, m_24 &&& b.1 = b.1 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
def l_24 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsF m_24 g_24 bds_24 (dagRefF 0 (dagTraceF m_24 s_24 4 f_24) l_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_24 g_24 bds_24 0 (dagTraceF m_24 s_24 4 f_24) l_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0xaaaa0000aaaa
def s_25 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_25 : Nat := 0x22000002aa
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
def l_25 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsF m_25 g_25 bds_25 (dagRefF 0 (dagTraceF m_25 s_25 4 f_25) l_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_25 g_25 bds_25 0 (dagTraceF m_25 s_25 4 f_25) l_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0x3333000033330000
def s_26 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_26 : Nat := 0x113000011130000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
def l_26 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsF m_26 g_26 bds_26 (dagRefF 0 (dagTraceF m_26 s_26 4 f_26) l_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_26 g_26 bds_26 0 (dagTraceF m_26 s_26 4 f_26) l_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0xf0f00000f0f0000
def s_27 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_27 : Nat := 0x107000005070000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
def l_27 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsF m_27 g_27 bds_27 (dagRefF 0 (dagTraceF m_27 s_27 4 f_27) l_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_27 g_27 bds_27 0 (dagTraceF m_27 s_27 4 f_27) l_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xf0f00000f0f
def s_28 : List Nat := [0x50500000505, 0x30300000303, 0xf0000000f, 0xf0f]
def g_28 : Nat := 0x5070000070f
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
def l_28 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsF m_28 g_28 bds_28 (dagRefF 0 (dagTraceF m_28 s_28 4 f_28) l_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_28 g_28 bds_28 0 (dagTraceF m_28 s_28 4 f_28) l_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xff000000ff000000
def s_29 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_29 : Nat := 0x100000015000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
def l_29 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsF m_29 g_29 bds_29 (dagRefF 0 (dagTraceF m_29 s_29 4 f_29) l_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_29 g_29 bds_29 0 (dagTraceF m_29 s_29 4 f_29) l_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0xff000000ff00
def s_30 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_30 : Nat := 0x150000005700
def bds_30 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_30 : KnownBin bds_30 := by intro b hb; simp [bds_30] at hb
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp [bds_30] at hb
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_30] at hb
def f_30 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_30 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsF m_30 g_30 bds_30 (dagRefF 64 (dagTraceF m_30 s_30 5 f_30) l_30 0) s_30 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_0 : treeBlockF 0 32 (dagCheckNodeF m_30 g_30 bds_30 64 (dagTraceF m_30 s_30 5 f_30) l_30) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_1 : treeBlockF 32 64 (dagCheckNodeF m_30 g_30 bds_30 64 (dagTraceF m_30 s_30 5 f_30) l_30) = true := by decide +kernel
theorem nj_30_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_30 g_30 bds_30 64 (dagTraceF m_30 s_30 5 f_30) l_30) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_30_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_30_1 h1 h2)
theorem nc_30 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_30 g_30 bds_30 64 (dagTraceF m_30 s_30 5 f_30) l_30) i = true := nj_30_1
theorem lb_30 : LowerBin m_30 s_30 g_30 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0x5555555500000000
def s_31 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_31 : Nat := 0x115151500000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
def l_31 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsF m_31 g_31 bds_31 (dagRefF 0 (dagTraceF m_31 s_31 4 f_31) l_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_31 g_31 bds_31 0 (dagTraceF m_31 s_31 4 f_31) l_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0xaaaaaaaa
def s_32 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_32 : Nat := 0x202aa
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
def l_32 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsF m_32 g_32 bds_32 (dagRefF 0 (dagTraceF m_32 s_32 4 f_32) l_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_32 g_32 bds_32 0 (dagTraceF m_32 s_32 4 f_32) l_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0x3333333300000000
def s_33 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_33 : Nat := 0x113113300000000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
def l_33 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsF m_33 g_33 bds_33 (dagRefF 0 (dagTraceF m_33 s_33 4 f_33) l_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_33 g_33 bds_33 0 (dagTraceF m_33 s_33 4 f_33) l_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0x33333333
def s_34 : List Nat := [0x11111111, 0x3030303, 0x330033, 0x3333]
def g_34 : Nat := 0x11131333
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
def l_34 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsF m_34 g_34 bds_34 (dagRefF 0 (dagTraceF m_34 s_34 4 f_34) l_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_34 g_34 bds_34 0 (dagTraceF m_34 s_34 4 f_34) l_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xf0f0f0f000000000
def s_35 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_35 : Nat := 0x10103000000000
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
def l_35 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsF m_35 g_35 bds_35 (dagRefF 0 (dagTraceF m_35 s_35 4 f_35) l_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_35 g_35 bds_35 0 (dagTraceF m_35 s_35 4 f_35) l_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0xf0f0f0f00000000
def s_36 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_36 : Nat := 0x107050700000000
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
def l_36 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsF m_36 g_36 bds_36 (dagRefF 0 (dagTraceF m_36 s_36 4 f_36) l_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_36 g_36 bds_36 0 (dagTraceF m_36 s_36 4 f_36) l_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0xf0f0f0f
def s_37 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_37 : Nat := 0x507070f
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
def l_37 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsF m_37 g_37 bds_37 (dagRefF 0 (dagTraceF m_37 s_37 4 f_37) l_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_37 g_37 bds_37 0 (dagTraceF m_37 s_37 4 f_37) l_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xff00ff0000000000
def s_38 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_38 : Nat := 0x100150000000000
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
def l_38 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsF m_38 g_38 bds_38 (dagRefF 0 (dagTraceF m_38 s_38 4 f_38) l_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_38 g_38 bds_38 0 (dagTraceF m_38 s_38 4 f_38) l_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xff00ff00000000
def s_39 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_39 : Nat := 0x17003700000000
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_11
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
def l_39 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsF m_39 g_39 bds_39 (dagRefF 0 (dagTraceF m_39 s_39 4 f_39) l_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_39 g_39 bds_39 0 (dagTraceF m_39 s_39 4 f_39) l_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0xff00ff00
def s_40 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_40 : Nat := 0x15005700
def bds_40 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_40 : KnownBin bds_40 := by intro b hb; simp [bds_40] at hb
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp [bds_40] at hb
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_40] at hb
def f_40 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_40 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsF m_40 g_40 bds_40 (dagRefF 64 (dagTraceF m_40 s_40 5 f_40) l_40 0) s_40 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_0 : treeBlockF 0 32 (dagCheckNodeF m_40 g_40 bds_40 64 (dagTraceF m_40 s_40 5 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_1 : treeBlockF 32 64 (dagCheckNodeF m_40 g_40 bds_40 64 (dagTraceF m_40 s_40 5 f_40) l_40) = true := by decide +kernel
theorem nj_40_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_40 g_40 bds_40 64 (dagTraceF m_40 s_40 5 f_40) l_40) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_40_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_40_1 h1 h2)
theorem nc_40 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_40 g_40 bds_40 64 (dagTraceF m_40 s_40 5 f_40) l_40) i = true := nj_40_1
theorem lb_40 : LowerBin m_40 s_40 g_40 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0xff00ff
def s_41 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_41 : Nat := 0x1700ff
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
def l_41 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsF m_41 g_41 bds_41 (dagRefF 0 (dagTraceF m_41 s_41 4 f_41) l_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_41 g_41 bds_41 0 (dagTraceF m_41 s_41 4 f_41) l_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xffff000000000000
def s_42 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_42 : Nat := 0x117000000000000
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8), (m_9, s_9, 4, g_9), (m_10, s_10, 4, g_10), (m_11, s_11, 4, g_11)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_8
  · exact lb_9
  · exact lb_10
  · exact lb_11
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_42 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def l_42 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c1fc3e17c0f81b43516a0d05a0340662cc15c2a1522a41482184027c4f81e13c0780e89d02b05049893024248088910220404801001e21e00b001 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b407c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 11 4 10 6 5
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsF m_42 g_42 bds_42 (dagRefF 43 (dagTraceF m_42 s_42 6 f_42) l_42 0) s_42 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_0 : treeBlockF 0 32 (dagCheckNodeF m_42 g_42 bds_42 43 (dagTraceF m_42 s_42 6 f_42) l_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_1 : treeBlockF 32 43 (dagCheckNodeF m_42 g_42 bds_42 43 (dagTraceF m_42 s_42 6 f_42) l_42) = true := by decide +kernel
theorem nj_42_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_42 g_42 bds_42 43 (dagTraceF m_42 s_42 6 f_42) l_42) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_42_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_42_1 h1 h2)
theorem nc_42 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_42 g_42 bds_42 43 (dagTraceF m_42 s_42 6 f_42) l_42) i = true := nj_42_1
theorem lb_42 : LowerBin m_42 s_42 g_42 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xffff0000
def s_43 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_43 : Nat := 0x15170000
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
def l_43 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsF m_43 g_43 bds_43 (dagRefF 0 (dagTraceF m_43 s_43 4 f_43) l_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_43 g_43 bds_43 0 (dagTraceF m_43 s_43 4 f_43) l_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xaaaaaaaaaaaaaaaa
def s_44 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_44 : Nat := 0x20022000202aa
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 5, g_14), (m_16, s_16, 5, g_16), (m_25, s_25, 5, g_25), (m_32, s_32, 5, g_32)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_14
  · exact lb_16
  · exact lb_25
  · exact lb_32
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_44 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
def l_44 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x1f 2 1 5 1 2
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsF m_44 g_44 bds_44 (dagRefF 1 (dagTraceF m_44 s_44 6 f_44) l_44 0) s_44 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_0 : treeBlockF 0 1 (dagCheckNodeF m_44 g_44 bds_44 1 (dagTraceF m_44 s_44 6 f_44) l_44) = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_44 g_44 bds_44 1 (dagTraceF m_44 s_44 6 f_44) l_44) i = true := fun _ h1 h2 => treeBlockF_at nb_44_0 h1 h2
theorem lb_44 : LowerBin m_44 s_44 g_44 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0x5555555555555555
def s_45 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_45 : Nat := 0x115151515155555
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 7, g_19)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_19
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
def l_45 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsF m_45 g_45 bds_45 (dagRefF 0 (dagTraceF m_45 s_45 7 f_45) l_45 0) s_45 7 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_45 g_45 bds_45 0 (dagTraceF m_45 s_45 7 f_45) l_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0xcccccccccccccccc
def s_46 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_46 : Nat := 0x40404040444cc
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 6, g_18)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_18
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
def l_46 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsF m_46 g_46 bds_46 (dagRefF 0 (dagTraceF m_46 s_46 6 f_46) l_46 0) s_46 6 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_46 g_46 bds_46 0 (dagTraceF m_46 s_46 6 f_46) l_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0x3333333333333333
def s_47 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_47 : Nat := 0x113113311131333
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 6, g_21), (m_14, s_14, 5, g_14), (m_17, s_17, 5, g_17), (m_26, s_26, 5, g_26), (m_33, s_33, 5, g_33), (m_34, s_34, 5, g_34), (m_4, s_4, 4, g_4), (m_6, s_6, 4, g_6), (m_9, s_9, 4, g_9)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_21
  · exact lb_14
  · exact lb_17
  · exact lb_26
  · exact lb_33
  · exact lb_34
  · exact lb_4
  · exact lb_6
  · exact lb_9
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_47 : Nat → Nat × Nat := unpackForestF 0x145745a3c35d128e516952e145626ac455849b801f 4 11
def l_47 : Nat → Nat → Option Nat := unpackLinksF 0xf18f04b91220c08090581 0x145750aa993586ba8d5489b2a5c68b49158dab1156968ee51c49b801f 7 3 11 4 4
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsF m_47 g_47 bds_47 (dagRefF 11 (dagTraceF m_47 s_47 7 f_47) l_47 0) s_47 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_0 : treeBlockF 0 11 (dagCheckNodeF m_47 g_47 bds_47 11 (dagTraceF m_47 s_47 7 f_47) l_47) = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeF m_47 g_47 bds_47 11 (dagTraceF m_47 s_47 7 f_47) l_47) i = true := fun _ h1 h2 => treeBlockF_at nb_47_0 h1 h2
theorem lb_47 : LowerBin m_47 s_47 g_47 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_47 sub_47 gl_47 rc_47 nc_47

def m_48 : Nat := 0xf0f0f0f0f0f0f0f0
def s_48 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_48 : Nat := 0x101030101050f0
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 5, g_15), (m_17, s_17, 5, g_17), (m_22, s_22, 5, g_22), (m_35, s_35, 5, g_35), (m_1, s_1, 4, g_1), (m_6, s_6, 4, g_6)]
theorem kn_48 : KnownBin bds_48 := by
  intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_15
  · exact lb_17
  · exact lb_22
  · exact lb_35
  · exact lb_1
  · exact lb_6
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_48 : Nat → Nat × Nat := unpackForestF 0x24939948f2503c924d40b438a4e6303c8a4d40a3f860d20b4982114094f71145c15d70539c13574d05d14d704d1c0150250db24466d799b52668d4093f4f149395e5c4d170144e549394d4e4d9381650d09413d4e050093342d39094e46051094242054092b36d38f02436d08d929360f409272e524c25c2e514084f264f49931264a4082716578813416548593a164d8585e160d8081f04978413404948123a08d402340048d8101e0205c001f 7 11
def l_48 : Nat → Nat → Option Nat := unpackLinksF 0x3a8750ea1ccb6b6d0da1b073ae70cc3983035f1bc3782e8dd0ba16cad8529a414468851096d286504a094120a38c708c318230442772ec1d83b0742e8194320640c458831056cac1582a14aa941282503ec7c0f81e13c0780f01e02d0580b01512a0540a81322603580e001 0x25a3c940f1f95162505a13d984e649355a4c6303c3e4f639398a4d511314a4a618347d176134968d05f151121360845764d1d13474571db4174535fc517c975f15d7a5396942784d5c9341e075c0156c911ab5e68d49634d3e8f59a355850548145e4d1701450051404c52d09413d63149624d60579695258535113a564d950164e05118144ad38e235485391142384d498351c07508153c090fb4e3ad08e23e384a4d83d060d4c25c12534c9492e514794118078a93d1c4e41935284c499291607881342257879521c4e86936181785836040981016104d02b5008d004a5e0e948323a068d8102e0407a4343888fe014f6e50d913f4c4cd012b3449cb04f2409c501f0205c001f 11 4 11 7 5
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsF m_48 g_48 bds_48 (dagRefF 77 (dagTraceF m_48 s_48 7 f_48) l_48 0) s_48 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_0 : treeBlockF 0 32 (dagCheckNodeF m_48 g_48 bds_48 77 (dagTraceF m_48 s_48 7 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_1 : treeBlockF 32 64 (dagCheckNodeF m_48 g_48 bds_48 77 (dagTraceF m_48 s_48 7 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_2 : treeBlockF 64 77 (dagCheckNodeF m_48 g_48 bds_48 77 (dagTraceF m_48 s_48 7 f_48) l_48) = true := by decide +kernel
theorem nj_48_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_48 g_48 bds_48 77 (dagTraceF m_48 s_48 7 f_48) l_48) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_48_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_48_1 h1 h2)
theorem nj_48_2 : ∀ i, 0 ≤ i → i < 77 → (dagCheckNodeF m_48 g_48 bds_48 77 (dagTraceF m_48 s_48 7 f_48) l_48) i = true := block_join nj_48_1 (fun _ h1 h2 => treeBlockF_at nb_48_2 h1 h2)
theorem nc_48 : ∀ i, 0 ≤ i → i < 77 → (dagCheckNodeF m_48 g_48 bds_48 77 (dagTraceF m_48 s_48 7 f_48) l_48) i = true := nj_48_2
theorem lb_48 : LowerBin m_48 s_48 g_48 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0xf0f0f0f0f0f0f0f
def s_49 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_49 : Nat := 0x10705070507070f
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 6, g_18), (m_23, s_23, 6, g_23), (m_16, s_16, 5, g_16), (m_27, s_27, 5, g_27), (m_28, s_28, 5, g_28), (m_36, s_36, 5, g_36), (m_37, s_37, 5, g_37), (m_2, s_2, 4, g_2), (m_5, s_5, 4, g_5), (m_10, s_10, 4, g_10)]
theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_18
  · exact lb_23
  · exact lb_16
  · exact lb_27
  · exact lb_28
  · exact lb_36
  · exact lb_37
  · exact lb_2
  · exact lb_5
  · exact lb_10
theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_49 : Nat → Nat × Nat := unpackForestF 0xad24500b4fa6a5fa6a5daa46caa160aa060a6a57a9154a695ba6953a7854a685ba685300b47a5c5ea4b55a4b4500a4f9a35f9a35da1c6ca1960a18609a357a0c5e9a34d9f35c9f26c9a3479db4e9da5e9a3459c9549a15b9a1539b0549a05b9a05300a4798b5498a547245f97d6c7245b96b567245a9336c9326c9316c931609306c93060724578bc5e8bb5e8ba5e8b95e8fb5c8fa5c8b9528e05c8e0508b85e8c35c8c25c8c15c8b852724568ab5c87d6487b5c879388793487838878347245385b4985b4185a5e7235682b4982b4182a5e82a4682a447225681048810447214f7da5c7d9447d9347d8187e14c7d8147214b7c35c7c25c721477b14c7aa547214379148791447204f7595c75844758347582c7604c758247204b7435c7425c720477304c729547204300a377125d6d3457035d6d2456dc586dc546db546da546d2370094f6c3470094b6b2456635d6a3456625d68c6c68c6066237679276605c66a3766050009476515c5c34763a4d63a355c1466223f622375c1446034a60346602465c1365ea3b5ea375c1345da375c0185ca375c014009435ac6c5a96c55b5759a5d55a5658a5d559565635a563565625656156559360093b54a4d009375336c5316c4dc575235d4da564da4650b5d4d9564e45a4e4564e3564e1564d9460092b4c34a4c14a009274b25d473454a35d4724547c5847c5447b5447a54472370084f463470084b452454035d443454025d42c6c42c6040237419274015c40a3740150008473f05c363473da4d3da35360463c23f3c237360443a34a3a3463a2463603638a3b38a373603437a373602c36a37360240084334c6c3486c2fb5733a5d2f95632a5d2f8563035a3035630256300562f8360083b2ca4d2d3502d3482d25c2c927008372b36c2b06c25c572a35d259562594628b5d258562645a264562635626056258460082b2234a23350233482325c221472204a008272115c1e3472024d1e1461eb4a1eb461e1360081f1d05c1a3471c24d1a0461ab4a1ab461a0360081b19347008171806c014571706c013571605c013471524d012461434a0123611a4d122381214c11926011460f34a0fa380f94c0f146011360e04c0da37011240b35d0b3450b25d0b2450105606c5a09a5c06c5606b5606a4d06a3506926068260104601b5a0535c01b5601b4a01b4601a5601a46019460184601036008130001f 9 11
def l_49 : Nat → Nat → Option Nat := unpackLinksF 0x8501090a0f1c16482c10506090c08581010186030406080830101f37be607c82f901f013da37a48f481e80bce1788af101e10bc207840ef0dde03bc076c6ed81da0bb407680ec85d90394f7280e501c6238a17048e081bf137e06fc0df81bf037e06fc0dba1b7036a26cc4d889b1036206b86d701ae035826b00d601ac035236850d081a00b4006800d001a0034006610cc01980330064cac981930326064c0c9818e2b1c06380c58d89131206240c481890310160cac18183030036000bf857e0afc05f80bd8d7912f205e40bc817902f015ccab9817302e035c00b7856e0aa5c5480a78d4f029835300a6014c029805208a28d45028815100a08d41027c34f809f013a227404e429c81380a6274c4095992b025604a06940128024c249809301260246348c091812112420480290011f0a30746008c01142228044848901101220044008801100218441ca8289012202040407e90fd01f623ec07d80f911f203e407c80f901ea43c0a7708ee01d443a80738ce701c8339007200e401c8038086e8cdd01b8137006c8cd901ac335806b00d221a4034426880d00992732406198c30186030066000c0017c22f805f00be017632ec05d80b9117202e025c00b7096072c005800ac215802a845500a8115002a005400a80148427ca4e889d0138126c24b90932126024c047908f011a2234046808b1116022c045808b010e4208a40088000fe11f823d107a00ec41d803a087400e421c8039007010da31b4035886b00d221a4034806710c8318c230886100ba417402c905808a651482278c4e08963128225004a0090211462204440088010841f8c3f007c10f421e803d007a00f401b9837006e00d821b0036006c00d801b002e405c00b8016842d005a00b4016802d005a009500d2c01c8001 0xa0255ad245912649da4485a34912569f246539292b8298fa5c8ca5cab46c9fb6c9125caa960aa060a9154a7854ac25faba5da9a578b255a524d9ea479d24585235a895ba81535292ba705ba68532a82b17813a5c5ea5355a4b4591b649e35483a349fb5691b465b139350399035c8d35ca2c6c91b5c9f26ca2160a1860a0c5e9fb5c9f26c832349e34e9da5e82a349c9549b054a3b5fa335da13578b355a034d9eb479d345822369c15b9b9535a13b9a85b9a0533403b1681397c6896c549935498a548ab5497d6c9256486c6484a6496b5692355924588a45095b6c9526c9496c941609386c93060901508d0508f9508c8508e85c8c0509035c8fa5c8e05c8e85c8e0508d35c8ca5c8c15c9245e89c5d91b5e9125e9095e8f1528d85e8b8528ab5c8a5648646489b5c842648913888934880388783486b498634185a5e8324682a4484b498434183a5e8324682a448015881848810447b1447e0147e14c8025c7f9447f1347e8187d8147cb5c7c25c7a9407b14c7aa5479948791447805873044760147604c7815c77844770347682c7582474b5c7425c728407304c729549845f9745b9645a92c578b4568745385356822566d15f6c15b68157649538094f7d14b7b9477a1434705f4605b420573e8537884f7504b73847720432081f1c81b19017158137125d6ea556e2357035d6eb556da366f4586ec546e3546da5470b456fa456d2376c3476924d6b2455212a6934d6a3455993a6946c68c606786c668606792766a376ab5d69a5d682375913a5192a6705c660506515c6095463944601345d8185c8146424d60a4563a3562a3f622376134a60b46602465f23b5ea375da375ca3764b4763146619445f9365e1345d0185c0145b46c5a96c571645693459a5d5612658a5d5725557b5a5735656a56561565a357592564c2365815655936230251501154a4d5112a228271481153b6c5316c4f1644e9445235d4e13650b5d4f3554fc5a4f4564eb564e15652c5751a5651246501564d9462d845140114cb4a4c14a2c847138114b25d48a55482354a35d48b5547a364945848c544835447a544ab4549a4547237463474324d452452a02a4334d443453383a4346c42c604196c409604192740a3744b5d43a5d422374115c401503303a2982a3f05c3a8543d8443a0343782c368243e24d3aa453da353ca3f3c2373b34a3ab463a2463923b38a3737a3736a373eb473d0463b84439836380343702c360243546c3486c310643083433a5d3002632a5d3125531b5a3135630a5630056343573315622136320562f8362d1251301212810120102e3502db482d25c118102ea4d2c9272902a110122bb6c2b06c27064268442a35d2603628b5d2735527c5a2745626b56260562ac57299562914628056258462394510812100100f8102435023b482325c0f01024b4a229472204a0e8122115c1e9542024d1ea451f34a1eb4620b471f9461e1361d05c1a8541c24d1aa451b34a1ab461cb471b8461a0360d810193470d0101806c090640c054088441706c048640b054030340e0140d9241605c0385407844028340f9241524d0f12602026129441434a11946070461212412a381214c1324d119260182610144102380f94c10b4a0f146068460e04c0da370cb5d093550c3450ba5d04a550b24509a5c0a45a0945608b560824d03a4507a3507126068260535c05b5a04b560434a03b460325602a46021460184617c5716b5715b4714a4613a36111460e9360d1240a8560604601036acb4fa6347a424f99a4771a376c94f6b94b659475b9435513b541374d12b4b9274684f4584b3f847358432f03b2c0372502b218271d81f1981b18817008130001f 15 5 11 9 6
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsF m_49 g_49 bds_49 (dagRefF 347 (dagTraceF m_49 s_49 8 f_49) l_49 0) s_49 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_0 : treeBlockF 0 32 (dagCheckNodeF m_49 g_49 bds_49 347 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_1 : treeBlockF 32 64 (dagCheckNodeF m_49 g_49 bds_49 347 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_2 : treeBlockF 64 96 (dagCheckNodeF m_49 g_49 bds_49 347 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_3 : treeBlockF 96 128 (dagCheckNodeF m_49 g_49 bds_49 347 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_4 : treeBlockF 128 160 (dagCheckNodeF m_49 g_49 bds_49 347 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_5 : treeBlockF 160 192 (dagCheckNodeF m_49 g_49 bds_49 347 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_6 : treeBlockF 192 224 (dagCheckNodeF m_49 g_49 bds_49 347 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_7 : treeBlockF 224 256 (dagCheckNodeF m_49 g_49 bds_49 347 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_8 : treeBlockF 256 288 (dagCheckNodeF m_49 g_49 bds_49 347 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_9 : treeBlockF 288 320 (dagCheckNodeF m_49 g_49 bds_49 347 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_10 : treeBlockF 320 347 (dagCheckNodeF m_49 g_49 bds_49 347 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
theorem nj_49_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_49 g_49 bds_49 347 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_49_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_49_1 h1 h2)
theorem nj_49_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_49 g_49 bds_49 347 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_1 (fun _ h1 h2 => treeBlockF_at nb_49_2 h1 h2)
theorem nj_49_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_49 g_49 bds_49 347 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_2 (fun _ h1 h2 => treeBlockF_at nb_49_3 h1 h2)
theorem nj_49_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_49 g_49 bds_49 347 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_3 (fun _ h1 h2 => treeBlockF_at nb_49_4 h1 h2)
theorem nj_49_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_49 g_49 bds_49 347 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_4 (fun _ h1 h2 => treeBlockF_at nb_49_5 h1 h2)
theorem nj_49_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_49 g_49 bds_49 347 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_5 (fun _ h1 h2 => treeBlockF_at nb_49_6 h1 h2)
theorem nj_49_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_49 g_49 bds_49 347 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_6 (fun _ h1 h2 => treeBlockF_at nb_49_7 h1 h2)
theorem nj_49_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_49 g_49 bds_49 347 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_7 (fun _ h1 h2 => treeBlockF_at nb_49_8 h1 h2)
theorem nj_49_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_49 g_49 bds_49 347 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_8 (fun _ h1 h2 => treeBlockF_at nb_49_9 h1 h2)
theorem nj_49_10 : ∀ i, 0 ≤ i → i < 347 → (dagCheckNodeF m_49 g_49 bds_49 347 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_9 (fun _ h1 h2 => treeBlockF_at nb_49_10 h1 h2)
theorem nc_49 : ∀ i, 0 ≤ i → i < 347 → (dagCheckNodeF m_49 g_49 bds_49 347 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := nj_49_10
theorem lb_49 : LowerBin m_49 s_49 g_49 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_49 sub_49 gl_49 rc_49 nc_49

def m_50 : Nat := 0xff00ff00ff00ff00
def s_50 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_50 : Nat := 0x100150015005700
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 7, g_19), (m_21, s_21, 6, g_21), (m_23, s_23, 6, g_23), (m_30, s_30, 6, g_30), (m_40, s_40, 6, g_40), (m_20, s_20, 5, g_20), (m_22, s_22, 5, g_22), (m_29, s_29, 5, g_29), (m_38, s_38, 5, g_38)]
theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_19
  · exact lb_21
  · exact lb_23
  · exact lb_30
  · exact lb_40
  · exact lb_20
  · exact lb_22
  · exact lb_29
  · exact lb_38
theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_50 : Nat → Nat × Nat := unpackForestF 0x63314cc523909223310cd824590c42330d0b43104c01f 4 10
def l_50 : Nat → Nat → Option Nat := unpackLinksF 0x3cf1d3a30d9b1464c882e4701 0x204d433810e42488cd824590cc342d0f233b4ce92370cd023104c01f 7 3 10 4 4
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsF m_50 g_50 bds_50 (dagRefF 13 (dagTraceF m_50 s_50 8 f_50) l_50 0) s_50 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_0 : treeBlockF 0 13 (dagCheckNodeF m_50 g_50 bds_50 13 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 13 → (dagCheckNodeF m_50 g_50 bds_50 13 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := fun _ h1 h2 => treeBlockF_at nb_50_0 h1 h2
theorem lb_50 : LowerBin m_50 s_50 g_50 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_50 sub_50 gl_50 rc_50 nc_50

def m_51 : Nat := 0xff00ff00ff00ff
def s_51 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_51 : Nat := 0x170037001700ff
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_39, s_39, 5, g_39), (m_41, s_41, 5, g_41), (m_11, s_11, 4, g_11)]
theorem kn_51 : KnownBin bds_51 := by
  intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl
  · exact lb_39
  · exact lb_41
  · exact lb_11
theorem sub_51 : ∀ b ∈ bds_51, m_51 &&& b.1 = b.1 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl <;> decide +kernel
theorem gl_51 : ∀ b ∈ bds_51, canon b.1 g_51 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl <;> decide +kernel
def f_51 : Nat → Nat × Nat := unpackForestF 0xb4f0b4bc25cc2500b47a238a234a1340b430a4f0a4b0a475b545a4c6a445a4459240a430a3f0a3b345834500a37125c125411240a33001f 5 11
def l_51 : Nat → Nat → Option Nat := unpackLinksF 0x1e0f0783c1c2e07038193c86430371b85c2c3609248241209040a01008034c3801 0xca5cc250b238aa34a1347a406a346a447b54724c624459243c583450225c1a541124db4fd34bbb479b43924f8a4b824752434a3f423b2a370a33001f 9 4 11 5 5
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsF m_51 g_51 bds_51 (dagRefF 28 (dagTraceF m_51 s_51 6 f_51) l_51 0) s_51 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_0 : treeBlockF 0 28 (dagCheckNodeF m_51 g_51 bds_51 28 (dagTraceF m_51 s_51 6 f_51) l_51) = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 28 → (dagCheckNodeF m_51 g_51 bds_51 28 (dagTraceF m_51 s_51 6 f_51) l_51) i = true := fun _ h1 h2 => treeBlockF_at nb_51_0 h1 h2
theorem lb_51 : LowerBin m_51 s_51 g_51 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_51 sub_51 gl_51 rc_51 nc_51

def m_52 : Nat := 0xffff0000ffff0000
def s_52 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_52 : Nat := 0x117000015170000
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_42, s_42, 7, g_42)]
theorem kn_52 : KnownBin bds_52 := by
  intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_42
theorem sub_52 : ∀ b ∈ bds_52, m_52 &&& b.1 = b.1 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_52 : ∀ b ∈ bds_52, canon b.1 g_52 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
def l_52 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsF m_52 g_52 bds_52 (dagRefF 0 (dagTraceF m_52 s_52 7 f_52) l_52 0) s_52 7 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_52 g_52 bds_52 0 (dagTraceF m_52 s_52 7 f_52) l_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_52 sub_52 gl_52 rc_52 nc_52

def m_53 : Nat := 0xffff0000ffff
def s_53 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_53 : Nat := 0x1537000057ff
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_30, s_30, 6, g_30)]
theorem kn_53 : KnownBin bds_53 := by
  intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_30
theorem sub_53 : ∀ b ∈ bds_53, m_53 &&& b.1 = b.1 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_53 : ∀ b ∈ bds_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
def l_53 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsF m_53 g_53 bds_53 (dagRefF 0 (dagTraceF m_53 s_53 6 f_53) l_53 0) s_53 6 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_53 g_53 bds_53 0 (dagTraceF m_53 s_53 6 f_53) l_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_53 sub_53 gl_53 rc_53 nc_53

def m_54 : Nat := 0xffffffff00000000
def s_54 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_54 : Nat := 0x117153700000000
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_42, s_42, 7, g_42), (m_31, s_31, 5, g_31), (m_33, s_33, 5, g_33), (m_35, s_35, 5, g_35), (m_36, s_36, 5, g_36), (m_38, s_38, 5, g_38), (m_39, s_39, 5, g_39), (m_6, s_6, 4, g_6), (m_7, s_7, 4, g_7), (m_8, s_8, 4, g_8)]
theorem kn_54 : KnownBin bds_54 := by
  intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_42
  · exact lb_31
  · exact lb_33
  · exact lb_35
  · exact lb_36
  · exact lb_38
  · exact lb_39
  · exact lb_6
  · exact lb_7
  · exact lb_8
theorem sub_54 : ∀ b ∈ bds_54, m_54 &&& b.1 = b.1 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_54 : ∀ b ∈ bds_54, canon b.1 g_54 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_54 : Nat → Nat × Nat := unpackForestF 0x5a7e634e016978c97319286315cc62a18c17005a3e0a3fc146f824ff049b80b43bd6a77d14af5a480a4fbb0480292ee5a880a4701486028fed52f00a3b9e8b13d14ab09fd613baf099584deb40a561339e8a13c53278a053848a70893ed3e7da5cfb479f6873e0fe7c1dcf8379f0673c130051bc4b5e894bd1493a28a7c514b960b92c14228a3c9818930291450e280fc501b8e4b11c942280bc61408b2491404e241200a338047f008ee12304204c8046f029b20412402330129ee8d3df49a3a34b79ac0f2571e42e3a34776268ec0d1d1a1ba14e0129696d712da8b5a3f6b476dc131ad1bb60246b46696d412d2e25a50678c0968fd92303226c4b476b91817228304505c6c0bad7175282e04c4b46ea918151362c350544b8aad4154a82a0244b466984bd3095a7b504f6809849d34ae261234b0b80251c81a7a413420696875810cae22044430b840d1cfc9a2002c3f06840d0ced269e4503b48a40538851f90a3b358a06a130d42010a37320506409085199083f210765a930b520108372a078540d084199082f210564ad2095a01082723460444d0841190014012863114c75a88c35e1b6a83097c640a0c1520127e2c050049d8a4520126e024cc452f0092f0f29c024ac35a4024530a8a21493811a902c52054bc0c0901529023420124e0405004918001f 8 11
def l_54 : Nat → Nat → Option Nat := unpackLinksF 0x242190824019002400900240090023658d063408c86320891e221888220186121808586160850614083120c080960207e91fa07e81fa07d89f607c89ea47a81ea07a81ea07989e607981e607981e607981e6073b1baa6e05b426d01b406d01b406d01b026c01b006b09ac06b01ac06a85a436901a21680586d5e1d7805e017805e017425d017405c096845a0168059856605981660580d60058015c2570152554814a452814a0528146251814224e913a04e813a04d893604d813034b852a24a812624981260480d165448910144010e143810e0420cfe53f80fe03f80fe03e88fa03e04f043728d823600d423408ce13380ca23014be12f80ba22d0cb402d00b212b88ae02b80ae02b80ae02a0ca802a00a422900a402900a402808a0028009c227009c027009a1250c94024849011db468719846601904640188462018045841600561158054115005401484520140450012104801200423108042010804010e8c3430d0032100e0001 0x3322f6634eca4b99294320ae63950c60b97cd7075b65fa5fc447f868dc78a7e113fc126e1849efa2c5f452bf6a77ad2671190d13fbb04972d461cafbf15b662ae9254ed52f4315f7c2b6c655d1ca9c295d7b2b2c255518a8b0450af09878572b40a5893fb02775c4deb099d4048a70894cd3e95a5d2347a36870813de425ae04743087440fe841dd00379f06767162ca2955c50832bef056d6caba1153aa2995250278264d024822baae5565c2e4b0509403126052301047a588e4a11604230a0459249a49d3253e60a5ca947922870213dd825aa0473f0872207e400dc68178a02738d7a6d2f4015f752b6a655cf8a9c4824858c1081320936408248747f0c8ee0d1bc02337d268f7581e8ae3c85c77268ec0d1f9a7be34b7868eead0dd0a733a4d65492be9156920b04506e098b0971b0123823f6f476da8ddad19b3c60520d8cb18191362886c50078c11413c2e304505d098bcd7141a82ea50628c0c31417db02706c5c098b097158122684c586a0acd4134ae2a9505a8c0b29b15d2e2606c54048a0d413da02695c5225ea24ad3893a6123726b8e2d45a9a834a5c684a0cc8fd8d1dada375346696170f4ae1c8144826870050f0ae1b814360986c131102223560452b8765310c2e1a01432048800b0c812209343f06862050f2281ea4d3b48a6f140d8261a8403305064090b92616a402b078540d08c181334825680440808d18111343947e708ecd11b98a331927c600fcbc1d9603729066500bc9c15920272104692d3d1da5a13473e68630938e8a7100141d8d83ad446daa0c8141e8a638d78692f8c1521602829148452f0794e0b6c010d4035a402b400b8a214938152103024088a40e978152906453096a408d08080a66b4fcb6978ad1f01a1de24fba4977091edd21db23fb44773a8de2119bf94f732969451c7ca18b93f15276264dc48998812f0e2560649c04918001f 14 5 11 8 6
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsF m_54 g_54 bds_54 (dagRefF 206 (dagTraceF m_54 s_54 8 f_54) l_54 0) s_54 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_0 : treeBlockF 0 32 (dagCheckNodeF m_54 g_54 bds_54 206 (dagTraceF m_54 s_54 8 f_54) l_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_1 : treeBlockF 32 64 (dagCheckNodeF m_54 g_54 bds_54 206 (dagTraceF m_54 s_54 8 f_54) l_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_2 : treeBlockF 64 96 (dagCheckNodeF m_54 g_54 bds_54 206 (dagTraceF m_54 s_54 8 f_54) l_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_3 : treeBlockF 96 128 (dagCheckNodeF m_54 g_54 bds_54 206 (dagTraceF m_54 s_54 8 f_54) l_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_4 : treeBlockF 128 160 (dagCheckNodeF m_54 g_54 bds_54 206 (dagTraceF m_54 s_54 8 f_54) l_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_5 : treeBlockF 160 192 (dagCheckNodeF m_54 g_54 bds_54 206 (dagTraceF m_54 s_54 8 f_54) l_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_6 : treeBlockF 192 206 (dagCheckNodeF m_54 g_54 bds_54 206 (dagTraceF m_54 s_54 8 f_54) l_54) = true := by decide +kernel
theorem nj_54_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_54 g_54 bds_54 206 (dagTraceF m_54 s_54 8 f_54) l_54) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_54_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_54_1 h1 h2)
theorem nj_54_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_54 g_54 bds_54 206 (dagTraceF m_54 s_54 8 f_54) l_54) i = true := block_join nj_54_1 (fun _ h1 h2 => treeBlockF_at nb_54_2 h1 h2)
theorem nj_54_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_54 g_54 bds_54 206 (dagTraceF m_54 s_54 8 f_54) l_54) i = true := block_join nj_54_2 (fun _ h1 h2 => treeBlockF_at nb_54_3 h1 h2)
theorem nj_54_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_54 g_54 bds_54 206 (dagTraceF m_54 s_54 8 f_54) l_54) i = true := block_join nj_54_3 (fun _ h1 h2 => treeBlockF_at nb_54_4 h1 h2)
theorem nj_54_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_54 g_54 bds_54 206 (dagTraceF m_54 s_54 8 f_54) l_54) i = true := block_join nj_54_4 (fun _ h1 h2 => treeBlockF_at nb_54_5 h1 h2)
theorem nj_54_6 : ∀ i, 0 ≤ i → i < 206 → (dagCheckNodeF m_54 g_54 bds_54 206 (dagTraceF m_54 s_54 8 f_54) l_54) i = true := block_join nj_54_5 (fun _ h1 h2 => treeBlockF_at nb_54_6 h1 h2)
theorem nc_54 : ∀ i, 0 ≤ i → i < 206 → (dagCheckNodeF m_54 g_54 bds_54 206 (dagTraceF m_54 s_54 8 f_54) l_54) i = true := nj_54_6
theorem lb_54 : LowerBin m_54 s_54 g_54 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_54 sub_54 gl_54 rc_54 nc_54

def m_55 : Nat := 0xffffffff
def s_55 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_55 : Nat := 0x151757ff
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_40, s_40, 6, g_40), (m_32, s_32, 5, g_32), (m_34, s_34, 5, g_34), (m_37, s_37, 5, g_37), (m_41, s_41, 5, g_41), (m_43, s_43, 5, g_43), (m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5), (m_12, s_12, 4, g_12)]
theorem kn_55 : KnownBin bds_55 := by
  intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_40
  · exact lb_32
  · exact lb_34
  · exact lb_37
  · exact lb_41
  · exact lb_43
  · exact lb_4
  · exact lb_5
  · exact lb_12
theorem sub_55 : ∀ b ∈ bds_55, m_55 &&& b.1 = b.1 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_55 : ∀ b ∈ bds_55, canon b.1 g_55 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_55 : Nat → Nat × Nat := unpackForestF 0x25028928045005a7802d2e3c4b9260258f128c7e4be3f24f1f82f8fc15c8c4f23f04f2013490c1248015241049200248fc11c789423d4b31e05d005a3c648e232469191348c81c4640d63305f1a3408cc13c640d001687179448bc2280293c014970db5c8ac1ac36d461e27f0f1378781fc3c0ee252990f03787ca24440d21f0a91003487c1243c0ce1b6a10e35986c2e80291e1149908a44844924220a21104b0901f84d1842405e1104800a4383c1a8028fe0c47d060250051dc141340146f040358191ec0c0f5d8688ec25b80c12bb0969d84aeffc5e7fc2ebb0959fd498fe45476097bf5151d824efc24c7de2a3b00bdf4298fa04c7ca2a3e44f1d8056f7b4c7bc263d9151ed688f613c76013bce969e725cf415479c913b0095e5098ecc54789a23c40b1d9268ef34477d1a3bc091d90c8ed34476d1a3b4091d9048ec0230051980253dd5258ea02574919ba451801294e8239719a8b9c939c64a2e3c6071db038e9b1c9048e3a6071d2a38c8cc0128ee21296d121b844f9b4286dab526d52936a579bd028da9526d4a2b708c9b8264dc04d6d4a236c541b502ada123004a3364945a36acd1a5b6ba3035cdb1a34aed1a4f68d21b48d69a96a0d2356691a7348d09a44b4d225668d1c8024fda1482009376422db3ad819d4d8c8457641a5b20d0d996a2c82566462d32c941918acc8b5a645ab32292591482c824e00497b1cd080124ec595462ca200213d88268c40345f9a1afc9697e0acc1a4160d1cafc1397f684bfa4e5fd212fc0f801096b035b581a9af48e5606a2b025b58129aec939604a2b64605b1b02d89b16c4c8b62605b12a2dad416d4a0b602458119ac05296028cb0a3b58519ac24ed61266b114c588a22c405161246b014400423ab41315a088ad03c5681a2b4090010868f45a54daeaa694554054aa02654d2823d1591e6b6a7b4d53d1ca3cd694d8b08f35752a2f2949451e6ac8f25b5163028adb1456c08f25747927a849191e4928f2434f12d2789593c0549e02647920a740d11e47e9bb504dda623c8ed2f6b49a3504bdab25ed392f68497a5a4bd2b23c8e52d4808f2374ad26252d11290488f23349920a4c8e51e2b49214448898a444a51e2ac8fc6047daa23c15c0107e8d03e4681e2340d0010768aa4145d26a2a8c515298008373f1ada24511108c08806c3f1aba1c510fc69e861343f1a19f8969084a2842453f02b20c904fc09c7eb5a40da81fad58fd69c7eb423f52d1fa958fd2b47e03e0041995b16cf76c07ba6c3dd3015b15cad6b4783513c81d1e40d8f06a07825d2b5ab1dc8d4ad69c56b4b2b5a19ce968e74ac7382a39c1315ad08ad4b671a4e38d1e95a968e16b056a5737a2f1bcd44ad4ac6e3502b5279a9168d94a06a456351ad1a8d58d44926a2412b5271a2d70d104856a4b33da015a91ccd49865b5432c1215a90cc34b461a5630d269868f4c42986213c30c1315a908bf6845fa4e2fd2115a568bd2885ca322e49f174510b9264569562d9b016c950ad0ae593502c9a4164970ad09e573502b9a015c930ad08e0082f2a427152130a90880082b26da114c8f49b4844d93c285a8142940a14904d84f271a8138d009c4a04e24026c2380209c7f8b64c134259b012c1b07f8ae4a1341fda59244d07f6863fa5a239a891cd147f0ac4245a22d28109158846b44235621124908904844724215a1fc27100d088049c402421fc1f00208c7d0a822c5f1162d8f0db0786c03c06c1162b8e6d2073688399441cc2208b14c710a822b5f115ad8d91b06c8c03606c115ab8ced70676a83393419c1a08ad4c6508822b4f18c1a08ad2c610b822b4717c260b91505c2682e034115a18b2d44594a2228561422d0ac940508ac2835a141ab0a092450482282391142708cd684d6a023356119a708cd08464b4232561192708c9084507c0081b10d2c00517c028b61f36c0f9b007c980028ae1cb480e5a207292039088014530dd2c004d7c026b61946c0ca30064980026ae16b5c0b5aa05a8e02d068013530ad24004d3c294700134b09d28004d1c228a8123440891c0440d00268610238074a703c9301d27c0125a04a2f032d101908809452049a6824d14122b40a250048ab0244f80248401b5e039a201c0d0036a401b4a00da3006568096a00195600ca7008d10054680215400ca10048c80102e0001f 10 11
def l_55 : Nat → Nat → Option Nat := unpackLinksF 0x436021b010c8485444280a138308468400c20020f83078183c041b0e0c8506408300c18020b8304c48144c0a020404ff8a7f813fa09fd00fe807f013f801fc00fdc17ea13ed21f680fb407d223e121ef84f7817b033d705eb80f5817aa0bd501e906f4027a003cf05e780f38179423c125e080efc276a53b309d884ec4076203af09d780ebc075c0bac09d210e804730439411c808e20870e0b8311c180e0426fa237329b902dc806da2b6b09b580da816c4436201b082d7836bc035d05ae80d7016ae2b5701ab80d5426a80b4f15a780d3c0696234b01a502d106688034401a200d0c16668333019788cb4265a0329119402ca0064e0b25099202c9006460b21098d0ebf1e5f60afb017d02bd845ec02ee217700bac35d602e80d7400ba005d002e8017382b9c05c42adf0d6f80b7035b802d90d6c02b5c15ae02d7016b02b5805ac02d6016b00b4065a002cd0d6116ae8857402b8095b04ad4156a02b20d5882ac0156002b0015782abc055e02af015780aa4654632a3015102a80253e0a9f014e06a6c15340a9a014c04a6005300297054b80a5c052e029701488ca2c6516028a054500a28050e1a87014380a0855040282014100a0804fe1a7f013f809fc04f81a77153a069c824e4026d1535069a024d0026315310298414c00a5f052f8097c04be025f012e0694c94a6025301298094c04a6025301298094c04a602500d258a8f4e47a023d011e808f4047a0238151b048d8046c0236011b008d024621a2f0917808bc0456222b0114848a40452022511108888014400220010e088604430021609098684c04240a12010900820a410020411020080c14001a000100007fc13fe01fe04ff007f803e461f200f7867bc03dc09ed04f4887a403d201e60cf30079413ca01e20cf10078803c011c95ce480724039201c60ce108708037c21be00dc0c6d8236c01b408da006c0436001ad0cd6806a4435009a800d400694334a01a20cd100688034209a100d080684034201a100cc126408318218b04c58062c030e218508c280614030a018308c1806003300017e08bd085dc32ee017604bb005d802d8516a08b5005a802cc216600b20459002c8016010b00057432ba015d00ae0257002b8015c00ad8253cc29c094e00a508528028e194700a3025141282214100a0024fc127c093e009f004f0226451320099004c8025e192f0097024b8025c012d0495064a8025401280894004a002500124109200490024801201084ae42402120109008306408420400fe107f003f801fc00fe007d083e801f400fa007d003d841e030ee0877003b021d800e810740039431ca00e110700238001c000dd0c6e8037401b808dc006e0037001b800dc006e0034c91a600d3006980340319040c8006382314218a00c4046200300418000c0006000300017820bc005d822e4217200b8045c002d0416800b4005a002d0016020b00057042b8015810ab0454842a4015008a8005400288614400a2004f08278013c009d044e80274013a009d004e80254812a0095004a0225001280094004a002500128008c203e9e1f400f6107a043d001e800f400770c3b801d810ec007504380a1c000dc106d0436801b400da006a0c35001a410d2006804318a18c00c21061002f8417c00b62059082c8016010b00054102a0014c10a60052042708138009c004e0026041300096084b00258012810940042202100108008400400820000fc107e003f001f020f8007a083d001e020e8206440233c00c40001 0x251289280451f00d88405e02462cf92f56026a9c0f4fa05e4c8231ec0d88205c7a036200172601833c4f55609a7c83d25c189ee0b64c04acb24c365262aa53246278aa04c910104861124102921824904124884d2420a84584c900124944be4924ea983d92017c8e0ae4504f1f8231e40d87e05e3d4b27ba519352e4969463e4a0ce12f8f02eaa40f4f605e4a8231dc0d87a05c760361e0171d40d87605c740341c8168d1a046a0be3304f1d2388e51a4704d2370711b0358c81a0e406c3802f181448bc228e006c3602f012426c0a7a9013d130867a83d388168de06c3502e3701b0d00ba24101af29aa384d44420a8a0f62b06a7a02d6a51c2688e0f32791294c88c181e40b222089100148881a4400d2232891085440c1e43e0922927f1413789c1fc4c0ee2406f0f0333c4168da06c3302f0e359515a8c58d722a6a30eb506b49fc361754407e878333bc168d606c3102e3501b0c00b8d206c2f02e3401a0b40b4268c21403f0901786526430912172490b02885412c220906603616017201a7102d093a09c87042835a735853d4309e8684383c1a9da0b46403615017418269040f48005a4f8252011f10a8c8d107c4a0328351f3364fd4109a7603f24c19c1809462036140178191840a8c20a09a3001b0980bbe00f60806af823d7d11abea0a9ef04d03a3d7f097bf449e0607afb82f7cc15bdc09de40462f01b0940bc00d92004aa9f84d3a81e9920b60304b002586ecaa370512008bce39456dca23fe175710aab78454f81e9d20b5fd498fe4546452e34c931fa8a8fc24c7de2a1a897131498f903830c1a3ea531f4098f10247ce2a27a570e8298f913c27c1a3e0d31ed278f784c78c103dad11ee8a8f613c4f02e1ce130c3058f08207a0aa3d4969714acea15a6d4ab3d24b9e7244c485a5b02b2521390c0846583e248191860b88005a2e81a0880b3c64d1e00a8f284c770123be111db028f1b447782a3c40b1da028ef82477d1a3c0d11de048ed82476d1a3b8d11da048f24547849a3ba190860b88004c2001e3b2092056890225b8092d40295dfe4ace995a718abb68559ab29ecd13f7ec97bf249d870b6b585750027a761351608a858433ac1f9cc0f4a506a488337d8179840b5f1056f582779812bb008c5b03610817748a23aa4b12709a6083d2fc16ba8095d3466e914661825ad411d2507e850332f81792008dcc482e823972118b96d09ce49ce424272412399181cb6c0e526c7213038e951cf6a2e6a5171919b804c5c4252de1216fd193844f9bc264dd1446e4a237a051ba464dc9326e026ac61152405a5e81d6d8a82c651162088e03526fd2937c579bc2a4dd9456dca22c21152307a5e02d2e40eb6a055c3486e09436d091b180f56906eb00354841797007da54b2d92516a9a434a921a9490d7c606b9b63508e1a7490d33486a5a8354d69a86acd3b4e699a134a969a44acd8b566c12db5a95dac49ed5a4368d1cb42905974b8ca24c659a633cd819d4d8caa4c649ae322d71946b2ccb516592832f169958acca35a64dab32492591482cfc5b6722bb36d2d9a686cc2566412731cd098c2a8c594461422b124d1840b8c084c5fc1e3100d184482c1a395fd18b02d098049cbfa4261da1b0c969850acc104e5f81f2a11811f6a8b4154542342ce5515069aba2415e91cae08c52009a71b602d92a2cc550e36d0b29545cda12ec9397048471a3d2dc1eadc0916d048b215458ca22dcd416d4a0b10445d2302e6d81724d864a685c5322e09816f4a8b09545b0122c853163288b10145a11dace8cd66276b293358491af8d6d4e6b2bdb535e5a8af096ce24b2bba535d528ad68cd6a294b4946580a223c0fcb505eaf04c574222b80f15b068ad0245362aa7e8c555054aa02655daeaac945534a0a5c64481ae296d555069aa7a3932518a9b1614b6b0a5c5e4c12ca949451f08a9ab484fd28260920c94809a24851e3028cdb1456c099a38419ae100d31324909d0345092320c8f931690402404a4122485113869496b464fd2d27c959272b4919562d01e9440d53d0549e02628dae100d31374909d0344ad1a270d4137698633404d1a8188091356b499b564c9a7262d09304b497a562011f18c8f5262b4911562cc1e9420d4856b896a404a918256930c4470633484a9a21649712904893a414991c97e8c5242889193148894972485208c08fb545622d2a5159516b6a735a531aba92d59484b6a225750d27a82925404869da414e51fa6c8ed2e472962374a1199848c5252b4909564782b9620bca004e8e03e46c1e2340d0b007a4e8352001693e0951749a8304d2bc1e9380d5184828b231454a620a134ad05e4d827410261fe0f1122888183c446302201b1080a88103c438a210211101078861344182e200130800787e83e3fd2ca129450848a832412151c9008c5036a08235a409ab202d39006847fa5a3f92b102938804847e95a44dada1ed5d0d69e85b434292d20e1590509c7e03e3a9a01b4970d749864a40365a61f2d80f84d87ba60361261c2d54ea4847983a3c81b1e8d44f16a07825d209a71dc8d4d56b84124c2011e1a2090d46b84023032c1217a510dc69a67b453a92d1d2958c12b45e1562d02695e114e80547382637db216e930df4aa7224e325211c68f4e16b06fa5837e2f1aed64de6a25b045371a81a4960c74a06ca50314121b5168d88ac6bb5a359ab100d38c769a6aa4935120980568bb2ac5904d2b82299a910d26b85824c2011e1a2090cf68040a5c3312019a930c549863b5c331aa166930cb0485d14431412188090c52986213c3252d1909588149c63a4d2151f18c8f4bf2b45c95630c1313e094c16846024e2fd2117a510ba2885e2322ec9f1724c8b76c05b2542d1a8166d20b24b8402402c1a815ed00804a05724c3ea2d9ed15cf56b477b563b5a71d8d2ceb686733423952d9c4968e04ae6ea5636d279a6938d04966724732921984908be2b45c1562d42b96213cad08e5584e2a826152110a309a4f0452001693e094a647a5104d270229040f4a36a040340289281429209f6a04f34027528138900a768452a422909e14013c9b08e3f83d2302e112130982684584c25db012c1b08e0a84504c2509a10e17085068491342182e104130800784204e225ac91ed448e68a45a502322d115158896b44435621d2490c9048547240231210ad104d088149c402422662d92b15c9369648b432412d11a1588309c3f83e1f42a0ae170540982b04c1e9b60f2d80780d82a84c1d9a40ead1074288398441c42a09c130490782683c1ba360db1806c0d82603c1a9ae0d2d506826833834194220960f0520b83183417d180bcd00610b82f84c17a2a0ba4d0510b82504c1181e0b80d0546b22d3511252c8b2944564a02bc5a1562b0a8d68536ac29249145208a08e44646226b50139ad098d584b69c253421252d0909584749c232421f22f8f716c778ae394531c1af8ded6c6b6ae33353191a78c4d2c6068e2db431602b09e1384507c21a5806d2002a900406d81fb600f930034900192801e3480eda20309403a4901c8440dd2c0208c00a4601a46c0ce300649800f460071300c1ae05ed500d480172380b41a02e9402b490062400a51c04ad00274a00b24002d180488e006460123440962a0468e003460110340811c03c9301f29c0a9420749f0144c81a6880c844018980289401b8bc0c45205da682cd14152b4099560489f0064c80f6880703401898012d400528802a34019a2008550106bc06b52031a5016d180a2b40415601ca7006508428be20c5b0f62b87114c366be1ab5b0c5ab858d4c2a69e1434b099a3842d0c1c4b408a420091949ed3e4e6971db478c5a1c5c93e2d4970d24784121c1c8fe0b47704a3775d19bac53dd1294e29476cca33444fda026ec792f63493b1413d7d096af84756421a3a0fd190768a0373ec199580bca80564d0271f81188806c0102e0001f 17 6 11 10 7
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsF m_55 g_55 bds_55 (dagRefF 594 (dagTraceF m_55 s_55 8 f_55) l_55 0) s_55 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_0 : treeBlockF 0 32 (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_1 : treeBlockF 32 64 (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_2 : treeBlockF 64 96 (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_3 : treeBlockF 96 128 (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_4 : treeBlockF 128 160 (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_5 : treeBlockF 160 192 (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_6 : treeBlockF 192 224 (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_7 : treeBlockF 224 256 (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_8 : treeBlockF 256 288 (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_9 : treeBlockF 288 320 (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_10 : treeBlockF 320 352 (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_11 : treeBlockF 352 384 (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_12 : treeBlockF 384 416 (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_13 : treeBlockF 416 448 (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_14 : treeBlockF 448 480 (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_15 : treeBlockF 480 512 (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_16 : treeBlockF 512 544 (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_17 : treeBlockF 544 576 (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_18 : treeBlockF 576 594 (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) = true := by decide +kernel
theorem nj_55_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_55_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_55_1 h1 h2)
theorem nj_55_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) i = true := block_join nj_55_1 (fun _ h1 h2 => treeBlockF_at nb_55_2 h1 h2)
theorem nj_55_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) i = true := block_join nj_55_2 (fun _ h1 h2 => treeBlockF_at nb_55_3 h1 h2)
theorem nj_55_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) i = true := block_join nj_55_3 (fun _ h1 h2 => treeBlockF_at nb_55_4 h1 h2)
theorem nj_55_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) i = true := block_join nj_55_4 (fun _ h1 h2 => treeBlockF_at nb_55_5 h1 h2)
theorem nj_55_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) i = true := block_join nj_55_5 (fun _ h1 h2 => treeBlockF_at nb_55_6 h1 h2)
theorem nj_55_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) i = true := block_join nj_55_6 (fun _ h1 h2 => treeBlockF_at nb_55_7 h1 h2)
theorem nj_55_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) i = true := block_join nj_55_7 (fun _ h1 h2 => treeBlockF_at nb_55_8 h1 h2)
theorem nj_55_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) i = true := block_join nj_55_8 (fun _ h1 h2 => treeBlockF_at nb_55_9 h1 h2)
theorem nj_55_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) i = true := block_join nj_55_9 (fun _ h1 h2 => treeBlockF_at nb_55_10 h1 h2)
theorem nj_55_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) i = true := block_join nj_55_10 (fun _ h1 h2 => treeBlockF_at nb_55_11 h1 h2)
theorem nj_55_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) i = true := block_join nj_55_11 (fun _ h1 h2 => treeBlockF_at nb_55_12 h1 h2)
theorem nj_55_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) i = true := block_join nj_55_12 (fun _ h1 h2 => treeBlockF_at nb_55_13 h1 h2)
theorem nj_55_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) i = true := block_join nj_55_13 (fun _ h1 h2 => treeBlockF_at nb_55_14 h1 h2)
theorem nj_55_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) i = true := block_join nj_55_14 (fun _ h1 h2 => treeBlockF_at nb_55_15 h1 h2)
theorem nj_55_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) i = true := block_join nj_55_15 (fun _ h1 h2 => treeBlockF_at nb_55_16 h1 h2)
theorem nj_55_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) i = true := block_join nj_55_16 (fun _ h1 h2 => treeBlockF_at nb_55_17 h1 h2)
theorem nj_55_18 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) i = true := block_join nj_55_17 (fun _ h1 h2 => treeBlockF_at nb_55_18 h1 h2)
theorem nc_55 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_55 g_55 bds_55 594 (dagTraceF m_55 s_55 8 f_55) l_55) i = true := nj_55_18
theorem lb_55 : LowerBin m_55 s_55 g_55 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_55 sub_55 gl_55 rc_55 nc_55

def g_56 : Nat := 0x1171537151757ff
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_54, s_54, 9, g_54), (m_50, s_50, 9, g_50), (m_49, s_49, 9, g_49), (m_55, s_55, 9, g_55), (m_52, s_52, 8, g_52), (m_48, s_48, 8, g_48), (m_47, s_47, 8, g_47), (m_45, s_45, 8, g_45), (m_53, s_53, 7, g_53), (m_51, s_51, 7, g_51), (m_46, s_46, 7, g_46), (m_44, s_44, 7, g_44), (m_19, s_19, 7, g_19), (m_42, s_42, 7, g_42), (m_30, s_30, 6, g_30), (m_23, s_23, 6, g_23), (m_21, s_21, 6, g_21), (m_18, s_18, 6, g_18), (m_28, s_28, 5, g_28), (m_17, s_17, 5, g_17), (m_22, s_22, 5, g_22), (m_24, s_24, 5, g_24), (m_25, s_25, 5, g_25), (m_26, s_26, 5, g_26), (m_27, s_27, 5, g_27), (m_15, s_15, 5, g_15), (m_29, s_29, 5, g_29), (m_14, s_14, 5, g_14), (m_13, s_13, 5, g_13), (m_20, s_20, 5, g_20), (m_12, s_12, 4, g_12), (m_3, s_3, 4, g_3), (m_2, s_2, 4, g_2), (m_0, s_0, 4, g_0)]
theorem kn_56 : KnownBin bds_56 := by
  intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_54
  · exact lb_50
  · exact lb_49
  · exact lb_55
  · exact lb_52
  · exact lb_48
  · exact lb_47
  · exact lb_45
  · exact lb_53
  · exact lb_51
  · exact lb_46
  · exact lb_44
  · exact lb_19
  · exact lb_42
  · exact lb_30
  · exact lb_23
  · exact lb_21
  · exact lb_18
  · exact lb_28
  · exact lb_17
  · exact lb_22
  · exact lb_24
  · exact lb_25
  · exact lb_26
  · exact lb_27
  · exact lb_15
  · exact lb_29
  · exact lb_14
  · exact lb_13
  · exact lb_20
  · exact lb_12
  · exact lb_3
  · exact lb_2
  · exact lb_0
theorem sub_56 : ∀ b ∈ bds_56, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_56 : ∀ b ∈ bds_56, canon b.1 g_56 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_56 : Nat → Nat × Nat := unpackForestF 0x86a558695500c5f8545e8514500c5b83b608396d00c577fa477fa457f94b80a5d80a457f9477f94500c537e35e7e13500b5b7c35e7c2357c13500b537a36e7a2357a13500b4b7836e782357813500b4376b4b76b4300a5f724617234b7437c7436c7234372b4b72b437216d00a576fc6e6fc626fb636f94500a4f6cd626db6c6db5c6cb636c95d00a4769d6f69d6369b6e69b5e6993500a3f60c5b60c5960c5760b5b66a3560b4b653646523560b4363b4b63b4360a5560a4f6256860a476135e60a3f0095f5dc5b5ea445e9445dc535d95e0095b5b4615b34b5bb7c5b343009574ec5b5923f59237589444ec534eb5f56a6c5696c4eb5755c6e4eb4f54b434e96e4e95e52c5b52c534e9364f34b4f3434f24b4f2434fa5e4f2334e934009534646f4646e46467464624bb544636b4a3544a235463634626f48c7c4626747b634624546d7e4623f0094f451443ec6b43a44439443ec633eb6f41d704197c3eb673eb4f4023f3e96e3f4633e9360094b355623ce703cb6c3536b3ab6c3ab5c3aa35353633526f38b4b38b4338570352673736c36b633525d35e723523f00947341442bc6b32a3f32a37321442bc632bb6f3027c3017c2bb672f47e2bb4f2da652da3f2b96e2b95e2c4632b936009432a3642a2652056f293542056b2837c2056726b5426a55205632036e2035e2026f2437c202672337e2025f2236c2025720d6f20d63202350093f1f16415d6f1e15415d6b1d17c15d671c15415d6315b6f1a27c1a17c15b6715b5f1896c15b5717a4f1596e16d661595e15936009330ed6f13a56139560ed6312c6e0ec6311c7e0ec5b10c7e0ec530fb430e96e0e95e0092b0db680156f0cb58015630b46e0b348014630145b09b480145308b430136e07a6e0136306a4406453013620135e0135b0135303d6e013520134301b4b01b4301266009270003f 9 11
def l_56 : Nat → Nat → Option Nat := unpackLinksF 0xcd07340c923240c9031c4c7031c0c513121c407100c403100c28f0a0bcb2f20bc82e66b792da2b606c2bb006be1af82a8ba90aa21a8068aba2828819d2a7219b8a6e09b826649982660979248b920248092024808da63608d823608c8a301889e2208882201870a1c081ae06081820608182060808a0208081fa47e81fa07d89f607d81f417d01f2176b1da07681da07589d60740dd007401d007309c447009c007001bc26d11b406d01b406c09b006b85ae06b05ac06b01ac06a09a806a01a806a01a8069859c562a58a0620588062018806185860618180360018005f857e05f057c05e8564b59016215881620570d5c057015c0560956155815415501521511d40250014004f093c04e853a04c913204c813204b892c14b012a14a0528049851684581141450114044090c243010c04301063418102240810203f88fe03f80fc13b20ec03b00e633980e413900e213880e20370cda13680da03680d813600d613580d413500d403408bab2e80b812e00b612d80b222c80b012c00b002c00ac22a84aa02a04a802984a602904a4023ac8e023808e022888a022048802184860208882020048001c9c7201b886e01b046c01b00682198466017905e017045c016845a016045611580560158056015045401500540140834e00e4001 0x2a13f85d6e872556ba3f869552993f1e9331492b0d12785c5e851452893f1d933843608396d2793f1c933809452693f8125d80a451412a70a4d82a47822456b23f4c14d8194b801477f9452613f1b9331312b0c1277eb5e4b15f4495b3c157339537e1356da553b1551292b0b9274a15f3a9574415a7d35e7025f6d2577ca354995f4315b3a157319537c1351212b0a9271192b6696f7b36e7726f752677aa356616f5f96b5c1675a1637a1351112b0a127742651092b6516f5f16a7936e76a6f73a6778a356496f5e16b5b16758163781351012b091270896d70c517734b76b430815d4914f4294b39947311432493f1b133421597317d0212574b7c7436c7297d019257334b72b43309421a93275c617534b73b437216d4814f4114b379472f9432393f19933011257146e70c62703636296f579630514d6f9452293f191336e36c6db5c571626ed626d3636196f561636c95d2193f181332f1436116f559636bd6f6b5636ab6e6a35e6096f551634615f4095b351572e953699356426566a3565b6408a6d63a65652356434b63b43625686135e68c5b6845967c574c4516735b6634b64b430825d6325562a4f61a4760a3f5f2445e9445fc5b5e4535d95e5bb7c5497d5cc615c34b5b3435416d531365193459a3f592375497e5894452936511345726c5696c55c6e54b435345b52c534fa5e51b4b5134350a4b502434f2335a45b5845357b5f563575534f5416e5395e521364e93446a3f4bb544ab5447a554a23548c7c47b6346d7e4dc6f4d46e4cc674c4624b36b49b634926f482670524d472454623f4514444244439443f136425704197c4017e4023f3f46344c6b4346342b6f4136740b4f3f96e3e9363d36935a3f3d6703cb6c3725d3bb6c3b35c36a6d3aa353934b38b43385703736c36b6335e723dd623c36b3a36339a6f37a673625d3523f2c95d341443323f32a37321442c13630a7c3017c2e16c2f47e2d97e2e2652da3f2c46333c6b31c633136f2fb672eb4f2d16e2c95e2b9362ab642a26521235293542837c2735426a5520a352324f2437c2337e2236c2156f20d6329d6f28d6b27d672656325b6e2535e24a6f23a6722a5f21a57202351f1641e1541d17c1695c1c1541aa7c1a17c1797e1896c17a4f16d661ed6f1dd6b1cd671bd631b36f19b671935f183571716e1615e15936142561395612c6e11c7e10c7e0f97e0fb4314d6f13563124631145b104530f16e0e95e0db6803b500cb580bc6e0b3480227608b7e0637209b4801a7608b4307a6e06a440645303d6e0234b01b430d56f0c5630ac630a45b094530836e0736305b620535e04b5b043530335202b43012668645f84c5b834577f4537db5b7bb5379b4b77b437625f71a576f24f6c2476923f6015f5d15b5a9574e1534594f3e14b349472b1431f93f151330e12b009270003f 14 5 11 9 6
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsF fullMask g_56 bds_56 (dagRefF 271 (dagTraceF fullMask rootStock 11 f_56) l_56 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_0 : treeBlockF 0 32 (dagCheckNodeF fullMask g_56 bds_56 271 (dagTraceF fullMask rootStock 11 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_1 : treeBlockF 32 64 (dagCheckNodeF fullMask g_56 bds_56 271 (dagTraceF fullMask rootStock 11 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_2 : treeBlockF 64 96 (dagCheckNodeF fullMask g_56 bds_56 271 (dagTraceF fullMask rootStock 11 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_3 : treeBlockF 96 128 (dagCheckNodeF fullMask g_56 bds_56 271 (dagTraceF fullMask rootStock 11 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_4 : treeBlockF 128 160 (dagCheckNodeF fullMask g_56 bds_56 271 (dagTraceF fullMask rootStock 11 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_5 : treeBlockF 160 192 (dagCheckNodeF fullMask g_56 bds_56 271 (dagTraceF fullMask rootStock 11 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_6 : treeBlockF 192 224 (dagCheckNodeF fullMask g_56 bds_56 271 (dagTraceF fullMask rootStock 11 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_7 : treeBlockF 224 256 (dagCheckNodeF fullMask g_56 bds_56 271 (dagTraceF fullMask rootStock 11 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_8 : treeBlockF 256 271 (dagCheckNodeF fullMask g_56 bds_56 271 (dagTraceF fullMask rootStock 11 f_56) l_56) = true := by decide +kernel
theorem nj_56_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF fullMask g_56 bds_56 271 (dagTraceF fullMask rootStock 11 f_56) l_56) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_56_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_56_1 h1 h2)
theorem nj_56_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF fullMask g_56 bds_56 271 (dagTraceF fullMask rootStock 11 f_56) l_56) i = true := block_join nj_56_1 (fun _ h1 h2 => treeBlockF_at nb_56_2 h1 h2)
theorem nj_56_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF fullMask g_56 bds_56 271 (dagTraceF fullMask rootStock 11 f_56) l_56) i = true := block_join nj_56_2 (fun _ h1 h2 => treeBlockF_at nb_56_3 h1 h2)
theorem nj_56_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF fullMask g_56 bds_56 271 (dagTraceF fullMask rootStock 11 f_56) l_56) i = true := block_join nj_56_3 (fun _ h1 h2 => treeBlockF_at nb_56_4 h1 h2)
theorem nj_56_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF fullMask g_56 bds_56 271 (dagTraceF fullMask rootStock 11 f_56) l_56) i = true := block_join nj_56_4 (fun _ h1 h2 => treeBlockF_at nb_56_5 h1 h2)
theorem nj_56_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF fullMask g_56 bds_56 271 (dagTraceF fullMask rootStock 11 f_56) l_56) i = true := block_join nj_56_5 (fun _ h1 h2 => treeBlockF_at nb_56_6 h1 h2)
theorem nj_56_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF fullMask g_56 bds_56 271 (dagTraceF fullMask rootStock 11 f_56) l_56) i = true := block_join nj_56_6 (fun _ h1 h2 => treeBlockF_at nb_56_7 h1 h2)
theorem nj_56_8 : ∀ i, 0 ≤ i → i < 271 → (dagCheckNodeF fullMask g_56 bds_56 271 (dagTraceF fullMask rootStock 11 f_56) l_56) i = true := block_join nj_56_7 (fun _ h1 h2 => treeBlockF_at nb_56_8 h1 h2)
theorem nc_56 : ∀ i, 0 ≤ i → i < 271 → (dagCheckNodeF fullMask g_56 bds_56 271 (dagTraceF fullMask rootStock 11 f_56) l_56) i = true := nj_56_8
theorem lb_56 : LowerBin fullMask rootStock g_56 12 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_56 sub_56 gl_56 rc_56 nc_56

def wg : List Gate := [⟨GateOp.and, [5, 4]⟩, ⟨GateOp.or, [5, 4]⟩, ⟨GateOp.and, [4, 0]⟩, ⟨GateOp.or, [2, 1]⟩, ⟨GateOp.or, [2, 0]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.or, [6, 0]⟩, ⟨GateOp.and, [12, 3]⟩, ⟨GateOp.or, [13, 8]⟩, ⟨GateOp.and, [14, 9]⟩, ⟨GateOp.or, [13, 1]⟩, ⟨GateOp.and, [16, 11]⟩, ⟨GateOp.or, [15, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276677320 * 2 ^ 32 + 3941115904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276677320 * 2 ^ 32 + 3941115904)) (13 - 1) := by
  rw [show canon fullMask (4276677320 * 2 ^ 32 + 3941115904) = g_56 by decide]
  exact lb_56

end PEqualNP.Outside.L_meta_48849

theorem PEqualNP.Outside.L_meta_48849 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677320 * 2 ^ 32 + 3941115904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677320 * 2 ^ 32 + 3941115904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_48849.table2_from_lowerBin (4276677320 * 2 ^ 32 + 3941115904) 13 PEqualNP.Outside.L_meta_48849.root_lb PEqualNP.Outside.L_meta_48849.wg 18 rfl PEqualNP.Outside.L_meta_48849.wfits PEqualNP.Outside.L_meta_48849.weval

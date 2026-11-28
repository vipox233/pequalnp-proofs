import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48420

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
def KnownBin (bounds : List (Nat × List Nat × Nat × Nat)) : Prop :=
  ∀ b ∈ bounds, LowerBin b.1 b.2.1 b.2.2.2 b.2.2.1
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
def lenN (l : List Nat) : Nat :=
  List.rec 0 (fun _ _ ih => Nat.add ih 1) l
theorem lenN_eq (l : List Nat) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons _ ws ih => change Nat.add (lenN ws) 1 = ws.length + 1; rw [ih]
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
def forceWP {α : Type} (w : Nat) (k : Nat → α) : α :=
  match w with
  | 0 => k 0
  | m + 1 => k (m + 1)
theorem forceWP_eq {α : Type} (w : Nat) (k : Nat → α) : forceWP w k = k w := by
  cases w <;> rfl
def forceCons {α : Type} (l : List Nat) (k : List Nat → α) : α :=
  match l with
  | [] => k []
  | x :: xs => k (x :: xs)
theorem forceCons_eq {α : Type} (l : List Nat) (k : List Nat → α) : forceCons l k = k l := by
  cases l <;> rfl
def forceList {α : Type} (ws : List Nat) (k : List Nat → α) : α :=
  (List.rec (motive := fun _ => (List Nat → α) → α) (fun k => k [])
    (fun w _ next k => next (fun rest => k (w :: rest))) ws) k
theorem forceList_eq {α : Type} (ws : List Nat) (k : List Nat → α) : forceList ws k = k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceList ws (fun rest => k (w :: rest)) = _
    rw [ih]
def canonV2 (mask w : Nat) : Nat :=
  forceWP (Nat.land w mask) (fun v =>
    Bool.rec
      (Bool.rec
        (forceWP (Nat.xor mask v) (fun iv => Bool.rec iv v (Nat.blt v iv)))
        0 (Nat.beq v mask))
      0 (Nat.beq v 0))
theorem canonV2_eq (mask w : Nat) : canonV2 mask w = canon mask w := by
  unfold canonV2 canon bsel; dsimp only
  rw [forceWP_eq]
  change Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (forceWP (Nat.xor mask (w &&& mask)) (fun iv => Bool.rec (motive := fun _ => Nat) iv (w &&& mask) (Nat.blt (w &&& mask) iv)))
      0 (Nat.beq (w &&& mask) mask)) 0 (Nat.beq (w &&& mask) 0) = _
  rw [forceWP_eq]
  cases Nat.beq (w &&& mask) 0 <;> cases Nat.beq (w &&& mask) mask <;> rfl
def HistValid (mask : Nat) (stock : List Nat) : List (Nat × Nat × Nat) → Prop
  | [] => True
  | (z, x, y) :: rest =>
    (∃ op < 4, z = binOp mask op x y) ∧
    (x ∈ stock ∨ ∃ a b, (x, a, b) ∈ rest) ∧
    (y ∈ stock ∨ ∃ a b, (y, a, b) ∈ rest) ∧
    HistValid mask stock rest
def WsCovered (stock : List Nat) (hist : List (Nat × Nat × Nat)) (ws : List Nat) : Prop :=
  ∀ w ∈ ws, w ∈ stock ∨ ∃ a b, (w, a, b) ∈ hist
theorem getD_mem_of_lt {l : List Nat} {i : Nat} (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi
theorem childState_valid {mask token : Nat} {stock : List Nat}
    {st ch : Nat × List Nat × List (Nat × Nat × Nat)}
    (hv : HistValid mask stock st.2.2) (hc : WsCovered stock st.2.2 st.2.1)
    (h : childState mask token st = some ch) :
    HistValid mask stock ch.2.2 ∧ WsCovered stock ch.2.2 ch.2.1 := by
  obtain ⟨fuel, ws, hist⟩ := st
  dsimp only at hv hc
  unfold childState at h; dsimp only at h
  split at h
  · contradiction
  · rename_i hok
    split at h
    · contradiction
    · have heq := Option.some.inj h
      subst ch
      simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hok
      have hab : (token >>> 8) < ((token >>> 4) &&& 15) := by
        cases h1 : Nat.blt (token >>> 8) ((token >>> 4) &&& 15)
        · exfalso; exact hok (Or.inl (Or.inr h1))
        · exact Nat.blt_eq.mp h1
      have hbl : ((token >>> 4) &&& 15) < ws.length := by
        cases h2 : Nat.blt ((token >>> 4) &&& 15) ws.length
        · exfalso; exact hok (Or.inr h2)
        · exact Nat.blt_eq.mp h2
      have hx : ws.getD (token >>> 8) 0 ∈ ws := getD_mem_of_lt (by omega)
      have hy : ws.getD ((token >>> 4) &&& 15) 0 ∈ ws := getD_mem_of_lt hbl
      have hop : ((token >>> 2) &&& 3) < 4 := by
        have := Nat.and_lt_two_pow (token >>> 2) (n := 2) (by omega : 3 < 2 ^ 2)
        simpa using this
      refine ⟨⟨⟨(token >>> 2) &&& 3, hop, rfl⟩, hc _ hx, hc _ hy, hv⟩, ?_⟩
      intro w hw
      rcases insertSorted_mem.mp hw with rfl | hrest
      · exact Or.inr ⟨_, _, List.mem_cons_self⟩
      · have hwm : w ∈ ws := (dropVal_mem.mp (dropVal_mem.mp hrest).1).1
        rcases hc w hwm with hst | ⟨a, b, hmem⟩
        · exact Or.inl hst
        · exact Or.inr ⟨a, b, List.mem_cons_of_mem _ hmem⟩
theorem dagTrace_valid {mask fuel : Nat} {stock : List Nat} {forest : Nat → Nat × Nat}
    {i : Nat} {st : Nat × List Nat × List (Nat × Nat × Nat)}
    (h : dagTrace mask stock fuel forest i = some st) :
    HistValid mask stock st.2.2 ∧ WsCovered stock st.2.2 st.2.1 := by
  unfold dagTrace at h
  suffices ∀ steps j s,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j = some s →
      HistValid mask stock s.2.2 ∧ WsCovered stock s.2.2 s.2.1 from
    this (fuel + 1) i st h
  intro steps
  induction steps with
  | zero => intro j s h; contradiction
  | succ n ih =>
    intro j s h; dsimp only at h
    split at h
    · split at h
      · have e := Option.some.inj h; subst s
        exact ⟨trivial, fun w hw => Or.inl (subsetWords_subset stock _ w hw)⟩
      · contradiction
    · cases hp : (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) n) ((forest j).1 - 1) with
      | none => rw [hp] at h; contradiction
      | some p =>
        rw [hp] at h
        have ⟨hv, hc⟩ := ih _ _ hp
        exact childState_valid hv hc h
theorem addUniq_mem {w u : Nat} {l : List Nat} : u ∈ addUniq w l ↔ u = w ∨ u ∈ l := by
  unfold addUniq
  cases h : l.contains w
  · simp [List.mem_cons]
  · simp only [ite_true]
    have hw : w ∈ l := List.contains_iff_mem.mp h
    constructor
    · exact Or.inr
    · rintro (rfl | hu); exact hw; exact hu
theorem recipeStart_mem {cut : Nat} {stock ws : List Nat} {u : Nat} :
    u ∈ recipeStart cut stock ws ↔ ∃ w ∈ ws, canon cut w = u ∧ ¬Avail stock u := by
  induction ws with
  | nil => simp [recipeStart]
  | cons w ws ih =>
    change u ∈ (if availB stock (canon cut w) then recipeStart cut stock ws
                else addUniq (canon cut w) (recipeStart cut stock ws)) ↔ _
    cases ha : availB stock (canon cut w)
    · simp only [Bool.false_eq_true, ite_false, addUniq_mem, ih]
      have hna : ¬Avail stock (canon cut w) := fun h => by rw [availB_spec.mpr h] at ha; exact Bool.noConfusion ha
      constructor
      · rintro (rfl | ⟨w', hw', rfl, hnu⟩)
        · exact ⟨w, List.mem_cons_self, rfl, hna⟩
        · exact ⟨w', List.mem_cons_of_mem _ hw', rfl, hnu⟩
      · rintro ⟨w', hw', rfl, hnu⟩
        rcases List.mem_cons.mp hw' with rfl | hw'
        · exact Or.inl rfl
        · exact Or.inr ⟨w', hw', rfl, hnu⟩
    · simp only [ite_true, ih]
      have hya : Avail stock (canon cut w) := availB_spec.mp ha
      constructor
      · rintro ⟨w', hw', rfl, hnu⟩; exact ⟨w', List.mem_cons_of_mem _ hw', rfl, hnu⟩
      · rintro ⟨w', hw', rfl, hnu⟩
        rcases List.mem_cons.mp hw' with rfl | hw'
        · exact absurd hya hnu
        · exact ⟨w', hw', rfl, hnu⟩
theorem recipeClose_sub {cut : Nat} {stock : List Nat} {hist : List (Nat × Nat × Nat)} {acc : List Nat} :
    ∀ u ∈ acc, u ∈ recipeClose cut stock hist acc := by
  induction hist generalizing acc with
  | nil => intro u hu; exact hu
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    intro u hu
    change u ∈ (if acc.contains (canon cut w) then
      let va := canon cut a; let vb := canon cut b
      let acc1 := if availB stock va then acc else addUniq va acc
      let acc2 := if availB stock vb then acc1 else addUniq vb acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist acc)
    split
    · apply ih
      have h1 : u ∈ (if availB stock (canon cut a) then acc else addUniq (canon cut a) acc) := by
        split; exact hu; exact addUniq_mem.mpr (Or.inr hu)
      split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
    · exact ih u hu
theorem recipeClose_nil (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) :
    recipeClose cut stock hist [] = [] := by
  induction hist with
  | nil => rfl
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    change (if [].contains (canon cut w) then _ else recipeClose cut stock hist []) = []
    exact ih
theorem recipeClose_mono {cut : Nat} {stock : List Nat} {hist : List (Nat × Nat × Nat)} :
    ∀ {A B : List Nat}, (∀ u ∈ A, u ∈ B) →
      ∀ u ∈ recipeClose cut stock hist A, u ∈ recipeClose cut stock hist B := by
  induction hist with
  | nil => intro A B hAB u hu; exact hAB u hu
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    intro A B hAB u hu
    change u ∈ (if A.contains (canon cut w) then
      let acc1 := if availB stock (canon cut a) then A else addUniq (canon cut a) A
      let acc2 := if availB stock (canon cut b) then acc1 else addUniq (canon cut b) acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist A) at hu
    change u ∈ (if B.contains (canon cut w) then
      let acc1 := if availB stock (canon cut a) then B else addUniq (canon cut a) B
      let acc2 := if availB stock (canon cut b) then acc1 else addUniq (canon cut b) acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist B)
    cases hA : A.contains (canon cut w)
    · simp only [hA, Bool.false_eq_true, ite_false] at hu
      cases hB : B.contains (canon cut w)
      · simp only [Bool.false_eq_true, ite_false]; exact ih hAB u hu
      · simp only [ite_true]
        apply ih _ u hu
        intro x hx
        have h1 : x ∈ (if availB stock (canon cut a) then B else addUniq (canon cut a) B) := by
          split; exact hAB x hx; exact addUniq_mem.mpr (Or.inr (hAB x hx))
        split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
    · have hwB : B.contains (canon cut w) = true := List.contains_iff_mem.mpr (hAB _ (List.contains_iff_mem.mp hA))
      simp only [hA, ite_true] at hu
      simp only [hwB, ite_true]
      apply ih _ u hu
      intro x hx
      have h1 : ∀ y, y ∈ (if availB stock (canon cut a) then A else addUniq (canon cut a) A) →
          y ∈ (if availB stock (canon cut a) then B else addUniq (canon cut a) B) := by
        intro y hy
        cases hca : availB stock (canon cut a)
        · simp only [hca, Bool.false_eq_true, ite_false, addUniq_mem] at hy ⊢
          rcases hy with rfl | hy; exact Or.inl rfl; exact Or.inr (hAB y hy)
        · simp only [hca, ite_true] at hy ⊢; exact hAB y hy
      cases hcb : availB stock (canon cut b)
      · simp only [hcb, Bool.false_eq_true, ite_false, addUniq_mem] at hx ⊢
        rcases hx with rfl | hx; exact Or.inl rfl; exact Or.inr (h1 x hx)
      · simp only [hcb, ite_true] at hx ⊢; exact h1 x hx
noncomputable def buildFrom (cut : Nat) (bstock : List Nat) (S : Finset Nat) :
    List (Nat × Nat × Nat) → List Nat
  | [] => []
  | (z, x, y) :: rest =>
    let vs := buildFrom cut bstock S rest
    let v := canon cut z
    let := Classical.propDecidable
    if v ∈ S ∧ ¬Avail (vs ++ bstock) v ∧ Avail (vs ++ bstock) (canon cut x) ∧ Avail (vs ++ bstock) (canon cut y)
    then vs ++ [v] else vs
theorem buildFrom_builds {mask cut : Nat} {stock bstock : List Nat} {S : Finset Nat}
    (sub : mask &&& cut = cut) :
    ∀ {hist : List (Nat × Nat × Nat)}, HistValid mask stock hist →
      BuildsBin cut bstock (buildFrom cut bstock S hist)
  | [], _ => trivial
  | (z, x, y) :: rest, ⟨⟨op, hop, hz⟩, _, _, hrest⟩ => by
    unfold buildFrom; dsimp only
    have ih := buildFrom_builds (bstock := bstock) (S := S) sub hrest
    split
    · rename_i hcond
      obtain ⟨_, hna, hax, hay⟩ := hcond
      have hgate : GateBin cut (buildFrom cut bstock S rest ++ bstock) (canon cut z) := by
        have hsub := canon_sub_binOp (op := op) (a := x) (b := y) sub
        rw [← hz] at hsub
        rcases hsub with h0 | hx | hy | ⟨op', hop', heq⟩
        · exact absurd (Or.inl h0) hna
        · exact absurd (hx ▸ hax) hna
        · exact absurd (hy ▸ hay) hna
        · exact ⟨canon cut x, canon cut y, op', hop', hax, hay, heq⟩
      exact builds_append ih ⟨hgate, trivial⟩
    · exact ih
theorem buildFrom_nodup_sub (cut : Nat) (bstock : List Nat) (S : Finset Nat) :
    ∀ (hist : List (Nat × Nat × Nat)),
      (buildFrom cut bstock S hist).Nodup ∧ ∀ u ∈ buildFrom cut bstock S hist, u ∈ S
  | [] => ⟨List.nodup_nil, fun _ h => nomatch h⟩
  | (z, x, y) :: rest => by
    unfold buildFrom; dsimp only
    obtain ⟨hnd, hsub⟩ := buildFrom_nodup_sub cut bstock S rest
    split
    · rename_i hcond
      obtain ⟨hvS, hna, _, _⟩ := hcond
      have hnm : canon cut z ∉ buildFrom cut bstock S rest := fun hm =>
        hna (Or.inr (List.mem_append_left bstock hm))
      refine ⟨List.nodup_append.mpr ⟨hnd, List.nodup_singleton _, fun a ha b hb heq => by
        rw [List.mem_singleton.mp hb] at heq; exact hnm (heq ▸ ha)⟩, ?_⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact hsub u hu
      · rw [List.mem_singleton.mp hu]; exact hvS
    · exact ⟨hnd, hsub⟩
theorem buildFrom_mono_avail (cut : Nat) (bstock : List Nat) (S : Finset Nat)
    (r : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) {u : Nat}
    (hu : Avail (buildFrom cut bstock S rest ++ bstock) u) :
    Avail (buildFrom cut bstock S (r :: rest) ++ bstock) u := by
  obtain ⟨z, x, y⟩ := r
  unfold buildFrom; dsimp only
  split
  · exact avail_weaken (fun w hw => by simp only [List.mem_append] at hw ⊢; tauto) hu
  · exact hu
theorem buildFrom_covers {mask cut : Nat} {stock bstock : List Nat} {S : Finset Nat}
    (hstk : ∀ s ∈ stock, Avail bstock (canon cut s)) :
    ∀ {hist : List (Nat × Nat × Nat)}, HistValid mask stock hist →
      ∀ (acc : List Nat),
        (∀ u ∈ acc, Avail bstock u ∨ ∃ z x y, (z, x, y) ∈ hist ∧ canon cut z = u) →
        (∀ u ∈ recipeClose cut bstock hist acc, u ∈ S) →
        ∀ u ∈ acc, Avail (buildFrom cut bstock S hist ++ bstock) u
  | [], _, acc, hcov, _, u, hu => by
    rcases hcov u hu with ha | ⟨_, _, _, hm, _⟩
    · exact avail_weaken (fun w hw => List.mem_append_right _ hw) ha
    · exact nomatch hm
  | (z, x, y) :: rest, ⟨_, hxc, hyc, hrest⟩, acc, hcov, hS, u, hu => by
    cases hcz : acc.contains (canon cut z)
    · have hnz : canon cut z ∉ acc := fun hm => by rw [List.contains_iff_mem.mpr hm] at hcz; exact Bool.noConfusion hcz
      have hS' : ∀ v ∈ recipeClose cut bstock rest acc, v ∈ S := by
        intro v hv; apply hS v
        change v ∈ (if acc.contains (canon cut z) then _ else recipeClose cut bstock rest acc)
        simp only [hcz, Bool.false_eq_true, ite_false]; exact hv
      have hcov' : ∀ v ∈ acc, Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v := by
        intro v hv
        rcases hcov v hv with ha | ⟨z', x', y', hm, heq⟩
        · exact Or.inl ha
        · rcases List.mem_cons.mp hm with hhead | htail
          · rcases Prod.mk.inj hhead with ⟨rfl, _⟩
            exact absurd (heq ▸ hv) hnz
          · exact Or.inr ⟨z', x', y', htail, heq⟩
      exact buildFrom_mono_avail cut bstock S (z, x, y) rest
        (buildFrom_covers hstk hrest acc hcov' hS' u hu)
    · have hzacc : canon cut z ∈ acc := List.contains_iff_mem.mp hcz
      have hzS : canon cut z ∈ S := hS _ (recipeClose_sub _ hzacc)
      set acc1 := if availB bstock (canon cut x) then acc else addUniq (canon cut x) acc
      set acc2 := if availB bstock (canon cut y) then acc1 else addUniq (canon cut y) acc1
      have hS2 : ∀ v ∈ recipeClose cut bstock rest acc2, v ∈ S := by
        intro v hv; apply hS v
        change v ∈ (if acc.contains (canon cut z) then recipeClose cut bstock rest acc2 else _)
        simp only [hcz, ite_true]; exact hv
      let := Classical.propDecidable
      set acc' := acc2.filter (fun v => decide (Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v))
      have hsub' : ∀ v ∈ acc', v ∈ acc2 := fun v hv => (List.mem_filter.mp hv).1
      have hcov' : ∀ v ∈ acc', Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v :=
        fun v hv => of_decide_eq_true (List.mem_filter.mp hv).2
      have hS' : ∀ v ∈ recipeClose cut bstock rest acc', v ∈ S :=
        fun v hv => hS2 v (recipeClose_mono hsub' v hv)
      have hIH := buildFrom_covers hstk hrest acc' hcov' hS'
      have hacc_sub2 : ∀ v ∈ acc, v ∈ acc2 := by
        intro v hv
        have h1 : v ∈ acc1 := by
          unfold acc1; split; exact hv; exact addUniq_mem.mpr (Or.inr hv)
        unfold acc2; split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
      have hax : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut x) := by
        cases hbx : availB bstock (canon cut x)
        · have hx2 : canon cut x ∈ acc2 := by
            have hx1 : canon cut x ∈ acc1 := by
              unfold acc1; simp only [hbx, Bool.false_eq_true, ite_false]; exact addUniq_mem.mpr (Or.inl rfl)
            unfold acc2; split; exact hx1; exact addUniq_mem.mpr (Or.inr hx1)
          have hpx : Avail bstock (canon cut x) ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = canon cut x := by
            rcases hxc with hs | ⟨a, b, hm⟩
            · exact Or.inl (hstk x hs)
            · exact Or.inr ⟨x, a, b, hm, rfl⟩
          exact hIH _ (List.mem_filter.mpr ⟨hx2, decide_eq_true hpx⟩)
        · exact avail_weaken (fun w hw => List.mem_append_right _ hw) (availB_spec.mp hbx)
      have hay : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut y) := by
        cases hby : availB bstock (canon cut y)
        · have hy2 : canon cut y ∈ acc2 := by
            unfold acc2; simp only [hby, Bool.false_eq_true, ite_false]; exact addUniq_mem.mpr (Or.inl rfl)
          have hpy : Avail bstock (canon cut y) ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = canon cut y := by
            rcases hyc with hs | ⟨a, b, hm⟩
            · exact Or.inl (hstk y hs)
            · exact Or.inr ⟨y, a, b, hm, rfl⟩
          exact hIH _ (List.mem_filter.mpr ⟨hy2, decide_eq_true hpy⟩)
        · exact avail_weaken (fun w hw => List.mem_append_right _ hw) (availB_spec.mp hby)
      by_cases huz : u = canon cut z
      · subst huz
        unfold buildFrom; dsimp only
        split
        · exact Or.inr (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))
        · rename_i hneg
          by_cases ha : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut z)
          · exact ha
          · exact absurd ⟨hzS, ha, hax, hay⟩ hneg
      · have hpu : Avail bstock u ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = u := by
          rcases hcov u hu with ha | ⟨z', x', y', hm, heq⟩
          · exact Or.inl ha
          · rcases List.mem_cons.mp hm with hhead | htail
            · rcases Prod.mk.inj hhead with ⟨rfl, _⟩; exact absurd heq.symm huz
            · exact Or.inr ⟨z', x', y', htail, heq⟩
        exact buildFrom_mono_avail cut bstock S (z, x, y) rest
          (hIH u (List.mem_filter.mpr ⟨hacc_sub2 u hu, decide_eq_true hpu⟩))
def flatStartF (cut : Nat) (stock ws : List Nat) : Nat × List Nat :=
  List.rec (0, []) (fun w _ ih =>
    match ih with
    | (fl, acc) =>
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec
          (Bool.rec
            (Bool.rec (fl, v :: acc) (fl, acc) (memN v acc))
            (fl, acc) (memN v stock))
          (forceWP (Nat.add fl 1) (fun fl1 => (fl1, acc)))
          (Nat.beq v 0))) ws
theorem flatStartF_eq (cut : Nat) (stock ws : List Nat) :
    flatStartF cut stock ws = (flatCount cut ws, recipeStart cut stock ws) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hstep : flatStartF cut stock (w :: ws) =
      match flatStartF cut stock ws with
      | (fl, acc) =>
        forceWP (canonV2 cut w) (fun v =>
          Bool.rec
            (Bool.rec
              (Bool.rec (fl, v :: acc) (fl, acc) (memN v acc))
              (fl, acc) (memN v stock))
            (forceWP (Nat.add fl 1) (fun fl1 => (fl1, acc)))
            (Nat.beq v 0)) := rfl
    rw [hstep, ih]; dsimp only; rw [forceWP_eq, canonV2_eq, forceWP_eq]
    change Bool.rec
        (Bool.rec
          (Bool.rec (flatCount cut ws, canon cut w :: recipeStart cut stock ws)
            (flatCount cut ws, recipeStart cut stock ws) (memN (canon cut w) (recipeStart cut stock ws)))
          (flatCount cut ws, recipeStart cut stock ws) (memN (canon cut w) stock))
        (Nat.add (flatCount cut ws) 1, recipeStart cut stock ws) (Nat.beq (canon cut w) 0) =
      (bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws),
       if availB stock (canon cut w) then recipeStart cut stock ws else addUniq (canon cut w) (recipeStart cut stock ws))
    simp only [memN_eq, availB, addUniq]
    have haux (b1 b2 b3 : Bool) :
        Bool.rec (Bool.rec (Bool.rec (flatCount cut ws, canon cut w :: recipeStart cut stock ws)
          (flatCount cut ws, recipeStart cut stock ws) b3)
          (flatCount cut ws, recipeStart cut stock ws) b2)
          (Nat.add (flatCount cut ws) 1, recipeStart cut stock ws) b1 =
        (bsel b1 (flatCount cut ws + 1) (flatCount cut ws),
         if (b1 || b2) = true then recipeStart cut stock ws
         else if b3 = true then recipeStart cut stock ws else canon cut w :: recipeStart cut stock ws) := by
      cases b1 <;> cases b2 <;> cases b3 <;> rfl
    exact haux _ _ _
def recipeCloseV2 (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec (next acc)
          (forceWP (canonV2 cut a) (fun va =>
            forceCons
              (Bool.rec (Bool.rec (Bool.rec (va :: acc) acc (memN va acc)) acc (memN va stock)) acc (Nat.beq va 0))
              (fun acc1 =>
                forceWP (canonV2 cut b) (fun vb =>
                  forceCons
                    (Bool.rec (Bool.rec (Bool.rec (vb :: acc1) acc1 (memN vb acc1)) acc1 (memN vb stock)) acc1 (Nat.beq vb 0))
                    next))))
          (memN v acc))) hist needed
theorem recipeCloseV2_eq (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) :
    recipeCloseV2 cut stock hist needed = recipeClose cut stock hist needed := by
  induction hist generalizing needed with
  | nil => rfl
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    have hstep : recipeCloseV2 cut stock ((w, a, b) :: hist) needed =
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec (recipeCloseV2 cut stock hist needed)
          (forceWP (canonV2 cut a) (fun va =>
            forceCons
              (Bool.rec (Bool.rec (Bool.rec (va :: needed) needed (memN va needed)) needed (memN va stock)) needed (Nat.beq va 0))
              (fun acc1 =>
                forceWP (canonV2 cut b) (fun vb =>
                  forceCons
                    (Bool.rec (Bool.rec (Bool.rec (vb :: acc1) acc1 (memN vb acc1)) acc1 (memN vb stock)) acc1 (Nat.beq vb 0))
                    (recipeCloseV2 cut stock hist)))))
          (memN v needed)) := rfl
    rw [hstep]
    simp only [forceWP_eq, forceCons_eq, canonV2_eq, memN_eq]
    change Bool.rec (recipeCloseV2 cut stock hist needed) _ (needed.contains (canon cut w)) =
      (if needed.contains (canon cut w) then
        let va := canon cut a; let vb := canon cut b
        let acc1 := if availB stock va then needed else addUniq va needed
        let acc2 := if availB stock vb then acc1 else addUniq vb acc1
        recipeClose cut stock hist acc2
      else recipeClose cut stock hist needed)
    cases needed.contains (canon cut w)
    · exact ih needed
    · dsimp only [ite_true]
      rw [ih]
      congr 1
      have hadd (v : Nat) (l : List Nat) :
          Bool.rec (Bool.rec (Bool.rec (v :: l) l (l.contains v)) l (stock.contains v)) l (Nat.beq v 0) =
          if availB stock v then l else addUniq v l := by
        dsimp only [availB, addUniq]
        have haux (b1 b2 b3 : Bool) :
            Bool.rec (Bool.rec (Bool.rec (v :: l) l b3) l b2) l b1 =
            if (b1 || b2) = true then l else if b3 = true then l else v :: l := by
          cases b1 <;> cases b2 <;> cases b3 <;> rfl
        exact haux _ _ _
      rw [hadd (canon cut a) needed, hadd (canon cut b)]
def boundClosesV2 (fuel : Nat) (ws : List Nat) (hist : List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, bstock, lower, _) := bound
  match flatStartF cut bstock ws with
  | (fl, start0) =>
    forceWP (Nat.sub fuel fl) (fun rem =>
      Bool.rec false
        (match start0 with
         | [] => true
         | s0 :: sr =>
           forceList (s0 :: sr) (fun start =>
             Bool.rec false
               (Nat.blt (Nat.add (lenN (recipeCloseV2 cut bstock hist start)) rem) lower)
               (Nat.blt (Nat.add (lenN start) rem) lower)))
        (Nat.blt rem lower))
theorem boundClosesV2_sound {mask goal : Nat} {stock : List Nat}
    {fuel : Nat} {ws : List Nat} {hist : List (Nat × Nat × Nat)}
    {bound : Nat × List Nat × Nat × Nat}
    (hlow : LowerBin bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (sub : mask &&& bound.1 = bound.1)
    (hg : canon bound.1 goal = bound.2.2.2) (hnz : bound.2.2.2 ≠ 0)
    (hstk : ∀ s ∈ stock, Avail bound.2.1 (canon bound.1 s))
    (hv : HistValid mask stock hist) (hc : WsCovered stock hist ws)
    (nd : ws.Nodup) {k : Nat} (hk : k ≤ fuel)
    (hlive : LiveBin mask goal k ws.toFinset) :
    boundClosesV2 fuel ws hist bound = false := by
  obtain ⟨cut, bstock, lower, bgoal⟩ := bound
  dsimp only at hlow sub hg hnz hstk
  apply Bool.eq_false_iff.mpr
  intro hbc
  unfold boundClosesV2 at hbc; dsimp only at hbc
  rw [flatStartF_eq] at hbc; dsimp only at hbc
  simp only [forceWP_eq] at hbc
  cases h1 : Nat.blt (Nat.sub fuel (flatCount cut ws)) lower
  · rw [h1] at hbc; exact Bool.noConfusion hbc
  · rw [h1] at hbc; dsimp only at hbc
    have hlen_lt : (recipeClose cut bstock hist (recipeStart cut bstock ws)).length + (fuel - flatCount cut ws) < lower := by
      cases hs : recipeStart cut bstock ws with
      | nil =>
        rw [recipeClose_nil]; simp only [List.length_nil, Nat.zero_add]
        exact Nat.blt_eq.mp h1
      | cons s0 sr =>
        rw [hs] at hbc; dsimp only at hbc
        simp only [forceList_eq, recipeCloseV2_eq, lenN_eq] at hbc
        cases h2 : Nat.blt (Nat.add (s0 :: sr).length (Nat.sub fuel (flatCount cut ws))) lower
        · rw [h2] at hbc; exact Bool.noConfusion hbc
        · rw [h2] at hbc; dsimp only at hbc
          exact Nat.blt_eq.mp hbc
    set needed := recipeClose cut bstock hist (recipeStart cut bstock ws)
    set S := needed.toFinset
    set vs := buildFrom cut bstock S hist
    have hvbd : BuildsBin cut bstock vs := buildFrom_builds sub hv
    obtain ⟨hvnd, hvsub⟩ := buildFrom_nodup_sub cut bstock S hist
    have hvlen : vs.length ≤ needed.length := by
      rw [← List.toFinset_card_of_nodup hvnd]
      have hsubf : vs.toFinset ⊆ S := fun u hu => hvsub u (List.mem_toFinset.mp hu)
      exact Nat.le_trans (Finset.card_le_card hsubf) (List.toFinset_card_le needed)
    have hcov_start : ∀ u ∈ recipeStart cut bstock ws,
        Avail bstock u ∨ ∃ z x y, (z, x, y) ∈ hist ∧ canon cut z = u := by
      intro u hu
      obtain ⟨w, hww, rfl, hna⟩ := recipeStart_mem.mp hu
      rcases hc w hww with hws | ⟨a, b, hmem⟩
      · exact absurd (hstk w hws) hna
      · exact Or.inr ⟨w, a, b, hmem, rfl⟩
    have hvs_start := buildFrom_covers hstk hv (recipeStart cut bstock ws) hcov_start
      (fun u hu => List.mem_toFinset.mpr hu)
    have hsup : ∀ w ∈ ws.toFinset, Avail (vs ++ bstock) (canon cut w) := by
      intro w hw
      have hww : w ∈ ws := List.mem_toFinset.mp hw
      by_cases ha : Avail bstock (canon cut w)
      · exact avail_weaken (fun u hu => List.mem_append_right _ hu) ha
      · exact hvs_start _ (recipeStart_mem.mpr ⟨w, hww, rfl, ha⟩)
    have hgnf : canon cut goal ≠ 0 := hg.symm ▸ hnz
    obtain ⟨ys, hylen, hybd, hyhit⟩ := maskedBuildBin sub hgnf hlive (vs ++ bstock) hsup
    rw [← flatCount_card cut nd] at hylen
    have hboth := builds_append hvbd hybd
    have hfinal : Avail ((vs ++ ys) ++ bstock) bgoal := by
      rw [← hg]
      exact avail_weaken (fun u hu => by simp only [List.mem_append] at hu ⊢; tauto) hyhit
    have heno := hlow (vs ++ ys) hboth hfinal
    simp only [List.length_append] at heno
    omega
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
def checkHintBoundV5 (goal negGoal fuel1 : Nat) (ws1 : List Nat) (hist1 : List (Nat × Nat × Nat))
    (bounds : List (Nat × List Nat × Nat × Nat)) (cid : Nat) : Bool :=
  match nthBound bounds cid with
  | some b => boundClosesV2 fuel1 ws1 hist1 b
  | none => Bool.rec true false (dagPartF ws1 goal negGoal)
theorem checkHintBoundV5_open {mask goal fuel1 cid : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {ws1 : List Nat} {hist1 : List (Nat × Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 ws1)
    (nd : ws1.Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k ws1.toFinset) :
    checkHintBoundV5 goal (Nat.xor mask goal) fuel1 ws1 hist1 bounds cid = false := by
  unfold checkHintBoundV5
  cases hb : nthBound bounds cid with
  | some b =>
    dsimp only
    have hmem := nthBound_mem hb
    have hg := hgoals b hmem
    exact boundClosesV2_sound (hknown b hmem) (hsub b hmem) hg.1 hg.2 (hstk b hmem) hv hc nd hk hlive
  | none =>
    dsimp only
    have hdp : dagPartF ws1 goal (Nat.xor mask goal) = true := by
      have heq : dagPartF ws1 goal (Nat.xor mask goal) = dagPart ws1 goal (mask ^^^ goal) :=
        dagPartF_eq ws1 goal (mask ^^^ goal)
      rw [heq]; exact dagPart_live hgm hlive
    rw [hdp]
def hintCloseLeafV5 (goal negGoal ep cutBits cutMask : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (fuel1 : Nat) (ws1 : List Nat) (hist1 : List (Nat × Nat × Nat))
    (sp : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  Bool.rec (some (cur, h))
    (forceWP (Nat.land h 3) (fun tag =>
      Bool.rec
        (Bool.rec
          (Bool.rec none
            (forceWP (Nat.shiftRight h 2) (fun h' => some (cur, h')))
            (checkHintBoundV5 goal negGoal fuel1 ws1 hist1 bounds tag))
          (forceWP (Nat.shiftRight h 2) (fun h1 =>
            forceWP (Nat.add 2 (Nat.land h1 7)) (fun cid =>
              Bool.rec none
                (forceWP (Nat.shiftRight h1 3) (fun h' => some (cur, h')))
                (checkHintBoundV5 goal negGoal fuel1 ws1 hist1 bounds cid))))
          (Nat.beq tag 2))
        (forceWP (Nat.shiftRight h 2) (fun h1 =>
          forceWP (Nat.add 10 (Nat.land h1 cutMask)) (fun cid =>
            Bool.rec none
              (forceWP (Nat.shiftRight h1 cutBits) (fun h' => some (cur, h')))
              (checkHintBoundV5 goal negGoal fuel1 ws1 hist1 bounds cid))))
        (Nat.beq tag 3)))
    (Nat.beq (Nat.land ep sp) ep)
theorem hintCloseLeafV5_open {mask goal cutBits cutMask fuel1 : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {ws1 : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)} {h : Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 ws1)
    (nd : ws1.Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k ws1.toFinset) :
    hintCloseLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask bounds fuel1 ws1 hist1 (orSep ws1) cur h = none := by
  unfold hintCloseLeafV5
  rw [sepPack_live hgm hlive]; dsimp only
  rw [forceWP_eq]
  cases Nat.beq (Nat.land h 3) 3
  · dsimp only
    cases Nat.beq (Nat.land h 3) 2
    · dsimp only
      rw [checkHintBoundV5_open hgm hknown hsub hgoals hstk hv hc nd hk hlive]
    · dsimp only
      rw [forceWP_eq, forceWP_eq]
      rw [checkHintBoundV5_open hgm hknown hsub hgoals hstk hv hc nd hk hlive]
  · dsimp only
    rw [forceWP_eq, forceWP_eq]
    rw [checkHintBoundV5_open hgm hknown hsub hgoals hstk hv hc nd hk hlive]
def stepLeafV5 (goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel1 z spZ baseSp : Nat) (rest : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tok : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match cur with
  | (t, dest) :: tl =>
    Bool.rec
      (hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel1 (z :: rest) hist1 (Nat.lor spZ baseSp) cur h)
      (Bool.rec none
        (match states dest with
         | none => none
         | some saved =>
           Bool.rec none (Bool.rec none (some (tl, h)) (eqListN saved.2.1 (insertSortedF z rest)))
             (Nat.beq saved.1 fuel1))
        (Nat.blt dest count))
      (Nat.beq tok t)
  | [] =>
    hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel1 (z :: rest) hist1 (Nat.lor spZ baseSp) [] h
theorem stepLeafV5_ref {mask goal cutBits cutMask count fuel1 z tok h : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {rest : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)}
    {res : List (Nat × Nat) × Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 (z :: rest))
    (nd : (z :: rest).Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k (z :: rest).toFinset)
    (hok : stepLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds states
      fuel1 z (sepPack z) (orSep rest) rest hist1 tok cur h = some res) :
    ∃ dest < count, ∃ saved, states dest = some saved ∧ saved.1 = fuel1 ∧ saved.2.1 = insertSorted z rest := by
  have hcl := hintCloseLeafV5_open (cutBits := cutBits) (cutMask := cutMask) (cur := cur) (h := h)
    hgm hknown hsub hgoals hstk hv hc nd hk hlive
  unfold stepLeafV5 at hok
  have hor : Nat.lor (sepPack z) (orSep rest) = orSep (z :: rest) := rfl
  rw [hor] at hok
  cases cur with
  | nil => dsimp only at hok; rw [hcl] at hok; cases hok
  | cons hd tl =>
    obtain ⟨t, dest⟩ := hd
    dsimp only at hok
    cases ht : Nat.beq tok t
    · rw [ht] at hok; dsimp only at hok; rw [hcl] at hok; cases hok
    · rw [ht] at hok; dsimp only at hok
      cases hlt : Nat.blt dest count
      · rw [hlt] at hok; dsimp only at hok; cases hok
      · rw [hlt] at hok; dsimp only at hok
        cases hst : states dest with
        | none => rw [hst] at hok; dsimp only at hok; cases hok
        | some saved =>
          rw [hst] at hok; dsimp only at hok
          cases hf : Nat.beq saved.1 fuel1
          · rw [hf] at hok; dsimp only at hok; cases hok
          · rw [hf] at hok; dsimp only at hok
            cases heq : eqListN saved.2.1 (insertSortedF z rest)
            · rw [heq] at hok; dsimp only at hok; cases hok
            · rw [eqListN_eq, insertSortedF_eq, beq_iff_eq] at heq
              exact ⟨dest, Nat.blt_eq.mp hlt, saved, hst, Nat.beq_eq.mp hf, heq⟩
def checkKeepsV5 (goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n z spZ spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tokBase : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match (Bool.rec
    (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur h)
    (some (cur, h)) (Nat.blt fuel (Nat.sub n 1)) : Option (List (Nat × Nat) × Nat)) with
  | none => none
  | some (c1, h1) =>
    match (Bool.rec
      (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1 h1)
      (some (c1, h1)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
    | none => none
    | some (c2, h2) =>
      match (Bool.rec
        (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2 h2)
        (some (c2, h2)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
      | none => none
      | some (c3, h3) =>
        Bool.rec
          (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spAll ws0 hist1 (Nat.add tokBase 3) c3 h3)
          (some (c3, h3)) (Nat.blt fuel (Nat.add n 1))
theorem checkKeepsV5_at {goal negGoal ep cutBits cutMask count fuel fuel1 n z spZ spAll spNoA spNoB spNoAB tokBase h : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist1 : List (Nat × Nat × Nat)}
    {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hok : checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
      ws0 wsNoA wsNoB wsNoAB hist1 tokBase cur h = some res)
    (keepA keepB : Bool) :
    match keepA, keepB with
    | false, false => Nat.blt fuel (n - 1) = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase c hh = some r
    | true, false => Nat.blt fuel n = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (tokBase + 1) c hh = some r
    | false, true => Nat.blt fuel n = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (tokBase + 2) c hh = some r
    | true, true => Nat.blt fuel (n + 1) = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spAll ws0 hist1 (tokBase + 3) c hh = some r := by
  unfold checkKeepsV5 at hok
  cases hp0 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur h)
    (some (cur, h)) (Nat.blt fuel (Nat.sub n 1)) : Option (List (Nat × Nat) × Nat)) with
  | none => rw [hp0] at hok; dsimp only at hok; cases hok
  | some p1 =>
    obtain ⟨c1, h1⟩ := p1
    rw [hp0] at hok; dsimp only at hok
    cases hp1 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1 h1)
      (some (c1, h1)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
    | none => rw [hp1] at hok; dsimp only at hok; cases hok
    | some p2 =>
      obtain ⟨c2, h2⟩ := p2
      rw [hp1] at hok; dsimp only at hok
      cases hp2 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2 h2)
        (some (c2, h2)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
      | none => rw [hp2] at hok; dsimp only at hok; cases hok
      | some p3 =>
        obtain ⟨c3, h3⟩ := p3
        rw [hp2] at hok; dsimp only at hok
        cases keepA <;> cases keepB
        · cases hw : Nat.blt fuel (n - 1)
          · have hw' : Nat.blt fuel (Nat.sub n 1) = false := hw
            rw [hw'] at hp0; exact Or.inr ⟨cur, h, (c1, h1), hp0⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp2; exact Or.inr ⟨c2, h2, (c3, h3), hp2⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp1; exact Or.inr ⟨c1, h1, (c2, h2), hp1⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel (n + 1)
          · have hw' : Nat.blt fuel (Nat.add n 1) = false := hw
            rw [hw'] at hok; exact Or.inr ⟨c3, h3, res, hok⟩
          · exact Or.inl rfl
def checkOpV5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x y rawZ op : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  forceWP (canonV2 mask rawZ) (fun z =>
    Bool.rec
      (Bool.rec
        (forceWP (sepPack z) (fun spZ =>
          checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
            ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) cur h))
        (some (cur, h)) (memN z ws0))
      (some (cur, h)) (Nat.beq z 0))
def check4OpsV5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x nx y : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
  | none => none
  | some (c1, h1) =>
    match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1 h1 with
    | none => none
    | some (c2, h2) =>
      match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2 h2 with
      | none => none
      | some (c3, h3) =>
        checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land nx y) 3 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c3 h3
theorem check4OpsV5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n x y spAll spNoA spNoB spNoAB tokAB op h : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist : List (Nat × Nat × Nat)}
    {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hop : op < 4)
    (hok : check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x (Nat.xor mask x) y
      spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h = some res) :
    let z := binOp mask op x y
    z = 0 ∨ ws0.contains z = true ∨
      ∃ c hh r, checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z (sepPack z)
        spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) c hh = some r := by
  unfold check4OpsV5 at hok
  have extract (rawZ op' : Nat) (c0 : List (Nat × Nat)) (h0 : Nat) (r0 : List (Nat × Nat) × Nat)
      (hz : canon mask rawZ = binOp mask op' x y)
      (hrun : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y rawZ op'
        spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c0 h0 = some r0) :
      binOp mask op' x y = 0 ∨ ws0.contains (binOp mask op' x y) = true ∨
        ∃ c hh r, checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n (binOp mask op' x y)
          (sepPack (binOp mask op' x y)) spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB
          ((binOp mask op' x y, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op') 2) c hh = some r := by
    unfold checkOpV5 at hrun
    rw [forceWP_eq, canonV2_eq, hz] at hrun
    cases hz0 : Nat.beq (binOp mask op' x y) 0
    · rw [hz0] at hrun; dsimp only at hrun
      cases hm : memN (binOp mask op' x y) ws0
      · rw [hm] at hrun; dsimp only at hrun
        rw [forceWP_eq] at hrun
        exact Or.inr (Or.inr ⟨c0, h0, r0, hrun⟩)
      · rw [memN_eq] at hm; exact Or.inr (Or.inl hm)
    · exact Or.inl (Nat.beq_eq.mp hz0)
  cases hp0 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
  | none => rw [hp0] at hok; dsimp only at hok; cases hok
  | some p1 =>
    obtain ⟨c1, h1⟩ := p1; rw [hp0] at hok; dsimp only at hok
    cases hp1 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1 h1 with
    | none => rw [hp1] at hok; dsimp only at hok; cases hok
    | some p2 =>
      obtain ⟨c2, h2⟩ := p2; rw [hp1] at hok; dsimp only at hok
      cases hp2 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2 h2 with
      | none => rw [hp2] at hok; dsimp only at hok; cases hok
      | some p3 =>
        obtain ⟨c3, h3⟩ := p3; rw [hp2] at hok; dsimp only at hok
        rcases (by omega : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3) with rfl | rfl | rfl | rfl
        · exact extract _ 0 cur h (c1, h1) rfl hp0
        · exact extract _ 1 c1 h1 (c2, h2) rfl hp1
        · exact extract _ 2 c2 h2 (c3, h3) rfl hp2
        · exact extract _ 3 c3 h3 res rfl hok
def loopB_V5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n a x nx spAll spNoA : Nat) (ws0 wsNoA : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, b, cur, h =>
    forceWP (getDN ws0 b) (fun y =>
      forceList (dropValF true y ws0) (fun wsNoB =>
        forceList (dropValF true y wsNoA) (fun wsNoAB =>
          forceWP (orSepSkip y ps) (fun spNoB =>
            forceWP (orSepSkip2 x y ps) (fun spNoAB =>
              forceWP (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) (fun tokAB =>
                match check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx y spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
                | none => none
                | some (cur1, h1) =>
                  loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem (Nat.add b 1) cur1 h1))))))
theorem loopB_V5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n a x nx spAll spNoA : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem b0 b h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hb1 : b0 ≤ b) (hb2 : b < b0 + rem)
    (hok : loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem b0 cur h = some res) :
    let y := getDN ws0 b
    ∃ c hh r, check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx y spAll spNoA
      (orSepSkip y ps) (orSepSkip2 x y ps) ws0 wsNoA (dropValF true y ws0) (dropValF true y wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) c hh = some r := by
  induction rem generalizing b0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopB_V5 at hok
    rw [forceWP_eq, forceList_eq, forceList_eq, forceWP_eq, forceWP_eq, forceWP_eq] at hok
    cases hp : check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx (getDN ws0 b0) spAll spNoA
      (orSepSkip (getDN ws0 b0) ps) (orSepSkip2 x (getDN ws0 b0) ps) ws0 wsNoA
      (dropValF true (getDN ws0 b0) ws0) (dropValF true (getDN ws0 b0) wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b0) 2) cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : b = b0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change b0 + 1 ≤ b; omega) (by change b < (b0 + 1) + r; omega) hok
def loopA_V5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n spAll : Nat) (ws0 : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, a, cur, h =>
    forceWP (getDN ws0 a) (fun x =>
      forceList (dropValF true x ws0) (fun wsNoA =>
        forceWP (Nat.xor mask x) (fun nx =>
          forceWP (orSepSkip x ps) (fun spNoA =>
            match loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) cur h with
            | none => none
            | some (cur1, h1) =>
              loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist rem (Nat.add a 1) cur1 h1))))
theorem loopA_V5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n spAll : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem a0 a h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (ha1 : a0 ≤ a) (ha2 : a < a0 + rem)
    (hok : loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist rem a0 cur h = some res) :
    let x := getDN ws0 a
    ∃ c hh r, loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x (Nat.xor mask x) spAll
      (orSepSkip x ps) ws0 (dropValF true x ws0) ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) c hh = some r := by
  induction rem generalizing a0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopA_V5 at hok
    rw [forceWP_eq, forceList_eq, forceWP_eq, forceWP_eq] at hok
    cases hp : loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a0 (getDN ws0 a0) (Nat.xor mask (getDN ws0 a0)) spAll
      (orSepSkip (getDN ws0 a0) ps) ws0 (dropValF true (getDN ws0 a0) ws0) ps hist (Nat.sub n (Nat.add a0 1)) (Nat.add a0 1) cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : a = a0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change a0 + 1 ≤ a; omega) (by change a < (a0 + 1) + r; omega) hok
def dagCheckNodeV5 (mask goal ep cutBits cutMask : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (cursors : Nat → List (Nat × Nat)) (nodeHints : Nat → Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, hist) =>
    forceWs ws (fun ws0 =>
      forceWP (lenN ws0) (fun n =>
        Bool.rec
          (Bool.rec
            (Bool.rec false
              (forceW (Nat.xor mask goal) (fun negGoal =>
                forceW (Nat.sub fuel 1) (fun fuel1 =>
                  forceSepPairs ws0 (fun ps =>
                    forceW (orSepAll ps) (fun spAll =>
                      forceW (nodeHints (Nat.add i 1)) (fun h0 =>
                        match loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist n 0 (cursors (Nat.add i 1)) h0 with
                        | none => false
                        | some _ => true))))))
              (Nat.blt n 17))
            true (Nat.beq fuel 0))
          false (memN goal ws0)))
def stepRootV5 (goal negGoal ep cutBits cutMask count fuel : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (ws : List Nat) (tok : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  Bool.rec
    (match cur with
     | (t, dest) :: tl =>
       Bool.rec
         (hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel ws [] (orSep ws) cur h)
         (Bool.rec none
           (match states dest with
            | none => none
            | some saved =>
              Bool.rec none (Bool.rec none (some (tl, h)) (eqListN saved.2.1 ws)) (Nat.beq saved.1 fuel))
           (Nat.blt dest count))
         (Nat.beq tok t)
     | [] =>
       hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel ws [] (orSep ws) [] h)
    (some (cur, h)) (Nat.blt (Nat.add fuel 1) (lenN ws))
def loopRootsV5 (goal negGoal ep cutBits cutMask count fuel : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (stock : List Nat) : Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, tok, cur, h =>
    forceList (subsetWordsF stock tok) (fun ws =>
      match stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states ws tok cur h with
      | none => none
      | some (cur1, h1) =>
        loopRootsV5 goal negGoal ep cutBits cutMask count fuel bounds states stock rem (Nat.add tok 1) cur1 h1)
def dagCheckRootsV5 (mask goal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (rootCur : List (Nat × Nat)) (rootHint : Nat) (stock : List Nat) (fuel : Nat) : Bool :=
  match loopRootsV5 goal (Nat.xor mask goal) ep cutBits cutMask count fuel bounds states stock (Nat.shiftLeft 1 (lenN stock)) 0 rootCur rootHint with
  | none => false
  | some _ => true
theorem loopRootsV5_at {goal negGoal ep cutBits cutMask count fuel : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {stock : List Nat} {rem t0 tok h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (ht1 : t0 ≤ tok) (ht2 : tok < t0 + rem)
    (hok : loopRootsV5 goal negGoal ep cutBits cutMask count fuel bounds states stock rem t0 cur h = some res) :
    ∃ c hh r, stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states (subsetWordsF stock tok) tok c hh = some r := by
  induction rem generalizing t0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopRootsV5 at hok
    rw [forceList_eq] at hok
    cases hp : stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states (subsetWordsF stock t0) t0 cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : tok = t0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change t0 + 1 ≤ tok; omega) (by change tok < (t0 + 1) + r; omega) hok
theorem dagAllNodesV5 {mask goal cutBits cutMask fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)} {nodeHints : Nat → Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (snd : stock.Nodup)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV5 mask goal (edgePack mask goal) cutBits cutMask bounds count
      (dagTrace mask stock fuel forest) cursors nodeHints i = true) :
    ∀ cap i st, i < count → dagTrace mask stock fuel forest i = some st →
      st.1 = cap → ∀ k, k ≤ cap → ¬LiveBin mask goal k st.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i st hi htr hcap k hk hlive
    obtain ⟨rem, ws, hist⟩ := st
    dsimp only at hcap hlive
    have nd : ws.Nodup := dagTrace_nodup snd htr
    obtain ⟨hv, hcov⟩ := dagTrace_valid htr
    dsimp only at hv hcov
    have hchk := hnodes i (Nat.zero_le i) hi
    unfold dagCheckNodeV5 at hchk
    rw [htr] at hchk; dsimp only at hchk
    rw [forceWs_eq, forceWP_eq, lenN_eq, memN_eq] at hchk
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
          rw [forceW_eq, forceW_eq, forceSepPairs_eq, forceW_eq, forceW_eq] at hchk
          cases hloop : loopA_V5 mask goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds
              (dagTrace mask stock fuel forest) rem (Nat.sub rem 1) ws.length (orSepAll (mapSep ws)) ws (mapSep ws) hist
              ws.length 0 (cursors (Nat.add i 1)) (nodeHints (Nat.add i 1)) with
          | none => rw [hloop] at hchk; exact Bool.noConfusion hchk
          | some resA =>
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
            obtain ⟨cA, hA, rA, hB⟩ := loopA_V5_at (a := a) (Nat.zero_le a) (by omega) hloop
            obtain ⟨cB, hB', rB, hO⟩ := loopB_V5_at (b := b) (by change a + 1 ≤ b; omega) (by change b < (a + 1) + (ws.length - (a + 1)); omega) hB
            simp only [getDN_eq, dropValF_eq, orSepAll_mapSep, orSepSkip_mapSep, orSepSkip2_mapSep] at hO
            set x := ws.getD a 0
            set y := ws.getD b 0
            set z := binOp mask op x y
            have hznz : z ≠ 0 := hzeq.symm ▸ hz0
            have hznm : ws.contains z = false := by
              cases h : ws.contains z
              · rfl
              · exact absurd (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)) (hzeq.symm ▸ hf0)
            rcases check4OpsV5_at hop_lt hO with hz' | hcm | ⟨cK, hK', rK, hK⟩
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
              have hv' : HistValid mask stock ((z, x, y) :: hist) :=
                ⟨⟨op, hop_lt, rfl⟩, hcov x hxM, hcov y hyM, hv⟩
              have hcov' : WsCovered stock ((z, x, y) :: hist) (z :: rest) := by
                intro w hw
                rcases List.mem_cons.mp hw with rfl | hw'
                · exact Or.inr ⟨x, y, List.mem_cons_self⟩
                · have hwm : w ∈ ws := (dropVal_mem.mp (dropVal_mem.mp hw').1).1
                  rcases hcov w hwm with hst | ⟨u, v, hm⟩
                  · exact Or.inl hst
                  · exact Or.inr ⟨u, v, List.mem_cons_of_mem _ hm⟩
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
              have hka := checkKeepsV5_at hK keepA keepB
              have finish {tok' hh' : Nat} {c' : List (Nat × Nat)} {rr : List (Nat × Nat) × Nat}
                  (hstep : stepLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds
                    (dagTrace mask stock fuel forest) (Nat.sub rem 1) z (sepPack z) (orSep rest) rest ((z, x, y) :: hist) tok' c' hh' = some rr) : False := by
                obtain ⟨dest, hdest, saved, htr2, hfEq, hwEq⟩ :=
                  stepLeafV5_ref hgm hknown hsub hgoals hstk hv' hcov' hnd_u (k := k') (by change k' ≤ rem - 1; omega) hlive_u hstep
                exact ih (rem - 1) (by omega) dest saved hdest htr2 hfEq k' (by omega) (hwEq ▸ hlive_s)
              cases keepA <;> cases keepB
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false] at hlen'; omega
                · rw [hdropComm] at hst; exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
                · exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
                · exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [ite_true] at hlen'; omega
                · exact finish hst
      · rw [hcg] at hchk; exact Bool.noConfusion hchk
def nodupB : List Nat → Bool
  | [] => true
  | w :: ws => !memN w ws && nodupB ws
theorem nodupB_spec {l : List Nat} (h : nodupB l = true) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons w ws ih =>
    unfold nodupB at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', memN_eq] at h
    exact List.nodup_cons.mpr ⟨fun hm => by rw [List.contains_iff_mem.mpr hm] at h; exact Bool.noConfusion h.1, ih h.2⟩
theorem kn_nil : KnownBin [] := fun _ h => nomatch h
theorem kn_cons {m : Nat} {s : List Nat} {l g : Nat} {bs : List (Nat × List Nat × Nat × Nat)}
    (h : LowerBin m s g l) (hs : KnownBin bs) : KnownBin ((m, s, l, g) :: bs) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact h
  · exact hs b hb
def checkSliceMetaV5 (mask goal ep : Nat) (stock : List Nat)
    (bounds : List (Nat × List Nat × Nat × Nat)) : Bool :=
  Nat.beq (Nat.land goal mask) goal &&
  !Nat.beq goal 0 &&
  stock.all (fun w => Nat.beq (canon mask w) w) &&
  nodupB stock &&
  Nat.beq ep (edgePack mask goal) &&
  bounds.all (fun b =>
    Nat.beq (Nat.land mask b.1) b.1 &&
    Nat.beq (canon b.1 goal) b.2.2.2 &&
    !Nat.beq b.2.2.2 0 &&
    stock.all (fun s => availB b.2.1 (canon b.1 s)))
theorem lowerDagV5 {mask goal ep cutBits cutMask fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)} {nodeHints : Nat → Nat}
    (hknown : KnownBin bounds)
    (hroots : dagCheckRootsV5 mask goal ep cutBits cutMask count bounds
      (dagTraceF mask stock fuel forest) (cursors 0) (nodeHints 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV5 mask goal ep cutBits cutMask bounds count
      (dagTraceF mask stock fuel forest) cursors nodeHints i = true)
    (hmeta : checkSliceMetaV5 mask goal ep stock bounds = true) :
    LowerBin mask stock goal (fuel + 1) := by
  unfold checkSliceMetaV5 at hmeta
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hmeta
  obtain ⟨⟨⟨⟨⟨hgmB, hgnzB⟩, hcs⟩, hndB⟩, hepB⟩, hbdB⟩ := hmeta
  have hgm : Masked mask goal := Nat.beq_eq.mp hgmB
  have hgnz : goal ≠ 0 := fun h => by rw [h] at hgnzB; exact Bool.noConfusion hgnzB
  have snd : stock.Nodup := nodupB_spec hndB
  have hep : ep = edgePack mask goal := Nat.beq_eq.mp hepB
  have hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1 := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true] at h
    exact Nat.beq_eq.mp h.1.1.1
  have hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨Nat.beq_eq.mp h.1.1.2, fun h0 => by rw [h0] at h; exact Bool.noConfusion h.1.2⟩
  have hstkB : ∀ b ∈ bounds, stock.all (fun s => availB b.2.1 (canon b.1 s)) = true := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true] at h
    exact h.2
  subst hep
  have hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s) := fun b hb s hs =>
    availB_spec.mp (List.all_eq_true.mp (hstkB b hb) s hs)
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
  unfold dagCheckRootsV5 at hroots
  have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
    rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [hpow] at hroots
  cases hrl : loopRootsV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count fuel bounds
      (dagTrace mask stock fuel forest) stock (2 ^ stock.length) 0 (cursors 0) (nodeHints 0) with
  | none => rw [hrl] at hroots; exact Bool.noConfusion hroots
  | some resR =>
    obtain ⟨c, hh, rr, hsr⟩ := loopRootsV5_at (tok := tok) (Nat.zero_le tok) (by omega) hrl
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
    have hcov0 : WsCovered stock [] (subsetWords stock tok) :=
      fun w hw => Or.inl (subsetWords_subset stock tok w hw)
    have hcl := hintCloseLeafV5_open (cutBits := cutBits) (cutMask := cutMask) (fuel1 := fuel) (hist1 := []) (cur := c) (h := hh)
      hgm hknown hsub hgoals hstk trivial hcov0 hnd (k := k) (by omega) hlive'
    unfold stepRootV5 at hsr
    rw [hnw] at hsr; dsimp only at hsr
    cases c with
    | nil => dsimp only at hsr; rw [hcl] at hsr; cases hsr
    | cons hd tl =>
      obtain ⟨t, dest⟩ := hd
      dsimp only at hsr
      cases ht : Nat.beq tok t
      · rw [ht] at hsr; dsimp only at hsr; rw [hcl] at hsr; cases hsr
      · rw [ht] at hsr; dsimp only at hsr
        cases hltc : Nat.blt dest count
        · rw [hltc] at hsr; dsimp only at hsr; cases hsr
        · rw [hltc] at hsr; dsimp only at hsr
          cases htr2 : dagTrace mask stock fuel forest dest with
          | none => rw [htr2] at hsr; dsimp only at hsr; cases hsr
          | some saved =>
            rw [htr2] at hsr; dsimp only at hsr
            cases hf : Nat.beq saved.1 fuel
            · rw [hf] at hsr; dsimp only at hsr; cases hsr
            · rw [hf] at hsr; dsimp only at hsr
              cases heq : eqListN saved.2.1 (subsetWords stock tok)
              · rw [heq] at hsr; dsimp only at hsr; cases hsr
              · rw [eqListN_eq, beq_iff_eq] at heq
                exact dagAllNodesV5 hgm hknown hsub hgoals hstk snd hnodes fuel dest saved
                  (Nat.blt_eq.mp hltc) htr2 (Nat.beq_eq.mp hf) k (by omega) (heq ▸ hlive')
def unpackF (data width idx : Nat) : Nat :=
  Nat.land (Nat.shiftRight data (Nat.mul idx width)) (Nat.sub (Nat.shiftLeft 1 width) 1)
def unpackForestF (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := Nat.add pBits tBits
  let code := unpackF data w i
  (Nat.shiftRight code tBits, Nat.land code (Nat.sub (Nat.shiftLeft 1 tBits) 1))
def unpackListAux (data off w wMask tokBits tokMask : Nat) : Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, acc => acc
  | k + 1, acc =>
    forceWP (Nat.land (Nat.shiftRight data (Nat.mul (Nat.add off k) w)) wMask) (fun code =>
      unpackListAux data off w wMask tokBits tokMask k ((Nat.land code tokMask, Nat.shiftRight code tokBits) :: acc))
def unpackCursorV5 (index data idxW idxMask sizeBits sizeMask tokBits tokMask w wMask : Nat) :
    Nat → List (Nat × Nat) :=
  fun parent =>
    forceWP (Nat.land (Nat.shiftRight index (Nat.mul parent idxW)) idxMask) (fun entry =>
      unpackListAux data (Nat.shiftRight entry sizeBits) w wMask tokBits tokMask (Nat.land entry sizeMask) [])
def unpackHintV5 (index data idxW idxMask lenBits lenMask : Nat) : Nat → Nat :=
  fun parent =>
    forceWP (Nat.land (Nat.shiftRight index (Nat.mul parent idxW)) idxMask) (fun entry =>
      forceWP (Nat.land entry lenMask) (fun hlen =>
        Bool.rec
          (Nat.land (Nat.shiftRight data (Nat.shiftRight entry lenBits)) (Nat.sub (Nat.shiftLeft 1 hlen) 1))
          0 (Nat.beq hlen 0)))
abbrev uC := unpackCursorV5
abbrev uH := unpackHintV5
abbrev uF := unpackForestF
abbrev dN := dagCheckNodeV5
abbrev dR := dagCheckRootsV5
abbrev dT := dagTraceF
abbrev tB := treeBlockF
abbrev LPN := List (Nat × Nat)
abbrev BList := List (Nat × List Nat × Nat × Nat)
theorem bJ {a m b : Nat} {f : Nat → Bool} (h1 : ∀ i, a ≤ i → i < m → f i = true) (h2 : ∀ i, m ≤ i → i < b → f i = true) : ∀ i, a ≤ i → i < b → f i = true := block_join h1 h2
theorem tA {lo hi : Nat} {f : Nat → Bool} (h : treeBlockF lo hi f = true) : ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := treeBlockF_at h
theorem nc0 (f : Nat → Bool) : ∀ i, 0 ≤ i → i < 0 → f i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
def m_0 := 0x44444444
def s_0 : List Nat := [0x4040404, 0x440044, 0x4444]
def g_0 := 0x40444
def ep_0 := 0x4400000000000040040000000000004040000000000000000000000000000000000
def bds_0 : BList := []
def cc_0_0 : Nat → LPN := uC 0x9 0x7 2 3 1 1 3 7 4 15
def cur_0 : Nat → LPN := cc_0_0
def hc_0_0 (_ : Nat) := 0
def nh_0 : Nat → Nat := hc_0_0
def f_0 := uF 0x7 1 3
def ch_0 := dN 0x44444444 g_0 ep_0 1 1 bds_0 1 (dT 0x44444444 [0x4040404, 0x440044, 0x4444] 3 f_0) cur_0 nh_0
set_option maxHeartbeats 0 in
theorem rc_0 : dR 0x44444444 g_0 ep_0 1 1 1 bds_0 (dT 0x44444444 [0x4040404, 0x440044, 0x4444] 3 f_0) (cur_0 0) (nh_0 0) [0x4040404, 0x440044, 0x4444] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_0_0 : tB 0 1 ch_0 = true := by decide +kernel
theorem nc_0 : ∀ i, 0 ≤ i → i < 1 → ch_0 i = true := fun _ h1 h2 => tA nb_0_0 h1 h2
theorem lb_0 : LowerBin 0x44444444 [0x4040404, 0x440044, 0x4444] g_0 4 :=
  lowerDagV5 (kn_nil) rc_0 nc_0 (by decide +kernel)
def m_1 := 0xa000a000a000a
def s_1 : List Nat := [0x2000200020002, 0xa0000000a, 0xa000a]
def g_1 := 0x20002000a
def ep_1 := 0x2000800000002000000080000000000000000000000000000000000000002000200000000000000000000
def bds_1 : BList := []
def cc_1_0 : Nat → LPN := uC 0x9 0x7 2 3 1 1 3 7 4 15
def cur_1 : Nat → LPN := cc_1_0
def hc_1_0 (_ : Nat) := 0
def nh_1 : Nat → Nat := hc_1_0
def f_1 := uF 0x7 1 3
def ch_1 := dN 0xa000a000a000a g_1 ep_1 1 1 bds_1 1 (dT 0xa000a000a000a [0x2000200020002, 0xa0000000a, 0xa000a] 3 f_1) cur_1 nh_1
set_option maxHeartbeats 0 in
theorem rc_1 : dR 0xa000a000a000a g_1 ep_1 1 1 1 bds_1 (dT 0xa000a000a000a [0x2000200020002, 0xa0000000a, 0xa000a] 3 f_1) (cur_1 0) (nh_1 0) [0x2000200020002, 0xa0000000a, 0xa000a] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_1_0 : tB 0 1 ch_1 = true := by decide +kernel
theorem nc_1 : ∀ i, 0 ≤ i → i < 1 → ch_1 i = true := fun _ h1 h2 => tA nb_1_0 h1 h2
theorem lb_1 : LowerBin 0xa000a000a000a [0x2000200020002, 0xa0000000a, 0xa000a] g_1 4 :=
  lowerDagV5 (kn_nil) rc_1 nc_1 (by decide +kernel)
def m_2 := 0x5500550000000000
def s_2 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_2 := 0x100150000000000
def ep_2 := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
def bds_2 : BList := []
def cc_2_0 : Nat → LPN := uC 0x9 0x7 2 3 1 1 3 7 4 15
def cur_2 : Nat → LPN := cc_2_0
def hc_2_0 (_ : Nat) := 0
def nh_2 : Nat → Nat := hc_2_0
def f_2 := uF 0x7 1 3
def ch_2 := dN 0x5500550000000000 g_2 ep_2 1 1 bds_2 1 (dT 0x5500550000000000 [0x1100110000000000, 0x500050000000000, 0x550000000000] 3 f_2) cur_2 nh_2
set_option maxHeartbeats 0 in
theorem rc_2 : dR 0x5500550000000000 g_2 ep_2 1 1 1 bds_2 (dT 0x5500550000000000 [0x1100110000000000, 0x500050000000000, 0x550000000000] 3 f_2) (cur_2 0) (nh_2 0) [0x1100110000000000, 0x500050000000000, 0x550000000000] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_2_0 : tB 0 1 ch_2 = true := by decide +kernel
theorem nc_2 : ∀ i, 0 ≤ i → i < 1 → ch_2 i = true := fun _ h1 h2 => tA nb_2_0 h1 h2
theorem lb_2 : LowerBin 0x5500550000000000 [0x1100110000000000, 0x500050000000000, 0x550000000000] g_2 4 :=
  lowerDagV5 (kn_nil) rc_2 nc_2 (by decide +kernel)
def m_3 := 0x5555000000000000
def s_3 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_3 := 0x115000000000000
def ep_3 := 0x14000000000000010400000000000001100000000000000000000000000000
def bds_3 : BList := []
def cc_3_0 : Nat → LPN := uC 0x9 0x7 2 3 1 1 3 7 4 15
def cur_3 : Nat → LPN := cc_3_0
def hc_3_0 (_ : Nat) := 0
def nh_3 : Nat → Nat := hc_3_0
def f_3 := uF 0x7 1 3
def ch_3 := dN 0x5555000000000000 g_3 ep_3 1 1 bds_3 1 (dT 0x5555000000000000 [0x1111000000000000, 0x505000000000000, 0x55000000000000] 3 f_3) cur_3 nh_3
set_option maxHeartbeats 0 in
theorem rc_3 : dR 0x5555000000000000 g_3 ep_3 1 1 1 bds_3 (dT 0x5555000000000000 [0x1111000000000000, 0x505000000000000, 0x55000000000000] 3 f_3) (cur_3 0) (nh_3 0) [0x1111000000000000, 0x505000000000000, 0x55000000000000] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_3_0 : tB 0 1 ch_3 = true := by decide +kernel
theorem nc_3 : ∀ i, 0 ≤ i → i < 1 → ch_3 i = true := fun _ h1 h2 => tA nb_3_0 h1 h2
theorem lb_3 : LowerBin 0x5555000000000000 [0x1111000000000000, 0x505000000000000, 0x55000000000000] g_3 4 :=
  lowerDagV5 (kn_nil) rc_3 nc_3 (by decide +kernel)
def m_4 := 0x3030000030300000
def s_4 : List Nat := [0x1010000010100000, 0x30000000300000, 0x30300000]
def g_4 := 0x10000010300000
def ep_4 := 0x1020000000000000000000000010000000200000000000000000000000000000000000000010000010000000
def bds_4 : BList := []
def cc_4_0 : Nat → LPN := uC 0x9 0x7 2 3 1 1 3 7 4 15
def cur_4 : Nat → LPN := cc_4_0
def hc_4_0 (_ : Nat) := 0
def nh_4 : Nat → Nat := hc_4_0
def f_4 := uF 0x7 1 3
def ch_4 := dN 0x3030000030300000 g_4 ep_4 1 1 bds_4 1 (dT 0x3030000030300000 [0x1010000010100000, 0x30000000300000, 0x30300000] 3 f_4) cur_4 nh_4
set_option maxHeartbeats 0 in
theorem rc_4 : dR 0x3030000030300000 g_4 ep_4 1 1 1 bds_4 (dT 0x3030000030300000 [0x1010000010100000, 0x30000000300000, 0x30300000] 3 f_4) (cur_4 0) (nh_4 0) [0x1010000010100000, 0x30000000300000, 0x30300000] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_4_0 : tB 0 1 ch_4 = true := by decide +kernel
theorem nc_4 : ∀ i, 0 ≤ i → i < 1 → ch_4 i = true := fun _ h1 h2 => tA nb_4_0 h1 h2
theorem lb_4 : LowerBin 0x3030000030300000 [0x1010000010100000, 0x30000000300000, 0x30300000] g_4 4 :=
  lowerDagV5 (kn_nil) rc_4 nc_4 (by decide +kernel)
def m_5 := 0x3030303000000000
def s_5 : List Nat := [0x1010101000000000, 0x30003000000000, 0x303000000000]
def g_5 := 0x10103000000000
def ep_5 := 0x1020000000000010002000000000000000000000000000000000000000000010100000000000
def bds_5 : BList := []
def cc_5_0 : Nat → LPN := uC 0x9 0x7 2 3 1 1 3 7 4 15
def cur_5 : Nat → LPN := cc_5_0
def hc_5_0 (_ : Nat) := 0
def nh_5 : Nat → Nat := hc_5_0
def f_5 := uF 0x7 1 3
def ch_5 := dN 0x3030303000000000 g_5 ep_5 1 1 bds_5 1 (dT 0x3030303000000000 [0x1010101000000000, 0x30003000000000, 0x303000000000] 3 f_5) cur_5 nh_5
set_option maxHeartbeats 0 in
theorem rc_5 : dR 0x3030303000000000 g_5 ep_5 1 1 1 bds_5 (dT 0x3030303000000000 [0x1010101000000000, 0x30003000000000, 0x303000000000] 3 f_5) (cur_5 0) (nh_5 0) [0x1010101000000000, 0x30003000000000, 0x303000000000] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_5_0 : tB 0 1 ch_5 = true := by decide +kernel
theorem nc_5 : ∀ i, 0 ≤ i → i < 1 → ch_5 i = true := fun _ h1 h2 => tA nb_5_0 h1 h2
theorem lb_5 : LowerBin 0x3030303000000000 [0x1010101000000000, 0x30003000000000, 0x303000000000] g_5 4 :=
  lowerDagV5 (kn_nil) rc_5 nc_5 (by decide +kernel)
def m_6 := 0xcc000000cc
def s_6 : List Nat := [0x4400000044, 0xc0000000c, 0xcc]
def g_6 := 0x40000004c
def ep_6 := 0x4800000000000000000000000000000000000000040000000800000000000000000000000400000040
def bds_6 : BList := []
def cc_6_0 : Nat → LPN := uC 0x9 0x7 2 3 1 1 3 7 4 15
def cur_6 : Nat → LPN := cc_6_0
def hc_6_0 (_ : Nat) := 0
def nh_6 : Nat → Nat := hc_6_0
def f_6 := uF 0x7 1 3
def ch_6 := dN 0xcc000000cc g_6 ep_6 1 1 bds_6 1 (dT 0xcc000000cc [0x4400000044, 0xc0000000c, 0xcc] 3 f_6) cur_6 nh_6
set_option maxHeartbeats 0 in
theorem rc_6 : dR 0xcc000000cc g_6 ep_6 1 1 1 bds_6 (dT 0xcc000000cc [0x4400000044, 0xc0000000c, 0xcc] 3 f_6) (cur_6 0) (nh_6 0) [0x4400000044, 0xc0000000c, 0xcc] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_6_0 : tB 0 1 ch_6 = true := by decide +kernel
theorem nc_6 : ∀ i, 0 ≤ i → i < 1 → ch_6 i = true := fun _ h1 h2 => tA nb_6_0 h1 h2
theorem lb_6 : LowerBin 0xcc000000cc [0x4400000044, 0xc0000000c, 0xcc] g_6 4 :=
  lowerDagV5 (kn_nil) rc_6 nc_6 (by decide +kernel)
def m_7 := 0x3300000033000000
def s_7 : List Nat := [0x1100000011000000, 0x300000003000000, 0x33000000]
def g_7 := 0x100000013000000
def ep_7 := 0x1200000000000000000000000000000000000000010000000200000000000000000000000100000010000000
def bds_7 : BList := []
def cc_7_0 : Nat → LPN := uC 0x9 0x7 2 3 1 1 3 7 4 15
def cur_7 : Nat → LPN := cc_7_0
def hc_7_0 (_ : Nat) := 0
def nh_7 : Nat → Nat := hc_7_0
def f_7 := uF 0x7 1 3
def ch_7 := dN 0x3300000033000000 g_7 ep_7 1 1 bds_7 1 (dT 0x3300000033000000 [0x1100000011000000, 0x300000003000000, 0x33000000] 3 f_7) cur_7 nh_7
set_option maxHeartbeats 0 in
theorem rc_7 : dR 0x3300000033000000 g_7 ep_7 1 1 1 bds_7 (dT 0x3300000033000000 [0x1100000011000000, 0x300000003000000, 0x33000000] 3 f_7) (cur_7 0) (nh_7 0) [0x1100000011000000, 0x300000003000000, 0x33000000] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_7_0 : tB 0 1 ch_7 = true := by decide +kernel
theorem nc_7 : ∀ i, 0 ≤ i → i < 1 → ch_7 i = true := fun _ h1 h2 => tA nb_7_0 h1 h2
theorem lb_7 : LowerBin 0x3300000033000000 [0x1100000011000000, 0x300000003000000, 0x33000000] g_7 4 :=
  lowerDagV5 (kn_nil) rc_7 nc_7 (by decide +kernel)
def m_8 := 0xcc00cc
def s_8 : List Nat := [0x440044, 0xc000c, 0xcc]
def g_8 := 0x4004c
def ep_8 := 0x480000000000000000000000000004000800000000000000000000000000040040
def bds_8 : BList := []
def cc_8_0 : Nat → LPN := uC 0x9 0x7 2 3 1 1 3 7 4 15
def cur_8 : Nat → LPN := cc_8_0
def hc_8_0 (_ : Nat) := 0
def nh_8 : Nat → Nat := hc_8_0
def f_8 := uF 0x7 1 3
def ch_8 := dN 0xcc00cc g_8 ep_8 1 1 bds_8 1 (dT 0xcc00cc [0x440044, 0xc000c, 0xcc] 3 f_8) cur_8 nh_8
set_option maxHeartbeats 0 in
theorem rc_8 : dR 0xcc00cc g_8 ep_8 1 1 1 bds_8 (dT 0xcc00cc [0x440044, 0xc000c, 0xcc] 3 f_8) (cur_8 0) (nh_8 0) [0x440044, 0xc000c, 0xcc] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_8_0 : tB 0 1 ch_8 = true := by decide +kernel
theorem nc_8 : ∀ i, 0 ≤ i → i < 1 → ch_8 i = true := fun _ h1 h2 => tA nb_8_0 h1 h2
theorem lb_8 : LowerBin 0xcc00cc [0x440044, 0xc000c, 0xcc] g_8 4 :=
  lowerDagV5 (kn_nil) rc_8 nc_8 (by decide +kernel)
def m_9 := 0xf0f0
def s_9 : List Nat := [0x5050, 0x3030, 0xf0]
def g_9 := 0x1070
def ep_9 := 0x60000000000000000000000000000010200000000000001040
def bds_9 : BList := []
def cc_9_0 : Nat → LPN := uC 0x9 0x7 2 3 1 1 3 7 4 15
def cur_9 : Nat → LPN := cc_9_0
def hc_9_0 (_ : Nat) := 0
def nh_9 : Nat → Nat := hc_9_0
def f_9 := uF 0x7 1 3
def ch_9 := dN 0xf0f0 g_9 ep_9 1 1 bds_9 1 (dT 0xf0f0 [0x5050, 0x3030, 0xf0] 3 f_9) cur_9 nh_9
set_option maxHeartbeats 0 in
theorem rc_9 : dR 0xf0f0 g_9 ep_9 1 1 1 bds_9 (dT 0xf0f0 [0x5050, 0x3030, 0xf0] 3 f_9) (cur_9 0) (nh_9 0) [0x5050, 0x3030, 0xf0] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_9_0 : tB 0 1 ch_9 = true := by decide +kernel
theorem nc_9 : ∀ i, 0 ≤ i → i < 1 → ch_9 i = true := fun _ h1 h2 => tA nb_9_0 h1 h2
theorem lb_9 : LowerBin 0xf0f0 [0x5050, 0x3030, 0xf0] g_9 4 :=
  lowerDagV5 (kn_nil) rc_9 nc_9 (by decide +kernel)
def m_10 := 0x4444444444444444
def s_10 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_10 := 0x4040400040444
def ep_10 := 0x4000000400000004400004000000040040000404040004040000000000000000000000000000000000
def bds_10 : BList := [(m_0,s_0,4,g_0)]
def cc_10_0 : Nat → LPN := fun _ => []
def cur_10 : Nat → LPN := cc_10_0
def hc_10_0 (_ : Nat) := 0
def nh_10 : Nat → Nat := hc_10_0
def f_10 (_ : Nat) := (0,0)
def ch_10 := dN 0x4444444444444444 g_10 ep_10 1 1 bds_10 0 (dT 0x4444444444444444 [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444] 4 f_10) cur_10 nh_10
set_option maxHeartbeats 0 in
theorem rc_10 : dR 0x4444444444444444 g_10 ep_10 1 1 0 bds_10 (dT 0x4444444444444444 [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444] 4 f_10) (cur_10 0) (nh_10 0) [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444] 4 = true := by decide +kernel
def nc_10 := nc0 ch_10
theorem lb_10 : LowerBin 0x4444444444444444 [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444] g_10 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_10 nc_10 (by decide +kernel)
def m_11 := 0xa0a0a0a0a0a0a0a
def s_11 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_11 := 0x202020a0a
def ep_11 := 0x2020a0800000002000008080000000200000000000000000000000000000002020200000000000000000000
def bds_11 : BList := [(m_1,s_1,4,g_1)]
def cc_11_0 : Nat → LPN := fun _ => []
def cur_11 : Nat → LPN := cc_11_0
def hc_11_0 (_ : Nat) := 0
def nh_11 : Nat → Nat := hc_11_0
def f_11 (_ : Nat) := (0,0)
def ch_11 := dN 0xa0a0a0a0a0a0a0a g_11 ep_11 1 1 bds_11 0 (dT 0xa0a0a0a0a0a0a0a [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a] 4 f_11) cur_11 nh_11
set_option maxHeartbeats 0 in
theorem rc_11 : dR 0xa0a0a0a0a0a0a0a g_11 ep_11 1 1 0 bds_11 (dT 0xa0a0a0a0a0a0a0a [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a] 4 f_11) (cur_11 0) (nh_11 0) [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a] 4 = true := by decide +kernel
def nc_11 := nc0 ch_11
theorem lb_11 : LowerBin 0xa0a0a0a0a0a0a0a [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a] g_11 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_11 nc_11 (by decide +kernel)
def m_12 := 0x5050505050505050
def s_12 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_12 := 0x10101010101050
def ep_12 := 0x1000004000001000000000400010000000000040000000000000000000101010101010000000000000000000
def bds_12 : BList := []
def cc_12_0 : Nat → LPN := uC 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 4095 5 31 10 1023 16 65535
def cur_12 : Nat → LPN := cc_12_0
def hc_12_0 (_ : Nat) := 0
def nh_12 : Nat → Nat := hc_12_0
def f_12 := uF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_12 := dN 0x5050505050505050 g_12 ep_12 1 1 bds_12 64 (dT 0x5050505050505050 [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050] 5 f_12) cur_12 nh_12
set_option maxHeartbeats 0 in
theorem rc_12 : dR 0x5050505050505050 g_12 ep_12 1 1 64 bds_12 (dT 0x5050505050505050 [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050] 5 f_12) (cur_12 0) (nh_12 0) [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12_0 : tB 0 32 ch_12 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12_1 : tB 32 64 ch_12 = true := by decide +kernel
theorem nj_12_1 : ∀ i, 0 ≤ i → i < 64 → ch_12 i = true := bJ (fun _ h1 h2 => tA nb_12_0 h1 h2) (fun _ h1 h2 => tA nb_12_1 h1 h2)
theorem nc_12 : ∀ i, 0 ≤ i → i < 64 → ch_12 i = true := nj_12_1
theorem lb_12 : LowerBin 0x5050505050505050 [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050] g_12 6 :=
  lowerDagV5 (kn_nil) rc_12 nc_12 (by decide +kernel)
def m_13 := 0xaa00aa00aa00aa
def s_13 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_13 := 0x220022002a
def ep_13 := 0x22000800000022000000080000000000000000000000000000000800000022002200200000000000000000
def bds_13 : BList := [(m_1,s_1,4,g_1)]
def cc_13_0 : Nat → LPN := fun _ => []
def cur_13 : Nat → LPN := cc_13_0
def hc_13_0 (_ : Nat) := 0
def nh_13 : Nat → Nat := hc_13_0
def f_13 (_ : Nat) := (0,0)
def ch_13 := dN 0xaa00aa00aa00aa g_13 ep_13 1 1 bds_13 0 (dT 0xaa00aa00aa00aa [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa] 4 f_13) cur_13 nh_13
set_option maxHeartbeats 0 in
theorem rc_13 : dR 0xaa00aa00aa00aa g_13 ep_13 1 1 0 bds_13 (dT 0xaa00aa00aa00aa [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa] 4 f_13) (cur_13 0) (nh_13 0) [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa] 4 = true := by decide +kernel
def nc_13 := nc0 ch_13
theorem lb_13 : LowerBin 0xaa00aa00aa00aa [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa] g_13 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_13 nc_13 (by decide +kernel)
def m_14 := 0x5500550055005500
def s_14 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_14 := 0x100150011001500
def ep_14 := 0x1000000000001400000004000000000000000000010004000000040001001000110010000000000000000000
def bds_14 : BList := [(m_2,s_2,4,g_2)]
def cc_14_0 : Nat → LPN := fun _ => []
def cur_14 : Nat → LPN := cc_14_0
def hc_14_0 (_ : Nat) := 0
def nh_14 : Nat → Nat := hc_14_0
def f_14 (_ : Nat) := (0,0)
def ch_14 := dN 0x5500550055005500 g_14 ep_14 1 1 bds_14 0 (dT 0x5500550055005500 [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500] 4 f_14) cur_14 nh_14
set_option maxHeartbeats 0 in
theorem rc_14 : dR 0x5500550055005500 g_14 ep_14 1 1 0 bds_14 (dT 0x5500550055005500 [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500] 4 f_14) (cur_14 0) (nh_14 0) [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500] 4 = true := by decide +kernel
def nc_14 := nc0 ch_14
theorem lb_14 : LowerBin 0x5500550055005500 [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500] g_14 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_14 nc_14 (by decide +kernel)
def m_15 := 0x5555000055550000
def s_15 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_15 := 0x115000011150000
def ep_15 := 0x1000000000000000000000000014000000040000010400000004000001100000111000000000000000000000
def bds_15 : BList := [(m_3,s_3,4,g_3)]
def cc_15_0 : Nat → LPN := fun _ => []
def cur_15 : Nat → LPN := cc_15_0
def hc_15_0 (_ : Nat) := 0
def nh_15 : Nat → Nat := hc_15_0
def f_15 (_ : Nat) := (0,0)
def ch_15 := dN 0x5555000055550000 g_15 ep_15 1 1 bds_15 0 (dT 0x5555000055550000 [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000] 4 f_15) cur_15 nh_15
set_option maxHeartbeats 0 in
theorem rc_15 : dR 0x5555000055550000 g_15 ep_15 1 1 0 bds_15 (dT 0x5555000055550000 [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000] 4 f_15) (cur_15 0) (nh_15 0) [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000] 4 = true := by decide +kernel
def nc_15 := nc0 ch_15
theorem lb_15 : LowerBin 0x5555000055550000 [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000] g_15 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_15 nc_15 (by decide +kernel)
def m_16 := 0x55555555
def s_16 : List Nat := [0x11111111, 0x5050505, 0x550055, 0x5555]
def g_16 := 0x11151555
def ep_16 := 0x4400000000000040040000000000004040000000000111010000000000000000000
def bds_16 : BList := [(m_0,s_0,4,g_0)]
def cc_16_0 : Nat → LPN := fun _ => []
def cur_16 : Nat → LPN := cc_16_0
def hc_16_0 (_ : Nat) := 0
def nh_16 : Nat → Nat := hc_16_0
def f_16 (_ : Nat) := (0,0)
def ch_16 := dN 0x55555555 g_16 ep_16 1 1 bds_16 0 (dT 0x55555555 [0x11111111, 0x5050505, 0x550055, 0x5555] 4 f_16) cur_16 nh_16
set_option maxHeartbeats 0 in
theorem rc_16 : dR 0x55555555 g_16 ep_16 1 1 0 bds_16 (dT 0x55555555 [0x11111111, 0x5050505, 0x550055, 0x5555] 4 f_16) (cur_16 0) (nh_16 0) [0x11111111, 0x5050505, 0x550055, 0x5555] 4 = true := by decide +kernel
def nc_16 := nc0 ch_16
theorem lb_16 : LowerBin 0x55555555 [0x11111111, 0x5050505, 0x550055, 0x5555] g_16 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_16 nc_16 (by decide +kernel)
def m_17 := 0x5555555500000000
def s_17 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_17 := 0x115151500000000
def ep_17 := 0x1400000000000014000000000000010404040000000001101010000000000000000000000000
def bds_17 : BList := [(m_2,s_2,4,g_2)]
def cc_17_0 : Nat → LPN := fun _ => []
def cur_17 : Nat → LPN := cc_17_0
def hc_17_0 (_ : Nat) := 0
def nh_17 : Nat → Nat := hc_17_0
def f_17 (_ : Nat) := (0,0)
def ch_17 := dN 0x5555555500000000 g_17 ep_17 1 1 bds_17 0 (dT 0x5555555500000000 [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000] 4 f_17) cur_17 nh_17
set_option maxHeartbeats 0 in
theorem rc_17 : dR 0x5555555500000000 g_17 ep_17 1 1 0 bds_17 (dT 0x5555555500000000 [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000] 4 f_17) (cur_17 0) (nh_17 0) [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000] 4 = true := by decide +kernel
def nc_17 := nc0 ch_17
theorem lb_17 : LowerBin 0x5555555500000000 [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000] g_17 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_17 nc_17 (by decide +kernel)
def m_18 := 0x3030303030303030
def s_18 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_18 := 0x10103010301030
def ep_18 := 0x1020000000001020000000000010002000200020000000000000000000000000000000000010100010001000
def bds_18 : BList := [(m_4,s_4,4,g_4)]
def cc_18_0 : Nat → LPN := fun _ => []
def cur_18 : Nat → LPN := cc_18_0
def hc_18_0 (_ : Nat) := 0
def nh_18 : Nat → Nat := hc_18_0
def f_18 (_ : Nat) := (0,0)
def ch_18 := dN 0x3030303030303030 g_18 ep_18 1 1 bds_18 0 (dT 0x3030303030303030 [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030] 4 f_18) cur_18 nh_18
set_option maxHeartbeats 0 in
theorem rc_18 : dR 0x3030303030303030 g_18 ep_18 1 1 0 bds_18 (dT 0x3030303030303030 [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030] 4 f_18) (cur_18 0) (nh_18 0) [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030] 4 = true := by decide +kernel
def nc_18 := nc0 ch_18
theorem lb_18 : LowerBin 0x3030303030303030 [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030] g_18 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_18 nc_18 (by decide +kernel)
def m_19 := 0xcc00cc00cc00cc
def s_19 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_19 := 0x400040004004c
def ep_19 := 0x4800000000000000480000000000000000000400040004000800000000000000000004000400040040
def bds_19 : BList := [(m_6,s_6,4,g_6)]
def cc_19_0 : Nat → LPN := fun _ => []
def cur_19 : Nat → LPN := cc_19_0
def hc_19_0 (_ : Nat) := 0
def nh_19 : Nat → Nat := hc_19_0
def f_19 (_ : Nat) := (0,0)
def ch_19 := dN 0xcc00cc00cc00cc g_19 ep_19 1 1 bds_19 0 (dT 0xcc00cc00cc00cc [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc] 4 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dR 0xcc00cc00cc00cc g_19 ep_19 1 1 0 bds_19 (dT 0xcc00cc00cc00cc [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc] 4 f_19) (cur_19 0) (nh_19 0) [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc] 4 = true := by decide +kernel
def nc_19 := nc0 ch_19
theorem lb_19 : LowerBin 0xcc00cc00cc00cc [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc] g_19 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_19 nc_19 (by decide +kernel)
def m_20 := 0x3300330033003300
def s_20 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_20 := 0x100110013001300
def ep_20 := 0x1200020000001000000000000000000000000000010000000200020000000000000000000100110010001000
def bds_20 : BList := [(m_7,s_7,4,g_7)]
def cc_20_0 : Nat → LPN := fun _ => []
def cur_20 : Nat → LPN := cc_20_0
def hc_20_0 (_ : Nat) := 0
def nh_20 : Nat → Nat := hc_20_0
def f_20 (_ : Nat) := (0,0)
def ch_20 := dN 0x3300330033003300 g_20 ep_20 1 1 bds_20 0 (dT 0x3300330033003300 [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300] 4 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dR 0x3300330033003300 g_20 ep_20 1 1 0 bds_20 (dT 0x3300330033003300 [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300] 4 f_20) (cur_20 0) (nh_20 0) [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300] 4 = true := by decide +kernel
def nc_20 := nc0 ch_20
theorem lb_20 : LowerBin 0x3300330033003300 [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300] g_20 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_20 nc_20 (by decide +kernel)
def m_21 := 0xcccc0000cccc
def s_21 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_21 := 0x40400000c4c
def ep_21 := 0x848000000000000000000000000000000400000040400000c0800000000000000000000040400000040
def bds_21 : BList := [(m_6,s_6,4,g_6)]
def cc_21_0 : Nat → LPN := fun _ => []
def cur_21 : Nat → LPN := cc_21_0
def hc_21_0 (_ : Nat) := 0
def nh_21 : Nat → Nat := hc_21_0
def f_21 (_ : Nat) := (0,0)
def ch_21 := dN 0xcccc0000cccc g_21 ep_21 1 1 bds_21 0 (dT 0xcccc0000cccc [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc] 4 f_21) cur_21 nh_21
set_option maxHeartbeats 0 in
theorem rc_21 : dR 0xcccc0000cccc g_21 ep_21 1 1 0 bds_21 (dT 0xcccc0000cccc [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc] 4 f_21) (cur_21 0) (nh_21 0) [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc] 4 = true := by decide +kernel
def nc_21 := nc0 ch_21
theorem lb_21 : LowerBin 0xcccc0000cccc [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc] g_21 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_21 nc_21 (by decide +kernel)
def m_22 := 0x3333000033330000
def s_22 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_22 := 0x111000013330000
def ep_22 := 0x1222000000000000000000000010000000200000010000000200000000000000000000000111000010000000
def bds_22 : BList := [(m_4,s_4,4,g_4)]
def cc_22_0 : Nat → LPN := fun _ => []
def cur_22 : Nat → LPN := cc_22_0
def hc_22_0 (_ : Nat) := 0
def nh_22 : Nat → Nat := hc_22_0
def f_22 (_ : Nat) := (0,0)
def ch_22 := dN 0x3333000033330000 g_22 ep_22 1 1 bds_22 0 (dT 0x3333000033330000 [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000] 4 f_22) cur_22 nh_22
set_option maxHeartbeats 0 in
theorem rc_22 : dR 0x3333000033330000 g_22 ep_22 1 1 0 bds_22 (dT 0x3333000033330000 [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000] 4 f_22) (cur_22 0) (nh_22 0) [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000] 4 = true := by decide +kernel
def nc_22 := nc0 ch_22
theorem lb_22 : LowerBin 0x3333000033330000 [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000] g_22 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_22 nc_22 (by decide +kernel)
def m_23 := 0xcccccccc
def s_23 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_23 := 0x40c4c
def ep_23 := 0xc4800000000000400400000000000040c0800000000000000000000000000040040
def bds_23 : BList := [(m_0,s_0,4,g_0)]
def cc_23_0 : Nat → LPN := fun _ => []
def cur_23 : Nat → LPN := cc_23_0
def hc_23_0 (_ : Nat) := 0
def nh_23 : Nat → Nat := hc_23_0
def f_23 (_ : Nat) := (0,0)
def ch_23 := dN 0xcccccccc g_23 ep_23 1 1 bds_23 0 (dT 0xcccccccc [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc] 4 f_23) cur_23 nh_23
set_option maxHeartbeats 0 in
theorem rc_23 : dR 0xcccccccc g_23 ep_23 1 1 0 bds_23 (dT 0xcccccccc [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc] 4 f_23) (cur_23 0) (nh_23 0) [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc] 4 = true := by decide +kernel
def nc_23 := nc0 ch_23
theorem lb_23 : LowerBin 0xcccccccc [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc] g_23 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_23 nc_23 (by decide +kernel)
def m_24 := 0x3333333300000000
def s_24 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_24 := 0x111113300000000
def ep_24 := 0x1022000000000010002200000000010000000000000000000000000000000111110000000000
def bds_24 : BList := [(m_5,s_5,4,g_5)]
def cc_24_0 : Nat → LPN := fun _ => []
def cur_24 : Nat → LPN := cc_24_0
def hc_24_0 (_ : Nat) := 0
def nh_24 : Nat → Nat := hc_24_0
def f_24 (_ : Nat) := (0,0)
def ch_24 := dN 0x3333333300000000 g_24 ep_24 1 1 bds_24 0 (dT 0x3333333300000000 [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000] 4 f_24) cur_24 nh_24
set_option maxHeartbeats 0 in
theorem rc_24 : dR 0x3333333300000000 g_24 ep_24 1 1 0 bds_24 (dT 0x3333333300000000 [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000] 4 f_24) (cur_24 0) (nh_24 0) [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000] 4 = true := by decide +kernel
def nc_24 := nc0 ch_24
theorem lb_24 : LowerBin 0x3333333300000000 [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000] g_24 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_24 nc_24 (by decide +kernel)
def m_25 := 0xf000f000f000f
def s_25 : List Nat := [0x5000500050005, 0x3000300030003, 0xf0000000f, 0xf000f]
def g_25 := 0x500070007000f
def ep_25 := 0x2000800000002000000080000000000000000000000000000000000000002000200000005000400040000
def bds_25 : BList := [(m_1,s_1,4,g_1)]
def cc_25_0 : Nat → LPN := fun _ => []
def cur_25 : Nat → LPN := cc_25_0
def hc_25_0 (_ : Nat) := 0
def nh_25 : Nat → Nat := hc_25_0
def f_25 (_ : Nat) := (0,0)
def ch_25 := dN 0xf000f000f000f g_25 ep_25 1 1 bds_25 0 (dT 0xf000f000f000f [0x5000500050005, 0x3000300030003, 0xf0000000f, 0xf000f] 4 f_25) cur_25 nh_25
set_option maxHeartbeats 0 in
theorem rc_25 : dR 0xf000f000f000f g_25 ep_25 1 1 0 bds_25 (dT 0xf000f000f000f [0x5000500050005, 0x3000300030003, 0xf0000000f, 0xf000f] 4 f_25) (cur_25 0) (nh_25 0) [0x5000500050005, 0x3000300030003, 0xf0000000f, 0xf000f] 4 = true := by decide +kernel
def nc_25 := nc0 ch_25
theorem lb_25 : LowerBin 0xf000f000f000f [0x5000500050005, 0x3000300030003, 0xf0000000f, 0xf000f] g_25 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_25 nc_25 (by decide +kernel)
def m_26 := 0xf000f000f000f0
def s_26 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_26 := 0x10003000300070
def ep_26 := 0x20004000000020000000400000000000000000000000000000000000100030003000200010000000000040
def bds_26 : BList := []
def cc_26_0 : Nat → LPN := uC 0x8608608608608608607e47e07e07e07e07647607607227207206e26c16c06a16a06a06a06a06a06a06246206206206205a45a05a05625605605225015004e14e04e04e04e04e04e04644604604604603e43e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 12 4095 5 31 10 1023 16 65535
def cur_26 : Nat → LPN := cc_26_0
def hc_26_0 (_ : Nat) := 0
def nh_26 : Nat → Nat := hc_26_0
def f_26 := uF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def ch_26 := dN 0xf000f000f000f0 g_26 ep_26 1 1 bds_26 64 (dT 0xf000f000f000f0 [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0] 5 f_26) cur_26 nh_26
set_option maxHeartbeats 0 in
theorem rc_26 : dR 0xf000f000f000f0 g_26 ep_26 1 1 64 bds_26 (dT 0xf000f000f000f0 [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0] 5 f_26) (cur_26 0) (nh_26 0) [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_0 : tB 0 32 ch_26 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_1 : tB 32 64 ch_26 = true := by decide +kernel
theorem nj_26_1 : ∀ i, 0 ≤ i → i < 64 → ch_26 i = true := bJ (fun _ h1 h2 => tA nb_26_0 h1 h2) (fun _ h1 h2 => tA nb_26_1 h1 h2)
theorem nc_26 : ∀ i, 0 ≤ i → i < 64 → ch_26 i = true := nj_26_1
theorem lb_26 : LowerBin 0xf000f000f000f0 [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0] g_26 6 :=
  lowerDagV5 (kn_nil) rc_26 nc_26 (by decide +kernel)
def m_27 := 0xf0f00000f0f0
def s_27 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_27 := 0x103000001070
def ep_27 := 0x4000000000000000000000002000000060000000000000000000001030000010200000100000001040
def bds_27 : BList := [(m_9,s_9,4,g_9)]
def cc_27_0 : Nat → LPN := fun _ => []
def cur_27 : Nat → LPN := cc_27_0
def hc_27_0 (_ : Nat) := 0
def nh_27 : Nat → Nat := hc_27_0
def f_27 (_ : Nat) := (0,0)
def ch_27 := dN 0xf0f00000f0f0 g_27 ep_27 1 1 bds_27 0 (dT 0xf0f00000f0f0 [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0] 4 f_27) cur_27 nh_27
set_option maxHeartbeats 0 in
theorem rc_27 : dR 0xf0f00000f0f0 g_27 ep_27 1 1 0 bds_27 (dT 0xf0f00000f0f0 [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0] 4 f_27) (cur_27 0) (nh_27 0) [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0] 4 = true := by decide +kernel
def nc_27 := nc0 ch_27
theorem lb_27 : LowerBin 0xf0f00000f0f0 [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0] g_27 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_27 nc_27 (by decide +kernel)
def m_28 := 0xf0f00000f0f00000
def s_28 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_28 := 0x10000010300000
def ep_28 := 0x1020000000000000000000000010000000200000000000000000000000100000103000000010000010000000
def bds_28 : BList := [(m_4,s_4,4,g_4)]
def cc_28_0 : Nat → LPN := fun _ => []
def cur_28 : Nat → LPN := cc_28_0
def hc_28_0 (_ : Nat) := 0
def nh_28 : Nat → Nat := hc_28_0
def f_28 (_ : Nat) := (0,0)
def ch_28 := dN 0xf0f00000f0f00000 g_28 ep_28 1 1 bds_28 0 (dT 0xf0f00000f0f00000 [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000] 4 f_28) cur_28 nh_28
set_option maxHeartbeats 0 in
theorem rc_28 : dR 0xf0f00000f0f00000 g_28 ep_28 1 1 0 bds_28 (dT 0xf0f00000f0f00000 [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000] 4 f_28) (cur_28 0) (nh_28 0) [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000] 4 = true := by decide +kernel
def nc_28 := nc0 ch_28
theorem lb_28 : LowerBin 0xf0f00000f0f00000 [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000] g_28 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_28 nc_28 (by decide +kernel)
def m_29 := 0xf0f0f0f0
def s_29 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_29 := 0x10301070
def ep_29 := 0x400000000000200060000000000000000000000000103010200000000010001040
def bds_29 : BList := [(m_9,s_9,4,g_9)]
def cc_29_0 : Nat → LPN := fun _ => []
def cur_29 : Nat → LPN := cc_29_0
def hc_29_0 (_ : Nat) := 0
def nh_29 : Nat → Nat := hc_29_0
def f_29 (_ : Nat) := (0,0)
def ch_29 := dN 0xf0f0f0f0 g_29 ep_29 1 1 bds_29 0 (dT 0xf0f0f0f0 [0x50505050, 0x30303030, 0xf000f0, 0xf0f0] 4 f_29) cur_29 nh_29
set_option maxHeartbeats 0 in
theorem rc_29 : dR 0xf0f0f0f0 g_29 ep_29 1 1 0 bds_29 (dT 0xf0f0f0f0 [0x50505050, 0x30303030, 0xf000f0, 0xf0f0] 4 f_29) (cur_29 0) (nh_29 0) [0x50505050, 0x30303030, 0xf000f0, 0xf0f0] 4 = true := by decide +kernel
def nc_29 := nc0 ch_29
theorem lb_29 : LowerBin 0xf0f0f0f0 [0x50505050, 0x30303030, 0xf000f0, 0xf0f0] g_29 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_29 nc_29 (by decide +kernel)
def m_30 := 0xf0f0f0f00000000
def s_30 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_30 := 0x105050700000000
def ep_30 := 0x402000000000004000200000000000000000000000001000002000000000105050400000000
def bds_30 : BList := []
def cc_30_0 : Nat → LPN := uC 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 4095 5 31 10 1023 16 65535
def cur_30 : Nat → LPN := cc_30_0
def hc_30_0 (_ : Nat) := 0
def nh_30 : Nat → Nat := hc_30_0
def f_30 := uF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_30 := dN 0xf0f0f0f00000000 g_30 ep_30 1 1 bds_30 64 (dT 0xf0f0f0f00000000 [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000] 5 f_30) cur_30 nh_30
set_option maxHeartbeats 0 in
theorem rc_30 : dR 0xf0f0f0f00000000 g_30 ep_30 1 1 64 bds_30 (dT 0xf0f0f0f00000000 [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000] 5 f_30) (cur_30 0) (nh_30 0) [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_0 : tB 0 32 ch_30 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_1 : tB 32 64 ch_30 = true := by decide +kernel
theorem nj_30_1 : ∀ i, 0 ≤ i → i < 64 → ch_30 i = true := bJ (fun _ h1 h2 => tA nb_30_0 h1 h2) (fun _ h1 h2 => tA nb_30_1 h1 h2)
theorem nc_30 : ∀ i, 0 ≤ i → i < 64 → ch_30 i = true := nj_30_1
theorem lb_30 : LowerBin 0xf0f0f0f00000000 [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000] g_30 6 :=
  lowerDagV5 (kn_nil) rc_30 nc_30 (by decide +kernel)
def m_31 := 0xf0f0f0f000000000
def s_31 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_31 := 0x10103000000000
def ep_31 := 0x1020000000000010002000000000000000000000000000101030000000000010100000000000
def bds_31 : BList := [(m_5,s_5,4,g_5)]
def cc_31_0 : Nat → LPN := fun _ => []
def cur_31 : Nat → LPN := cc_31_0
def hc_31_0 (_ : Nat) := 0
def nh_31 : Nat → Nat := hc_31_0
def f_31 (_ : Nat) := (0,0)
def ch_31 := dN 0xf0f0f0f000000000 g_31 ep_31 1 1 bds_31 0 (dT 0xf0f0f0f000000000 [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000] 4 f_31) cur_31 nh_31
set_option maxHeartbeats 0 in
theorem rc_31 : dR 0xf0f0f0f000000000 g_31 ep_31 1 1 0 bds_31 (dT 0xf0f0f0f000000000 [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000] 4 f_31) (cur_31 0) (nh_31 0) [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000] 4 = true := by decide +kernel
def nc_31 := nc0 ch_31
theorem lb_31 : LowerBin 0xf0f0f0f000000000 [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000] g_31 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_31 nc_31 (by decide +kernel)
def m_32 := 0xff000000ff
def s_32 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_32 := 0x370000007f
def ep_32 := 0x4800000000000000000000000000000000000000040000000800000032000000200000000400000040
def bds_32 : BList := [(m_6,s_6,4,g_6)]
def cc_32_0 : Nat → LPN := fun _ => []
def cur_32 : Nat → LPN := cc_32_0
def hc_32_0 (_ : Nat) := 0
def nh_32 : Nat → Nat := hc_32_0
def f_32 (_ : Nat) := (0,0)
def ch_32 := dN 0xff000000ff g_32 ep_32 1 1 bds_32 0 (dT 0xff000000ff [0x5500000055, 0x3300000033, 0xf0000000f, 0xff] 4 f_32) cur_32 nh_32
set_option maxHeartbeats 0 in
theorem rc_32 : dR 0xff000000ff g_32 ep_32 1 1 0 bds_32 (dT 0xff000000ff [0x5500000055, 0x3300000033, 0xf0000000f, 0xff] 4 f_32) (cur_32 0) (nh_32 0) [0x5500000055, 0x3300000033, 0xf0000000f, 0xff] 4 = true := by decide +kernel
def nc_32 := nc0 ch_32
theorem lb_32 : LowerBin 0xff000000ff [0x5500000055, 0x3300000033, 0xf0000000f, 0xff] g_32 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_32 nc_32 (by decide +kernel)
def m_33 := 0xff000000ff000000
def s_33 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_33 := 0x100000013000000
def ep_33 := 0x1200000000000000000000000000000000000000010000000200000001000000130000000100000010000000
def bds_33 : BList := [(m_7,s_7,4,g_7)]
def cc_33_0 : Nat → LPN := fun _ => []
def cur_33 : Nat → LPN := cc_33_0
def hc_33_0 (_ : Nat) := 0
def nh_33 : Nat → Nat := hc_33_0
def f_33 (_ : Nat) := (0,0)
def ch_33 := dN 0xff000000ff000000 g_33 ep_33 1 1 bds_33 0 (dT 0xff000000ff000000 [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000] 4 f_33) cur_33 nh_33
set_option maxHeartbeats 0 in
theorem rc_33 : dR 0xff000000ff000000 g_33 ep_33 1 1 0 bds_33 (dT 0xff000000ff000000 [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000] 4 f_33) (cur_33 0) (nh_33 0) [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000] 4 = true := by decide +kernel
def nc_33 := nc0 ch_33
theorem lb_33 : LowerBin 0xff000000ff000000 [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000] g_33 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_33 nc_33 (by decide +kernel)
def m_34 := 0xff00ff
def s_34 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_34 := 0x37007f
def ep_34 := 0x480000000000000000000000000004000800000000003200200000000000040040
def bds_34 : BList := [(m_8,s_8,4,g_8)]
def cc_34_0 : Nat → LPN := fun _ => []
def cur_34 : Nat → LPN := cc_34_0
def hc_34_0 (_ : Nat) := 0
def nh_34 : Nat → Nat := hc_34_0
def f_34 (_ : Nat) := (0,0)
def ch_34 := dN 0xff00ff g_34 ep_34 1 1 bds_34 0 (dT 0xff00ff [0x550055, 0x330033, 0xf000f, 0xff] 4 f_34) cur_34 nh_34
set_option maxHeartbeats 0 in
theorem rc_34 : dR 0xff00ff g_34 ep_34 1 1 0 bds_34 (dT 0xff00ff [0x550055, 0x330033, 0xf000f, 0xff] 4 f_34) (cur_34 0) (nh_34 0) [0x550055, 0x330033, 0xf000f, 0xff] 4 = true := by decide +kernel
def nc_34 := nc0 ch_34
theorem lb_34 : LowerBin 0xff00ff [0x550055, 0x330033, 0xf000f, 0xff] g_34 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_34 nc_34 (by decide +kernel)
def m_35 := 0xff00ff0000000000
def s_35 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_35 := 0x100150000000000
def ep_35 := 0x1400000000000000000000000000010004000000000001001000000000000100150000000000
def bds_35 : BList := [(m_2,s_2,4,g_2)]
def cc_35_0 : Nat → LPN := fun _ => []
def cur_35 : Nat → LPN := cc_35_0
def hc_35_0 (_ : Nat) := 0
def nh_35 : Nat → Nat := hc_35_0
def f_35 (_ : Nat) := (0,0)
def ch_35 := dN 0xff00ff0000000000 g_35 ep_35 1 1 bds_35 0 (dT 0xff00ff0000000000 [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000] 4 f_35) cur_35 nh_35
set_option maxHeartbeats 0 in
theorem rc_35 : dR 0xff00ff0000000000 g_35 ep_35 1 1 0 bds_35 (dT 0xff00ff0000000000 [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000] 4 f_35) (cur_35 0) (nh_35 0) [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000] 4 = true := by decide +kernel
def nc_35 := nc0 ch_35
theorem lb_35 : LowerBin 0xff00ff0000000000 [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000] g_35 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_35 nc_35 (by decide +kernel)
def m_36 := 0xffff
def s_36 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_36 := 0x1f7f
def ep_36 := 0x600000000000000e0800000000000010200000000000001040
def bds_36 : BList := [(m_9,s_9,4,g_9)]
def cc_36_0 : Nat → LPN := fun _ => []
def cur_36 : Nat → LPN := cc_36_0
def hc_36_0 (_ : Nat) := 0
def nh_36 : Nat → Nat := hc_36_0
def f_36 (_ : Nat) := (0,0)
def ch_36 := dN 0xffff g_36 ep_36 1 1 bds_36 0 (dT 0xffff [0x5555, 0x3333, 0xf0f, 0xff] 4 f_36) cur_36 nh_36
set_option maxHeartbeats 0 in
theorem rc_36 : dR 0xffff g_36 ep_36 1 1 0 bds_36 (dT 0xffff [0x5555, 0x3333, 0xf0f, 0xff] 4 f_36) (cur_36 0) (nh_36 0) [0x5555, 0x3333, 0xf0f, 0xff] 4 = true := by decide +kernel
def nc_36 := nc0 ch_36
theorem lb_36 : LowerBin 0xffff [0x5555, 0x3333, 0xf0f, 0xff] g_36 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_36 nc_36 (by decide +kernel)
def m_37 := 0xffff0000
def s_37 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_37 := 0x13370000
def ep_37 := 0x240000000000000204000000000000133200000000000010040000
def bds_37 : BList := []
def cc_37_0 : Nat → LPN := uC 0x8608608608608608607e47e07e07e07e07647607607227207206e26c16c06a16a06a06a06a06a06a06246206206206205a45a05a05625605605225015004e14e04e04e04e04e04e04644604604604603e43e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 12 4095 5 31 10 1023 16 65535
def cur_37 : Nat → LPN := cc_37_0
def hc_37_0 (_ : Nat) := 0
def nh_37 : Nat → Nat := hc_37_0
def f_37 := uF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def ch_37 := dN 0xffff0000 g_37 ep_37 1 1 bds_37 64 (dT 0xffff0000 [0x55550000, 0x33330000, 0xf0f0000, 0xff0000] 5 f_37) cur_37 nh_37
set_option maxHeartbeats 0 in
theorem rc_37 : dR 0xffff0000 g_37 ep_37 1 1 64 bds_37 (dT 0xffff0000 [0x55550000, 0x33330000, 0xf0f0000, 0xff0000] 5 f_37) (cur_37 0) (nh_37 0) [0x55550000, 0x33330000, 0xf0f0000, 0xff0000] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_0 : tB 0 32 ch_37 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_1 : tB 32 64 ch_37 = true := by decide +kernel
theorem nj_37_1 : ∀ i, 0 ≤ i → i < 64 → ch_37 i = true := bJ (fun _ h1 h2 => tA nb_37_0 h1 h2) (fun _ h1 h2 => tA nb_37_1 h1 h2)
theorem nc_37 : ∀ i, 0 ≤ i → i < 64 → ch_37 i = true := nj_37_1
theorem lb_37 : LowerBin 0xffff0000 [0x55550000, 0x33330000, 0xf0f0000, 0xff0000] g_37 6 :=
  lowerDagV5 (kn_nil) rc_37 nc_37 (by decide +kernel)
def m_38 := 0xffff000000000000
def s_38 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_38 := 0x115000000000000
def ep_38 := 0x14000000000000010400000000000001100000000000000115000000000000
def bds_38 : BList := [(m_3,s_3,4,g_3)]
def cc_38_0 : Nat → LPN := fun _ => []
def cur_38 : Nat → LPN := cc_38_0
def hc_38_0 (_ : Nat) := 0
def nh_38 : Nat → Nat := hc_38_0
def f_38 (_ : Nat) := (0,0)
def ch_38 := dN 0xffff000000000000 g_38 ep_38 1 1 bds_38 0 (dT 0xffff000000000000 [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000] 4 f_38) cur_38 nh_38
set_option maxHeartbeats 0 in
theorem rc_38 : dR 0xffff000000000000 g_38 ep_38 1 1 0 bds_38 (dT 0xffff000000000000 [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000] 4 f_38) (cur_38 0) (nh_38 0) [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000] 4 = true := by decide +kernel
def nc_38 := nc0 ch_38
theorem lb_38 : LowerBin 0xffff000000000000 [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000] g_38 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_38 nc_38 (by decide +kernel)
def m_39 := 0x1144114411441144
def s_39 : List Nat := [0x44004400440044, 0x104010401040104, 0x114400001144, 0x11441144]
def g_39 := 0x104110411041144
def ep_39 := 0x1000004000001000000000400000000000000000010400040004000000000000000000000000000000000000
def bds_39 : BList := []
def cc_39_0 : Nat → LPN := uC 0x16ac58b12a44890e8701 0x193430d19282090d28209263a88d9d3a54d903a10d800f 7 127 3 7 10 1023 14 16383
def cur_39 : Nat → LPN := cc_39_0
def hc_39_0 (_ : Nat) := 0
def nh_39 : Nat → Nat := hc_39_0
def f_39 := uF 0xc7463629d64a0a6c43a494209086c00f 3 10
def ch_39 := dN 0x1144114411441144 g_39 ep_39 1 1 bds_39 10 (dT 0x1144114411441144 [0x44004400440044, 0x104010401040104, 0x114400001144, 0x11441144] 4 f_39) cur_39 nh_39
set_option maxHeartbeats 0 in
theorem rc_39 : dR 0x1144114411441144 g_39 ep_39 1 1 10 bds_39 (dT 0x1144114411441144 [0x44004400440044, 0x104010401040104, 0x114400001144, 0x11441144] 4 f_39) (cur_39 0) (nh_39 0) [0x44004400440044, 0x104010401040104, 0x114400001144, 0x11441144] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_0 : tB 0 10 ch_39 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 10 → ch_39 i = true := fun _ h1 h2 => tA nb_39_0 h1 h2
theorem lb_39 : LowerBin 0x1144114411441144 [0x44004400440044, 0x104010401040104, 0x114400001144, 0x11441144] g_39 5 :=
  lowerDagV5 (kn_nil) rc_39 nc_39 (by decide +kernel)
def m_40 := 0x1111444411114444
def s_40 : List Nat := [0x444400004444, 0x101040401010404, 0x11004400110044, 0x11114444]
def g_40 := 0x111040411110444
def ep_40 := 0x1000004000000000000000000010000000000040010004040000040000000000000000000000000000000000
def bds_40 : BList := []
def cc_40_0 : Nat → LPN := uC 0x1a2d58952244890e8701 0x1d283091e3420d0d2420a263a88d993a54d903a10d800f 7 127 3 7 10 1023 14 16383
def cur_40 : Nat → LPN := cc_40_0
def hc_40_0 (_ : Nat) := 0
def nh_40 : Nat → Nat := hc_40_0
def f_40 := uF 0xc74636f1a14e8a6c43a49220a086c00f 3 10
def ch_40 := dN 0x1111444411114444 g_40 ep_40 1 1 bds_40 10 (dT 0x1111444411114444 [0x444400004444, 0x101040401010404, 0x11004400110044, 0x11114444] 4 f_40) cur_40 nh_40
set_option maxHeartbeats 0 in
theorem rc_40 : dR 0x1111444411114444 g_40 ep_40 1 1 10 bds_40 (dT 0x1111444411114444 [0x444400004444, 0x101040401010404, 0x11004400110044, 0x11114444] 4 f_40) (cur_40 0) (nh_40 0) [0x444400004444, 0x101040401010404, 0x11004400110044, 0x11114444] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_0 : tB 0 10 ch_40 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 10 → ch_40 i = true := fun _ h1 h2 => tA nb_40_0 h1 h2
theorem lb_40 : LowerBin 0x1111444411114444 [0x444400004444, 0x101040401010404, 0x11004400110044, 0x11114444] g_40 5 :=
  lowerDagV5 (kn_nil) rc_40 nc_40 (by decide +kernel)
def m_41 := 0x1111111144444444
def s_41 : List Nat := [0x44444444, 0x101010104040404, 0x11001100440044, 0x111100004444]
def g_41 := 0x111111100040444
def ep_41 := 0x1000000004400010000000040040010000000004040000000000000000000000000000000000
def bds_41 : BList := [(m_0,s_0,4,g_0)]
def cc_41_0 : Nat → LPN := uC 0xa02809c65294250906408c5f47c1f0785c2701c06c5b06856458160545324c13048520444d407001 0xdc619492e146634bc69bd134946124b05114c1e9234187a68d4d2322413c7268c060e901534183054906921e343298451040c7a3fec77c8deb19d13f9a7724dd699a92f4a56849c291800f 10 1023 4 15 10 1023 15 32767
def cur_41 : Nat → LPN := cc_41_0
def hc_41_0 : Nat → Nat := uH 0xb4369cd983e5430000000000000000024058335d8d673d9030000000000000000017c5523514d363ccc3000000000000000000b8501b4001 0x1555aaad555b1aaad556aaad8d556aab5556c622222222223 14 16383 6 63
def nh_41 : Nat → Nat := hc_41_0
def f_41 := uF 0x18fc31d8637b68964a331a5924bc6960a0319853f0a7614dd922313c7a68c4d1a9a30180a6614bc295852714682530a9209441a482060291800f 5 10
def ch_41 := dN 0x1111111144444444 g_41 ep_41 1 1 bds_41 31 (dT 0x1111111144444444 [0x44444444, 0x101010104040404, 0x11001100440044, 0x111100004444] 5 f_41) cur_41 nh_41
set_option maxHeartbeats 0 in
theorem rc_41 : dR 0x1111111144444444 g_41 ep_41 1 1 31 bds_41 (dT 0x1111111144444444 [0x44444444, 0x101010104040404, 0x11001100440044, 0x111100004444] 5 f_41) (cur_41 0) (nh_41 0) [0x44444444, 0x101010104040404, 0x11001100440044, 0x111100004444] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_0 : tB 0 31 ch_41 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 31 → ch_41 i = true := fun _ h1 h2 => tA nb_41_0 h1 h2
theorem lb_41 : LowerBin 0x1111111144444444 [0x44444444, 0x101010104040404, 0x11001100440044, 0x111100004444] g_41 6 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_41 nc_41 (by decide +kernel)
def m_42 := 0x5500550000550055
def s_42 : List Nat := [0x1100110000110011, 0x500050000050005, 0x550055, 0x550000000055]
def g_42 := 0x100150000150055
def ep_42 := 0x1400000000400000000000000000010004000004000001001000001000000000000000000000
def bds_42 : BList := [(m_2,s_2,4,g_2)]
def cc_42_0 : Nat → LPN := uC 0xa02809c65294250906408c5f47c1f0785c2701c06c5b06856458160545324c13048520444d407001 0xdc619492e126634bc69bd134946124b04914c1e9234147a68d4d2322413c7268c050e901534182854906921e343298451040a7a3fec77c8deb19d13f9a7724dd699a92f4a56849c291800f 10 1023 4 15 10 1023 15 32767
def cur_42 : Nat → LPN := cc_42_0
def hc_42_0 : Nat → Nat := uH 0xb4369cd983e5430000000000000000024058335d8d673d9030000000000000000017c5523514d363ccc3000000000000000000b8501b4001 0x1555aaad555b1aaad556aaad8d556aab5556c622222222223 14 16383 6 63
def nh_42 : Nat → Nat := hc_42_0
def f_42 := uF 0x18fc31d8637b68964a331a5924bc696090319853f0a7614dd922313c7a68c4d1a9a30140a6614bc295852714682530a9209441a482050291800f 5 10
def ch_42 := dN 0x5500550000550055 g_42 ep_42 1 1 bds_42 31 (dT 0x5500550000550055 [0x1100110000110011, 0x500050000050005, 0x550055, 0x550000000055] 5 f_42) cur_42 nh_42
set_option maxHeartbeats 0 in
theorem rc_42 : dR 0x5500550000550055 g_42 ep_42 1 1 31 bds_42 (dT 0x5500550000550055 [0x1100110000110011, 0x500050000050005, 0x550055, 0x550000000055] 5 f_42) (cur_42 0) (nh_42 0) [0x1100110000110011, 0x500050000050005, 0x550055, 0x550000000055] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_0 : tB 0 31 ch_42 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 31 → ch_42 i = true := fun _ h1 h2 => tA nb_42_0 h1 h2
theorem lb_42 : LowerBin 0x5500550000550055 [0x1100110000110011, 0x500050000050005, 0x550055, 0x550000000055] g_42 6 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_42 nc_42 (by decide +kernel)
def m_43 := 0x5555000000005555
def s_43 : List Nat := [0x1111000000001111, 0x505000000000505, 0x55000000000055, 0x5555]
def g_43 := 0x115000000001555
def ep_43 := 0x14000000000040010400000000040001100000000010000000000000000000
def bds_43 : BList := [(m_3,s_3,4,g_3)]
def cc_43_0 : Nat → LPN := uC 0xa02809c65294250906408c5f47c1f0785c2701c06c5b06856458160545324c13048520444d407001 0xdc619492e126634bc69bd134946124b04914c1e9234147a68d4d2322413c7268c050e901534182854906921e343298451040a7a3fec77c8deb19d13f9a7724dd699a92f4a56849c291800f 10 1023 4 15 10 1023 15 32767
def cur_43 : Nat → LPN := cc_43_0
def hc_43_0 : Nat → Nat := uH 0xb4369cd983e5430000000000000000024058335d8d673d9030000000000000000017c5523514d363ccc3000000000000000000b8501b4001 0x1555aaad555b1aaad556aaad8d556aab5556c622222222223 14 16383 6 63
def nh_43 : Nat → Nat := hc_43_0
def f_43 := uF 0x18fc31d8637b68964a331a5924bc696090319853f0a7614dd922313c7a68c4d1a9a30140a6614bc295852714682530a9209441a482050291800f 5 10
def ch_43 := dN 0x5555000000005555 g_43 ep_43 1 1 bds_43 31 (dT 0x5555000000005555 [0x1111000000001111, 0x505000000000505, 0x55000000000055, 0x5555] 5 f_43) cur_43 nh_43
set_option maxHeartbeats 0 in
theorem rc_43 : dR 0x5555000000005555 g_43 ep_43 1 1 31 bds_43 (dT 0x5555000000005555 [0x1111000000001111, 0x505000000000505, 0x55000000000055, 0x5555] 5 f_43) (cur_43 0) (nh_43 0) [0x1111000000001111, 0x505000000000505, 0x55000000000055, 0x5555] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_0 : tB 0 31 ch_43 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 31 → ch_43 i = true := fun _ h1 h2 => tA nb_43_0 h1 h2
theorem lb_43 : LowerBin 0x5555000000005555 [0x1111000000001111, 0x505000000000505, 0x55000000000055, 0x5555] g_43 6 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_43 nc_43 (by decide +kernel)
def m_44 := 0x3030030330300303
def s_44 : List Nat := [0x1010010110100101, 0x30300000303, 0x30000300300003, 0x30300303]
def g_44 := 0x10010310300303
def ep_44 := 0x1020020000000000000000000010000200200000000000000000000000000000000000000010010010000000
def bds_44 : BList := [(m_4,s_4,4,g_4)]
def cc_44_0 : Nat → LPN := uC 0xa02809c65294241902408c5f47c1f0785c2701c06c5b06856458160545324c13048520444d407001 0xdc61a492e126a34bc69bd132926028b04910c1e1234147868d0d22a2403c7068c090e101434182850906121d34309841104127a3fec77c8deb19d03f987720dd619a82f4856809c211800f 10 1023 4 15 10 1023 15 32767
def cur_44 : Nat → LPN := cc_44_0
def hc_44_0 : Nat → Nat := uH 0xb0368cd943e4430000000000000000023057f35c8d633d80300000000000000000174350350cd343cc43000000000000000000b8301b4001 0x1555aaad555b1aaad556aaadb555aaad555b622222222223 14 16383 6 63
def nh_44 : Nat → Nat := hc_44_0
def f_44 := uF 0x18fc31d8637b689a8d2c925828bc696090319843f087610dd8a2303c7868c0d1a1a3024086610bc215842712682130a12084418482090211800f 5 10
def ch_44 := dN 0x3030030330300303 g_44 ep_44 1 1 bds_44 31 (dT 0x3030030330300303 [0x1010010110100101, 0x30300000303, 0x30000300300003, 0x30300303] 5 f_44) cur_44 nh_44
set_option maxHeartbeats 0 in
theorem rc_44 : dR 0x3030030330300303 g_44 ep_44 1 1 31 bds_44 (dT 0x3030030330300303 [0x1010010110100101, 0x30300000303, 0x30000300300003, 0x30300303] 5 f_44) (cur_44 0) (nh_44 0) [0x1010010110100101, 0x30300000303, 0x30000300300003, 0x30300303] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_0 : tB 0 31 ch_44 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 31 → ch_44 i = true := fun _ h1 h2 => tA nb_44_0 h1 h2
theorem lb_44 : LowerBin 0x3030030330300303 [0x1010010110100101, 0x30300000303, 0x30000300300003, 0x30300303] g_44 6 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_44 nc_44 (by decide +kernel)
def m_45 := 0xcc00cc0000cc00cc
def s_45 : List Nat := [0x4400440000440044, 0xc000c00000c000c, 0xcc00cc, 0xcc00000000cc]
def g_45 := 0x4000004004c
def ep_45 := 0x400000000480000000000000000000004000004000800000000000000000000040000040040
def bds_45 : BList := [(m_8,s_8,4,g_8)]
def cc_45_0 : Nat → LPN := uC 0xa0280a02719862488220809f17c1f07c1e174594641905c96158160581515050440100388d107001 0xc46178c2d18714cda81a1030985c30b688e4c1a984a4c8c80c4c20203a306860c9108980d2046907d0049018302460308051a7a3fec7798deb19d13f9a76f4dd699a92f4a56549c291800f 10 1023 4 15 10 1023 15 32767
def cur_45 : Nat → LPN := cc_45_0
def hc_45_0 : Nat → Nat := uH 0xae3684d0000000000278300000009b0e30f7f35c8d00000000001bc300000006c0d74f50350cd0000000000100300000003d0cb8f01b4001 0x5556aab6d555aaad556daaab555aaadb555622222222223 14 16383 6 63
def nh_45 : Nat → Nat := hc_45_0
def f_45 := uF 0x18fc31de94cd281a10031bdd30b8616d10319853f0a77093212040400a6ed8c1a1832440a6614bc2959b48368060c02938e30184028d0291800f 5 10
def ch_45 := dN 0xcc00cc0000cc00cc g_45 ep_45 1 1 bds_45 31 (dT 0xcc00cc0000cc00cc [0x4400440000440044, 0xc000c00000c000c, 0xcc00cc, 0xcc00000000cc] 5 f_45) cur_45 nh_45
set_option maxHeartbeats 0 in
theorem rc_45 : dR 0xcc00cc0000cc00cc g_45 ep_45 1 1 31 bds_45 (dT 0xcc00cc0000cc00cc [0x4400440000440044, 0xc000c00000c000c, 0xcc00cc, 0xcc00000000cc] 5 f_45) (cur_45 0) (nh_45 0) [0x4400440000440044, 0xc000c00000c000c, 0xcc00cc, 0xcc00000000cc] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_0 : tB 0 31 ch_45 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 31 → ch_45 i = true := fun _ h1 h2 => tA nb_45_0 h1 h2
theorem lb_45 : LowerBin 0xcc00cc0000cc00cc [0x4400440000440044, 0xc000c00000c000c, 0xcc00cc, 0xcc00000000cc] g_45 6 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_45 nc_45 (by decide +kernel)
def m_46 := 0x3030c0c03030c0c0
def s_46 : List Nat := [0x1010404010104040, 0xc0c00000c0c0, 0x3000c0003000c0, 0x3030c0c0]
def g_46 := 0x10000010300040
def ep_46 := 0x1020004000000000000000000010000000200040000000000000000000000000000000000010000010000040
def bds_46 : BList := [(m_4,s_4,4,g_4)]
def cc_46_0 : Nat → LPN := uC 0xa02809c6709862488220809f17c1f07c1e174594641905c96158160581515050440100388d107001 0xc24178c2d18714cd899a10309e5c30b688e0c1a184a4c8c8105318183a306a78c5108180c2046907d00c9e0820246034b049a7a3fec7798deb19d03f9876f0dd619a82f4856509c211800f 10 1023 4 15 10 1023 15 32767
def cur_46 : Nat → LPN := cc_46_0
def hc_46_0 : Nat → Nat := uH 0xb4369cd0000000000288500000009f0e40f8335d8d00000000001c4500000006e0d7cf523514d0000000000100500000003d0cb8f01b4001 0x1555aaad2d555aaad55696aaad556aab4b555622222222223 14 16383 6 63
def nh_46 : Nat → Nat := hc_46_0
def f_46 := uF 0x18fc31de94cd099a10031bdd3cb8616d10319843f08770932120414c086ed8c1a9e3144086610bc2159b48368064f02138e301a5824d0211800f 5 10
def ch_46 := dN 0x3030c0c03030c0c0 g_46 ep_46 1 1 bds_46 31 (dT 0x3030c0c03030c0c0 [0x1010404010104040, 0xc0c00000c0c0, 0x3000c0003000c0, 0x3030c0c0] 5 f_46) cur_46 nh_46
set_option maxHeartbeats 0 in
theorem rc_46 : dR 0x3030c0c03030c0c0 g_46 ep_46 1 1 31 bds_46 (dT 0x3030c0c03030c0c0 [0x1010404010104040, 0xc0c00000c0c0, 0x3000c0003000c0, 0x3030c0c0] 5 f_46) (cur_46 0) (nh_46 0) [0x1010404010104040, 0xc0c00000c0c0, 0x3000c0003000c0, 0x3030c0c0] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_0 : tB 0 31 ch_46 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 31 → ch_46 i = true := fun _ h1 h2 => tA nb_46_0 h1 h2
theorem lb_46 : LowerBin 0x3030c0c03030c0c0 [0x1010404010104040, 0xc0c00000c0c0, 0x3000c0003000c0, 0x3030c0c0] g_46 6 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_46 nc_46 (by decide +kernel)
def m_47 := 0x66006600660066
def s_47 : List Nat := [0x22002200220022, 0x6000600060006, 0x6600000066, 0x660066]
def g_47 := 0x4002600260066
def ep_47 := 0x22004000000022000000400000000000000000000400040004000000000000000000000000000000000000
def bds_47 : BList := []
def cc_47_0 : Nat → LPN := uC 0xcc61 0xa3a63600f 4 15 2 3 10 1023 12 4095
def cur_47 : Nat → LPN := cc_47_0
def hc_47_0 (_ : Nat) := 0
def nh_47 : Nat → Nat := hc_47_0
def f_47 := uF 0x18eb1b00f 1 10
def ch_47 := dN 0x66006600660066 g_47 ep_47 1 1 bds_47 3 (dT 0x66006600660066 [0x22002200220022, 0x6000600060006, 0x6600000066, 0x660066] 4 f_47) cur_47 nh_47
set_option maxHeartbeats 0 in
theorem rc_47 : dR 0x66006600660066 g_47 ep_47 1 1 3 bds_47 (dT 0x66006600660066 [0x22002200220022, 0x6000600060006, 0x6600000066, 0x660066] 4 f_47) (cur_47 0) (nh_47 0) [0x22002200220022, 0x6000600060006, 0x6600000066, 0x660066] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_0 : tB 0 3 ch_47 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 3 → ch_47 i = true := fun _ h1 h2 => tA nb_47_0 h1 h2
theorem lb_47 : LowerBin 0x66006600660066 [0x22002200220022, 0x6000600060006, 0x6600000066, 0x660066] g_47 5 :=
  lowerDagV5 (kn_nil) rc_47 nc_47 (by decide +kernel)
def m_48 := 0xaa005500aa0055
def s_48 : List Nat := [0x5500000055, 0x22001100220011, 0xa0005000a0005, 0xaa0055]
def g_48 := 0x1500220055
def ep_48 := 0x22004000000000000000000000000000000000000000040000000000000010002200000000000000000000
def bds_48 : BList := []
def cc_48_0 : Nat → LPN := uC 0xb146850a14214072e0701 0x282464d141438d263a88d9d29448482d109400f 7 127 3 7 10 1023 14 16383
def cur_48 : Nat → LPN := cc_48_0
def hc_48_0 (_ : Nat) := 0
def nh_48 : Nat → Nat := hc_48_0
def f_48 := uF 0x282418e863614a5534505052138d042d109400f 4 10
def ch_48 := dN 0xaa005500aa0055 g_48 ep_48 1 1 bds_48 11 (dT 0xaa005500aa0055 [0x5500000055, 0x22001100220011, 0xa0005000a0005, 0xaa0055] 4 f_48) cur_48 nh_48
set_option maxHeartbeats 0 in
theorem rc_48 : dR 0xaa005500aa0055 g_48 ep_48 1 1 11 bds_48 (dT 0xaa005500aa0055 [0x5500000055, 0x22001100220011, 0xa0005000a0005, 0xaa0055] 4 f_48) (cur_48 0) (nh_48 0) [0x5500000055, 0x22001100220011, 0xa0005000a0005, 0xaa0055] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_0 : tB 0 11 ch_48 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 11 → ch_48 i = true := fun _ h1 h2 => tA nb_48_0 h1 h2
theorem lb_48 : LowerBin 0xaa005500aa0055 [0x5500000055, 0x22001100220011, 0xa0005000a0005, 0xaa0055] g_48 5 :=
  lowerDagV5 (kn_nil) rc_48 nc_48 (by decide +kernel)
def m_49 := 0xaa00aa00550055
def s_49 : List Nat := [0x550055, 0x22002200110011, 0xa000a00050005, 0xaa00000055]
def g_49 := 0x2200150055
def ep_49 := 0x22000000400000000000000000000000000004000000000022001000000000000000000000
def bds_49 : BList := []
def cc_49_0 : Nat → LPN := uC 0xb146850932244890e8701 0x292478d0c34209263a88d992d5495029108400f 7 127 3 7 10 1023 14 16383
def cur_49 : Nat → LPN := cc_49_0
def hc_49_0 (_ : Nat) := 0
def nh_49 : Nat → Nat := hc_49_0
def f_49 := uF 0x292418e863678d052d149442920d0824108400f 4 10
def ch_49 := dN 0xaa00aa00550055 g_49 ep_49 1 1 bds_49 11 (dT 0xaa00aa00550055 [0x550055, 0x22002200110011, 0xa000a00050005, 0xaa00000055] 4 f_49) cur_49 nh_49
set_option maxHeartbeats 0 in
theorem rc_49 : dR 0xaa00aa00550055 g_49 ep_49 1 1 11 bds_49 (dT 0xaa00aa00550055 [0x550055, 0x22002200110011, 0xa000a00050005, 0xaa00000055] 4 f_49) (cur_49 0) (nh_49 0) [0x550055, 0x22002200110011, 0xa000a00050005, 0xaa00000055] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_0 : tB 0 11 ch_49 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 11 → ch_49 i = true := fun _ h1 h2 => tA nb_49_0 h1 h2
theorem lb_49 : LowerBin 0xaa00aa00550055 [0x550055, 0x22002200110011, 0xa000a00050005, 0xaa00000055] g_49 5 :=
  lowerDagV5 (kn_nil) rc_49 nc_49 (by decide +kernel)
def m_50 := 0xff0000000000ff
def s_50 : List Nat := [0x55000000000055, 0x33000000000033, 0xf00000000000f, 0xff]
def g_50 := 0x1500000000007f
def ep_50 := 0x400000000000800100000000000200015000000000040
def bds_50 : BList := []
def cc_50_0 : Nat → LPN := uC 0x72e18b060c0681 0xb24b24d2d92a72652532400f 7 127 3 7 9 511 12 4095
def cur_50 : Nat → LPN := cc_50_0
def hc_50_0 (_ : Nat) := 0
def nh_50 : Nat → Nat := hc_50_0
def f_50 := uF 0x32db2432a32632532400f 3 9
def ch_50 := dN 0xff0000000000ff g_50 ep_50 1 1 bds_50 7 (dT 0xff0000000000ff [0x55000000000055, 0x33000000000033, 0xf00000000000f, 0xff] 4 f_50) cur_50 nh_50
set_option maxHeartbeats 0 in
theorem rc_50 : dR 0xff0000000000ff g_50 ep_50 1 1 7 bds_50 (dT 0xff0000000000ff [0x55000000000055, 0x33000000000033, 0xf00000000000f, 0xff] 4 f_50) (cur_50 0) (nh_50 0) [0x55000000000055, 0x33000000000033, 0xf00000000000f, 0xff] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_0 : tB 0 7 ch_50 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 7 → ch_50 i = true := fun _ h1 h2 => tA nb_50_0 h1 h2
theorem lb_50 : LowerBin 0xff0000000000ff [0x55000000000055, 0x33000000000033, 0xf00000000000f, 0xff] g_50 5 :=
  lowerDagV5 (kn_nil) rc_50 nc_50 (by decide +kernel)
def m_51 := 0x5a005a005a005a00
def s_51 : List Nat := [0xa000a000a000a00, 0x1200120012001200, 0x5a0000005a00, 0x5a005a00]
def g_51 := 0x100012001a00
def ep_51 := 0x12000a0000001000000008000000000000000000000000000000000000001000120010000000000000000000
def bds_51 : BList := []
def cc_51_0 : Nat → LPN := uC 0xcc61 0x14a59080f 4 15 2 3 9 511 11 2047
def cur_51 : Nat → LPN := cc_51_0
def hc_51_0 (_ : Nat) := 0
def nh_51 : Nat → Nat := hc_51_0
def f_51 := uF 0x329c840f 1 9
def ch_51 := dN 0x5a005a005a005a00 g_51 ep_51 1 1 bds_51 3 (dT 0x5a005a005a005a00 [0xa000a000a000a00, 0x1200120012001200, 0x5a0000005a00, 0x5a005a00] 4 f_51) cur_51 nh_51
set_option maxHeartbeats 0 in
theorem rc_51 : dR 0x5a005a005a005a00 g_51 ep_51 1 1 3 bds_51 (dT 0x5a005a005a005a00 [0xa000a000a000a00, 0x1200120012001200, 0x5a0000005a00, 0x5a005a00] 4 f_51) (cur_51 0) (nh_51 0) [0xa000a000a000a00, 0x1200120012001200, 0x5a0000005a00, 0x5a005a00] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_0 : tB 0 3 ch_51 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 3 → ch_51 i = true := fun _ h1 h2 => tA nb_51_0 h1 h2
theorem lb_51 : LowerBin 0x5a005a005a005a00 [0xa000a000a000a00, 0x1200120012001200, 0x5a0000005a00, 0x5a005a00] g_51 5 :=
  lowerDagV5 (kn_nil) rc_51 nc_51 (by decide +kernel)
def m_52 := 0xaa005500aa005500
def s_52 : List Nat := [0x550000005500, 0x2200110022001100, 0xa0005000a000500, 0xaa005500]
def g_52 := 0x150002001500
def ep_52 := 0x200000000000000000000000000000000000000000004000200040000001000020010000000000000000000
def bds_52 : BList := []
def cc_52_0 : Nat → LPN := uC 0xb146850932244890e8701 0x54a1e7873029048fa064c2e511206842c00f 7 127 3 7 9 511 13 8191
def cur_52 : Nat → LPN := cc_52_0
def hc_52_0 (_ : Nat) := 0
def nh_52 : Nat → Nat := hc_52_0
def f_52 := uF 0x54a047c23279e08b844421a298148042c00f 4 9
def ch_52 := dN 0xaa005500aa005500 g_52 ep_52 1 1 bds_52 11 (dT 0xaa005500aa005500 [0x550000005500, 0x2200110022001100, 0xa0005000a000500, 0xaa005500] 4 f_52) cur_52 nh_52
set_option maxHeartbeats 0 in
theorem rc_52 : dR 0xaa005500aa005500 g_52 ep_52 1 1 11 bds_52 (dT 0xaa005500aa005500 [0x550000005500, 0x2200110022001100, 0xa0005000a000500, 0xaa005500] 4 f_52) (cur_52 0) (nh_52 0) [0x550000005500, 0x2200110022001100, 0xa0005000a000500, 0xaa005500] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_0 : tB 0 11 ch_52 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 11 → ch_52 i = true := fun _ h1 h2 => tA nb_52_0 h1 h2
theorem lb_52 : LowerBin 0xaa005500aa005500 [0x550000005500, 0x2200110022001100, 0xa0005000a000500, 0xaa005500] g_52 5 :=
  lowerDagV5 (kn_nil) rc_52 nc_52 (by decide +kernel)
def m_53 := 0x3c003c003c003c00
def s_53 : List Nat := [0x1400140014001400, 0xc000c000c000c00, 0x3c0000003c00, 0x3c003c00]
def g_53 := 0x140010001c00
def ep_53 := 0x100008000000140000000c000000000000000000000000000000000000000000000000000000140010001000
def bds_53 : BList := []
def cc_53_0 : Nat → LPN := uC 0xcc61 0xa9610f 4 15 2 3 6 63 8 255
def cur_53 : Nat → LPN := cc_53_0
def hc_53_0 (_ : Nat) := 0
def nh_53 : Nat → Nat := hc_53_0
def f_53 := uF 0x1a708f 1 6
def ch_53 := dN 0x3c003c003c003c00 g_53 ep_53 1 1 bds_53 3 (dT 0x3c003c003c003c00 [0x1400140014001400, 0xc000c000c000c00, 0x3c0000003c00, 0x3c003c00] 4 f_53) cur_53 nh_53
set_option maxHeartbeats 0 in
theorem rc_53 : dR 0x3c003c003c003c00 g_53 ep_53 1 1 3 bds_53 (dT 0x3c003c003c003c00 [0x1400140014001400, 0xc000c000c000c00, 0x3c0000003c00, 0x3c003c00] 4 f_53) (cur_53 0) (nh_53 0) [0x1400140014001400, 0xc000c000c000c00, 0x3c0000003c00, 0x3c003c00] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_0 : tB 0 3 ch_53 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 3 → ch_53 i = true := fun _ h1 h2 => tA nb_53_0 h1 h2
theorem lb_53 : LowerBin 0x3c003c003c003c00 [0x1400140014001400, 0xc000c000c000c00, 0x3c0000003c00, 0x3c003c00] g_53 5 :=
  lowerDagV5 (kn_nil) rc_53 nc_53 (by decide +kernel)
def m_54 := 0xcc00cc0033003300
def s_54 : List Nat := [0x4400440011001100, 0x33003300, 0xc000c0003000300, 0xcc0000003300]
def g_54 := 0x40013001300
def ep_54 := 0x400000000000000000000000000000004000200020000000000000000000000040010001000
def bds_54 : BList := []
def cc_54_0 : Nat → LPN := uC 0xb146850932244890e8701 0x54a1e787302904cfa264d2e591207442a00f 7 127 3 7 9 511 13 8191
def cur_54 : Nat → LPN := cc_54_0
def hc_54_0 (_ : Nat) := 0
def nh_54 : Nat → Nat := hc_54_0
def f_54 := uF 0x54a067c33279e0cb864421d298148042a00f 4 9
def ch_54 := dN 0xcc00cc0033003300 g_54 ep_54 1 1 bds_54 11 (dT 0xcc00cc0033003300 [0x4400440011001100, 0x33003300, 0xc000c0003000300, 0xcc0000003300] 4 f_54) cur_54 nh_54
set_option maxHeartbeats 0 in
theorem rc_54 : dR 0xcc00cc0033003300 g_54 ep_54 1 1 11 bds_54 (dT 0xcc00cc0033003300 [0x4400440011001100, 0x33003300, 0xc000c0003000300, 0xcc0000003300] 4 f_54) (cur_54 0) (nh_54 0) [0x4400440011001100, 0x33003300, 0xc000c0003000300, 0xcc0000003300] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_0 : tB 0 11 ch_54 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 11 → ch_54 i = true := fun _ h1 h2 => tA nb_54_0 h1 h2
theorem lb_54 : LowerBin 0xcc00cc0033003300 [0x4400440011001100, 0x33003300, 0xc000c0003000300, 0xcc0000003300] g_54 5 :=
  lowerDagV5 (kn_nil) rc_54 nc_54 (by decide +kernel)
def m_55 := 0xf0000f00f0000f00
def s_55 : List Nat := [0x5000050050000500, 0x3000030030000300, 0xf0000000f00, 0xf0000f00]
def g_55 := 0x50010000f00
def ep_55 := 0x10000a0000000000000000000000000000000000000000000000000000000000100000000000050010000000
def bds_55 : BList := []
def cc_55_0 : Nat → LPN := uC 0xb146850a14214072e0701 0x282868c142030f263e88c9d2d4494829108400f 7 127 3 7 10 1023 14 16383
def cur_55 : Nat → LPN := cc_55_0
def hc_55_0 (_ : Nat) := 0
def nh_55 : Nat → Nat := hc_55_0
def f_55 := uF 0x282818f863214b5630508052530f0429108400f 4 10
def ch_55 := dN 0xf0000f00f0000f00 g_55 ep_55 1 1 bds_55 11 (dT 0xf0000f00f0000f00 [0x5000050050000500, 0x3000030030000300, 0xf0000000f00, 0xf0000f00] 4 f_55) cur_55 nh_55
set_option maxHeartbeats 0 in
theorem rc_55 : dR 0xf0000f00f0000f00 g_55 ep_55 1 1 11 bds_55 (dT 0xf0000f00f0000f00 [0x5000050050000500, 0x3000030030000300, 0xf0000000f00, 0xf0000f00] 4 f_55) (cur_55 0) (nh_55 0) [0x5000050050000500, 0x3000030030000300, 0xf0000000f00, 0xf0000f00] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_0 : tB 0 11 ch_55 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 11 → ch_55 i = true := fun _ h1 h2 => tA nb_55_0 h1 h2
theorem lb_55 : LowerBin 0xf0000f00f0000f00 [0x5000050050000500, 0x3000030030000300, 0xf0000000f00, 0xf0000f00] g_55 5 :=
  lowerDagV5 (kn_nil) rc_55 nc_55 (by decide +kernel)
def m_56 := 0xf000f0000f000f00
def s_56 : List Nat := [0x5000500005000500, 0x3000300003000300, 0xf000f00, 0xf00000000f00]
def g_56 := 0x100003000f00
def ep_56 := 0x100000000c000000000000000000000000000000000000001000030000000000100000000000
def bds_56 : BList := []
def cc_56_0 : Nat → LPN := uC 0xb146850932244890e8701 0x292874f0e3024c263988c593954c503d10d400f 7 127 3 7 10 1023 14 16383
def cur_56 : Nat → LPN := cc_56_0
def hc_56_0 (_ : Nat) := 0
def nh_56 : Nat → Nat := hc_56_0
def f_56 := uF 0x292818e463174f053914c443d28c093010d400f 4 10
def ch_56 := dN 0xf000f0000f000f00 g_56 ep_56 1 1 bds_56 11 (dT 0xf000f0000f000f00 [0x5000500005000500, 0x3000300003000300, 0xf000f00, 0xf00000000f00] 4 f_56) cur_56 nh_56
set_option maxHeartbeats 0 in
theorem rc_56 : dR 0xf000f0000f000f00 g_56 ep_56 1 1 11 bds_56 (dT 0xf000f0000f000f00 [0x5000500005000500, 0x3000300003000300, 0xf000f00, 0xf00000000f00] 4 f_56) (cur_56 0) (nh_56 0) [0x5000500005000500, 0x3000300003000300, 0xf000f00, 0xf00000000f00] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_0 : tB 0 11 ch_56 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 11 → ch_56 i = true := fun _ h1 h2 => tA nb_56_0 h1 h2
theorem lb_56 : LowerBin 0xf000f0000f000f00 [0x5000500005000500, 0x3000300003000300, 0xf000f00, 0xf00000000f00] g_56 5 :=
  lowerDagV5 (kn_nil) rc_56 nc_56 (by decide +kernel)
def m_57 := 0xff00ff000000
def s_57 : List Nat := [0x550055000000, 0x330033000000, 0xf000f000000, 0xff000000]
def g_57 := 0x150013000000
def ep_57 := 0x4000200000000001000130000000000150010000000
def bds_57 : BList := []
def cc_57_0 : Nat → LPN := uC 0xcc61 0x17990f 4 15 2 3 5 31 7 127
def cur_57 : Nat → LPN := cc_57_0
def hc_57_0 (_ : Nat) := 0
def nh_57 : Nat → Nat := hc_57_0
def f_57 := uF 0x3ec8f 1 5
def ch_57 := dN 0xff00ff000000 g_57 ep_57 1 1 bds_57 3 (dT 0xff00ff000000 [0x550055000000, 0x330033000000, 0xf000f000000, 0xff000000] 4 f_57) cur_57 nh_57
set_option maxHeartbeats 0 in
theorem rc_57 : dR 0xff00ff000000 g_57 ep_57 1 1 3 bds_57 (dT 0xff00ff000000 [0x550055000000, 0x330033000000, 0xf000f000000, 0xff000000] 4 f_57) (cur_57 0) (nh_57 0) [0x550055000000, 0x330033000000, 0xf000f000000, 0xff000000] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_0 : tB 0 3 ch_57 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 3 → ch_57 i = true := fun _ h1 h2 => tA nb_57_0 h1 h2
theorem lb_57 : LowerBin 0xff00ff000000 [0x550055000000, 0x330033000000, 0xf000f000000, 0xff000000] g_57 5 :=
  lowerDagV5 (kn_nil) rc_57 nc_57 (by decide +kernel)
def m_58 := 0x666600006666
def s_58 : List Nat := [0x222200002222, 0x60600000606, 0x6600000066, 0x6666]
def g_58 := 0x42600000666
def ep_58 := 0x24000000000000000000000002200000060000004040000060000000000000000000000000000000000
def bds_58 : BList := []
def cc_58_0 : Nat → LPN := uC 0xcc61 0xbd750f 4 15 2 3 6 63 8 255
def cur_58 : Nat → LPN := cc_58_0
def hc_58_0 (_ : Nat) := 0
def nh_58 : Nat → Nat := hc_58_0
def f_58 := uF 0x1f7a8f 1 6
def ch_58 := dN 0x666600006666 g_58 ep_58 1 1 bds_58 3 (dT 0x666600006666 [0x222200002222, 0x60600000606, 0x6600000066, 0x6666] 4 f_58) cur_58 nh_58
set_option maxHeartbeats 0 in
theorem rc_58 : dR 0x666600006666 g_58 ep_58 1 1 3 bds_58 (dT 0x666600006666 [0x222200002222, 0x60600000606, 0x6600000066, 0x6666] 4 f_58) (cur_58 0) (nh_58 0) [0x222200002222, 0x60600000606, 0x6600000066, 0x6666] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_0 : tB 0 3 ch_58 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 3 → ch_58 i = true := fun _ h1 h2 => tA nb_58_0 h1 h2
theorem lb_58 : LowerBin 0x666600006666 [0x222200002222, 0x60600000606, 0x6600000066, 0x6666] g_58 5 :=
  lowerDagV5 (kn_nil) rc_58 nc_58 (by decide +kernel)
def m_59 := 0x5a5a00005a5a
def s_59 : List Nat := [0xa0a00000a0a, 0x121200001212, 0x5a0000005a, 0x5a5a]
def g_59 := 0x101200001a5a
def ep_59 := 0xa4800000000000000000000000200000040000000000000000000001012000010000000000000000000
def bds_59 : BList := []
def cc_59_0 : Nat → LPN := uC 0xcc61 0x14b59280f 4 15 2 3 9 511 11 2047
def cur_59 : Nat → LPN := cc_59_0
def hc_59_0 (_ : Nat) := 0
def nh_59 : Nat → Nat := hc_59_0
def f_59 := uF 0x32dc940f 1 9
def ch_59 := dN 0x5a5a00005a5a g_59 ep_59 1 1 bds_59 3 (dT 0x5a5a00005a5a [0xa0a00000a0a, 0x121200001212, 0x5a0000005a, 0x5a5a] 4 f_59) cur_59 nh_59
set_option maxHeartbeats 0 in
theorem rc_59 : dR 0x5a5a00005a5a g_59 ep_59 1 1 3 bds_59 (dT 0x5a5a00005a5a [0xa0a00000a0a, 0x121200001212, 0x5a0000005a, 0x5a5a] 4 f_59) (cur_59 0) (nh_59 0) [0xa0a00000a0a, 0x121200001212, 0x5a0000005a, 0x5a5a] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_0 : tB 0 3 ch_59 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 3 → ch_59 i = true := fun _ h1 h2 => tA nb_59_0 h1 h2
theorem lb_59 : LowerBin 0x5a5a00005a5a [0xa0a00000a0a, 0x121200001212, 0x5a0000005a, 0x5a5a] g_59 5 :=
  lowerDagV5 (kn_nil) rc_59 nc_59 (by decide +kernel)
def m_60 := 0xaa550000aa55
def s_60 : List Nat := [0x5500000055, 0x221100002211, 0xa0500000a05, 0xaa55]
def g_60 := 0x1500000a55
def ep_60 := 0xa40000000000000000000000000000000000000000400000a0000000010000000000000000000000000
def bds_60 : BList := []
def cc_60_0 : Nat → LPN := uC 0xb146850a14214072e0701 0x283464d141438d263d88d5d3944c483d10d400f 7 127 3 7 10 1023 14 16383
def cur_60 : Nat → LPN := cc_60_0
def hc_60_0 (_ : Nat) := 0
def nh_60 : Nat → Nat := hc_60_0
def f_60 := uF 0x283418f463514e5534505053138d043d10d400f 4 10
def ch_60 := dN 0xaa550000aa55 g_60 ep_60 1 1 bds_60 11 (dT 0xaa550000aa55 [0x5500000055, 0x221100002211, 0xa0500000a05, 0xaa55] 4 f_60) cur_60 nh_60
set_option maxHeartbeats 0 in
theorem rc_60 : dR 0xaa550000aa55 g_60 ep_60 1 1 11 bds_60 (dT 0xaa550000aa55 [0x5500000055, 0x221100002211, 0xa0500000a05, 0xaa55] 4 f_60) (cur_60 0) (nh_60 0) [0x5500000055, 0x221100002211, 0xa0500000a05, 0xaa55] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_0 : tB 0 11 ch_60 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 11 → ch_60 i = true := fun _ h1 h2 => tA nb_60_0 h1 h2
theorem lb_60 : LowerBin 0xaa550000aa55 [0x5500000055, 0x221100002211, 0xa0500000a05, 0xaa55] g_60 5 :=
  lowerDagV5 (kn_nil) rc_60 nc_60 (by decide +kernel)
def m_61 := 0xaaaa00005555
def s_61 : List Nat := [0x5555, 0x222200001111, 0xa0a00000505, 0xaa00000055]
def g_61 := 0x2200001555
def ep_61 := 0x2200000040000000000000040000000022000010000000000000000000
def bds_61 : BList := []
def cc_61_0 : Nat → LPN := uC 0xb146850932244890e8701 0x292478d0c34209263a88d992d5495029108400f 7 127 3 7 10 1023 14 16383
def cur_61 : Nat → LPN := cc_61_0
def hc_61_0 (_ : Nat) := 0
def nh_61 : Nat → Nat := hc_61_0
def f_61 := uF 0x292418e863678d052d149442920d0824108400f 4 10
def ch_61 := dN 0xaaaa00005555 g_61 ep_61 1 1 bds_61 11 (dT 0xaaaa00005555 [0x5555, 0x222200001111, 0xa0a00000505, 0xaa00000055] 4 f_61) cur_61 nh_61
set_option maxHeartbeats 0 in
theorem rc_61 : dR 0xaaaa00005555 g_61 ep_61 1 1 11 bds_61 (dT 0xaaaa00005555 [0x5555, 0x222200001111, 0xa0a00000505, 0xaa00000055] 4 f_61) (cur_61 0) (nh_61 0) [0x5555, 0x222200001111, 0xa0a00000505, 0xaa00000055] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_0 : tB 0 11 ch_61 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 11 → ch_61 i = true := fun _ h1 h2 => tA nb_61_0 h1 h2
theorem lb_61 : LowerBin 0xaaaa00005555 [0x5555, 0x222200001111, 0xa0a00000505, 0xaa00000055] g_61 5 :=
  lowerDagV5 (kn_nil) rc_61 nc_61 (by decide +kernel)
def m_62 := 0xcccc00003333
def s_62 : List Nat := [0x444400001111, 0x3333, 0xc0c00000303, 0xcc00000033]
def g_62 := 0x40400001333
def ep_62 := 0x20000004040000020000000000000000000000040400001000
def bds_62 : BList := []
def cc_62_0 : Nat → LPN := uC 0xb146850932244890e8701 0x5491e686342124cea26cd2a593206442200f 7 127 3 7 9 511 13 8191
def cur_62 : Nat → LPN := cc_62_0
def hc_62_0 (_ : Nat) := 0
def nh_62 : Nat → Nat := hc_62_0
def f_62 := uF 0x549067433679a0ca864c21921a109042200f 4 9
def ch_62 := dN 0xcccc00003333 g_62 ep_62 1 1 bds_62 11 (dT 0xcccc00003333 [0x444400001111, 0x3333, 0xc0c00000303, 0xcc00000033] 4 f_62) cur_62 nh_62
set_option maxHeartbeats 0 in
theorem rc_62 : dR 0xcccc00003333 g_62 ep_62 1 1 11 bds_62 (dT 0xcccc00003333 [0x444400001111, 0x3333, 0xc0c00000303, 0xcc00000033] 4 f_62) (cur_62 0) (nh_62 0) [0x444400001111, 0x3333, 0xc0c00000303, 0xcc00000033] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_0 : tB 0 11 ch_62 = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 11 → ch_62 i = true := fun _ h1 h2 => tA nb_62_0 h1 h2
theorem lb_62 : LowerBin 0xcccc00003333 [0x444400001111, 0x3333, 0xc0c00000303, 0xcc00000033] g_62 5 :=
  lowerDagV5 (kn_nil) rc_62 nc_62 (by decide +kernel)
def m_63 := 0xf00f0000f00f
def s_63 : List Nat := [0x500500005005, 0x300300003003, 0xf0000000f, 0xf00f]
def g_63 := 0x10070000100f
def ep_63 := 0x800000000000000000000000000000000000000000000000000001002000010000000100400001000
def bds_63 : BList := []
def cc_63_0 : Nat → LPN := uC 0xb146850932244890e8701 0x2a47d0f42927a8d9aa5991e1480f 7 127 3 7 6 63 10 1023
def cur_63 : Nat → LPN := cc_63_0
def hc_63_0 (_ : Nat) := 0
def nh_63 : Nat → Nat := hc_63_0
def f_63 := uF 0x2a41e8767d06a1985e2d0a41480f 4 6
def ch_63 := dN 0xf00f0000f00f g_63 ep_63 1 1 bds_63 11 (dT 0xf00f0000f00f [0x500500005005, 0x300300003003, 0xf0000000f, 0xf00f] 4 f_63) cur_63 nh_63
set_option maxHeartbeats 0 in
theorem rc_63 : dR 0xf00f0000f00f g_63 ep_63 1 1 11 bds_63 (dT 0xf00f0000f00f [0x500500005005, 0x300300003003, 0xf0000000f, 0xf00f] 4 f_63) (cur_63 0) (nh_63 0) [0x500500005005, 0x300300003003, 0xf0000000f, 0xf00f] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_0 : tB 0 11 ch_63 = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 11 → ch_63 i = true := fun _ h1 h2 => tA nb_63_0 h1 h2
theorem lb_63 : LowerBin 0xf00f0000f00f [0x500500005005, 0x300300003003, 0xf0000000f, 0xf00f] g_63 5 :=
  lowerDagV5 (kn_nil) rc_63 nc_63 (by decide +kernel)
def m_64 := 0xff0000ff00
def s_64 : List Nat := [0x5500005500, 0x3300003300, 0xf00000f00, 0xff00]
def g_64 := 0x3700001f00
def ep_64 := 0x400000e0000000032000010000000000400001000
def bds_64 : BList := []
def cc_64_0 : Nat → LPN := uC 0xcc61 0xba760f 4 15 2 3 6 63 8 255
def cur_64 : Nat → LPN := cc_64_0
def hc_64_0 (_ : Nat) := 0
def nh_64 : Nat → Nat := hc_64_0
def f_64 := uF 0x1ebb0f 1 6
def ch_64 := dN 0xff0000ff00 g_64 ep_64 1 1 bds_64 3 (dT 0xff0000ff00 [0x5500005500, 0x3300003300, 0xf00000f00, 0xff00] 4 f_64) cur_64 nh_64
set_option maxHeartbeats 0 in
theorem rc_64 : dR 0xff0000ff00 g_64 ep_64 1 1 3 bds_64 (dT 0xff0000ff00 [0x5500005500, 0x3300003300, 0xf00000f00, 0xff00] 4 f_64) (cur_64 0) (nh_64 0) [0x5500005500, 0x3300003300, 0xf00000f00, 0xff00] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_0 : tB 0 3 ch_64 = true := by decide +kernel
theorem nc_64 : ∀ i, 0 ≤ i → i < 3 → ch_64 i = true := fun _ h1 h2 => tA nb_64_0 h1 h2
theorem lb_64 : LowerBin 0xff0000ff00 [0x5500005500, 0x3300003300, 0xf00000f00, 0xff00] g_64 5 :=
  lowerDagV5 (kn_nil) rc_64 nc_64 (by decide +kernel)
def m_65 := 0x6666000066660000
def s_65 : List Nat := [0x2222000022220000, 0x606000006060000, 0x66000000660000, 0x66660000]
def g_65 := 0x4000002260000
def ep_65 := 0x222000000000000000000000004000000240000000400000204000000000000000000000000000000000000
def bds_65 : BList := []
def cc_65_0 : Nat → LPN := uC 0xcc61 0xbe720f 4 15 2 3 6 63 8 255
def cur_65 : Nat → LPN := cc_65_0
def hc_65_0 (_ : Nat) := 0
def nh_65 : Nat → Nat := hc_65_0
def f_65 := uF 0x1fb90f 1 6
def ch_65 := dN 0x6666000066660000 g_65 ep_65 1 1 bds_65 3 (dT 0x6666000066660000 [0x2222000022220000, 0x606000006060000, 0x66000000660000, 0x66660000] 4 f_65) cur_65 nh_65
set_option maxHeartbeats 0 in
theorem rc_65 : dR 0x6666000066660000 g_65 ep_65 1 1 3 bds_65 (dT 0x6666000066660000 [0x2222000022220000, 0x606000006060000, 0x66000000660000, 0x66660000] 4 f_65) (cur_65 0) (nh_65 0) [0x2222000022220000, 0x606000006060000, 0x66000000660000, 0x66660000] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_0 : tB 0 3 ch_65 = true := by decide +kernel
theorem nc_65 : ∀ i, 0 ≤ i → i < 3 → ch_65 i = true := fun _ h1 h2 => tA nb_65_0 h1 h2
theorem lb_65 : LowerBin 0x6666000066660000 [0x2222000022220000, 0x606000006060000, 0x66000000660000, 0x66660000] g_65 5 :=
  lowerDagV5 (kn_nil) rc_65 nc_65 (by decide +kernel)
def m_66 := 0xa5a50000a5a50000
def s_66 : List Nat := [0x505000005050000, 0x2121000021210000, 0xa5000000a50000, 0xa5a50000]
def g_66 := 0x105000001250000
def ep_66 := 0x20000000000000000000000004000000240000000000000000000001000000012000000000000000000000
def bds_66 : BList := []
def cc_66_0 : Nat → LPN := uC 0xb146850a14214072e0701 0x282868c142030f243e80c9c2a409881e104800f 7 127 3 7 10 1023 14 16383
def cur_66 : Nat → LPN := cc_66_0
def hc_66_0 (_ : Nat) := 0
def nh_66 : Nat → Nat := hc_66_0
def f_66 := uF 0x282810f843210a9630508042630f041e104800f 4 10
def ch_66 := dN 0xa5a50000a5a50000 g_66 ep_66 1 1 bds_66 11 (dT 0xa5a50000a5a50000 [0x505000005050000, 0x2121000021210000, 0xa5000000a50000, 0xa5a50000] 4 f_66) cur_66 nh_66
set_option maxHeartbeats 0 in
theorem rc_66 : dR 0xa5a50000a5a50000 g_66 ep_66 1 1 11 bds_66 (dT 0xa5a50000a5a50000 [0x505000005050000, 0x2121000021210000, 0xa5000000a50000, 0xa5a50000] 4 f_66) (cur_66 0) (nh_66 0) [0x505000005050000, 0x2121000021210000, 0xa5000000a50000, 0xa5a50000] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_0 : tB 0 11 ch_66 = true := by decide +kernel
theorem nc_66 : ∀ i, 0 ≤ i → i < 11 → ch_66 i = true := fun _ h1 h2 => tA nb_66_0 h1 h2
theorem lb_66 : LowerBin 0xa5a50000a5a50000 [0x505000005050000, 0x2121000021210000, 0xa5000000a50000, 0xa5a50000] g_66 5 :=
  lowerDagV5 (kn_nil) rc_66 nc_66 (by decide +kernel)
def m_67 := 0xaa550000aa550000
def s_67 : List Nat := [0x55000000550000, 0x2211000022110000, 0xa0500000a050000, 0xaa550000]
def g_67 := 0x15000002150000
def ep_67 := 0x200000000000000000000000000000000000000000400000204000000100000021000000000000000000000
def bds_67 : BList := []
def cc_67_0 : Nat → LPN := uC 0xb146850932244890e8701 0x54a1e7873029048fa064c2e511206842c00f 7 127 3 7 9 511 13 8191
def cur_67 : Nat → LPN := cc_67_0
def hc_67_0 (_ : Nat) := 0
def nh_67 : Nat → Nat := hc_67_0
def f_67 := uF 0x54a047c23279e08b844421a298148042c00f 4 9
def ch_67 := dN 0xaa550000aa550000 g_67 ep_67 1 1 bds_67 11 (dT 0xaa550000aa550000 [0x55000000550000, 0x2211000022110000, 0xa0500000a050000, 0xaa550000] 4 f_67) cur_67 nh_67
set_option maxHeartbeats 0 in
theorem rc_67 : dR 0xaa550000aa550000 g_67 ep_67 1 1 11 bds_67 (dT 0xaa550000aa550000 [0x55000000550000, 0x2211000022110000, 0xa0500000a050000, 0xaa550000] 4 f_67) (cur_67 0) (nh_67 0) [0x55000000550000, 0x2211000022110000, 0xa0500000a050000, 0xaa550000] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_0 : tB 0 11 ch_67 = true := by decide +kernel
theorem nc_67 : ∀ i, 0 ≤ i → i < 11 → ch_67 i = true := fun _ h1 h2 => tA nb_67_0 h1 h2
theorem lb_67 : LowerBin 0xaa550000aa550000 [0x55000000550000, 0x2211000022110000, 0xa0500000a050000, 0xaa550000] g_67 5 :=
  lowerDagV5 (kn_nil) rc_67 nc_67 (by decide +kernel)
def m_68 := 0xf00f0000f00f0000
def s_68 : List Nat := [0x5005000050050000, 0x3003000030030000, 0xf0000000f0000, 0xf00f0000]
def g_68 := 0x5000010070000
def ep_68 := 0x1002000000000000000000000000000000000000000000000000000000000000100200000005000010040000
def bds_68 : BList := []
def cc_68_0 : Nat → LPN := uC 0x72e18b060c0681 0xb2ca1cc2e82962242122000f 7 127 3 7 9 511 12 4095
def cur_68 : Nat → LPN := cc_68_0
def hc_68_0 (_ : Nat) := 0
def nh_68 : Nat → Nat := hc_68_0
def f_68 := uF 0x1bab86931184c00f 3 6
def ch_68 := dN 0xf00f0000f00f0000 g_68 ep_68 1 1 bds_68 7 (dT 0xf00f0000f00f0000 [0x5005000050050000, 0x3003000030030000, 0xf0000000f0000, 0xf00f0000] 4 f_68) cur_68 nh_68
set_option maxHeartbeats 0 in
theorem rc_68 : dR 0xf00f0000f00f0000 g_68 ep_68 1 1 7 bds_68 (dT 0xf00f0000f00f0000 [0x5005000050050000, 0x3003000030030000, 0xf0000000f0000, 0xf00f0000] 4 f_68) (cur_68 0) (nh_68 0) [0x5005000050050000, 0x3003000030030000, 0xf0000000f0000, 0xf00f0000] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_0 : tB 0 7 ch_68 = true := by decide +kernel
theorem nc_68 : ∀ i, 0 ≤ i → i < 7 → ch_68 i = true := fun _ h1 h2 => tA nb_68_0 h1 h2
theorem lb_68 : LowerBin 0xf00f0000f00f0000 [0x5005000050050000, 0x3003000030030000, 0xf0000000f0000, 0xf00f0000] g_68 5 :=
  lowerDagV5 (kn_nil) rc_68 nc_68 (by decide +kernel)
def m_69 := 0xa5a5a5a5
def s_69 : List Nat := [0x5050505, 0x21212121, 0xa500a5, 0xa5a5]
def g_69 := 0x1250525
def ep_69 := 0x4000000000000240020000000000000000000000000012000200000000000000000
def bds_69 : BList := []
def cc_69_0 : Nat → LPN := uC 0xb146850a14214072e0701 0x2946d1543d27a8d9ee4889a1580f 7 127 3 7 6 63 10 1023
def cur_69 : Nat → LPN := cc_69_0
def hc_69_0 (_ : Nat) := 0
def nh_69 : Nat → Nat := hc_69_0
def f_69 := uF 0x2941e8761b974550623d05a1580f 4 6
def ch_69 := dN 0xa5a5a5a5 g_69 ep_69 1 1 bds_69 11 (dT 0xa5a5a5a5 [0x5050505, 0x21212121, 0xa500a5, 0xa5a5] 4 f_69) cur_69 nh_69
set_option maxHeartbeats 0 in
theorem rc_69 : dR 0xa5a5a5a5 g_69 ep_69 1 1 11 bds_69 (dT 0xa5a5a5a5 [0x5050505, 0x21212121, 0xa500a5, 0xa5a5] 4 f_69) (cur_69 0) (nh_69 0) [0x5050505, 0x21212121, 0xa500a5, 0xa5a5] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_0 : tB 0 11 ch_69 = true := by decide +kernel
theorem nc_69 : ∀ i, 0 ≤ i → i < 11 → ch_69 i = true := fun _ h1 h2 => tA nb_69_0 h1 h2
theorem lb_69 : LowerBin 0xa5a5a5a5 [0x5050505, 0x21212121, 0xa500a5, 0xa5a5] g_69 5 :=
  lowerDagV5 (kn_nil) rc_69 nc_69 (by decide +kernel)
def m_70 := 0xaa55aa55
def s_70 : List Nat := [0x550055, 0x22112211, 0xa050a05, 0xaa55]
def g_70 := 0x2150a55
def ep_70 := 0x84000000000000000000000000002040a0000000000021000000000000000000000
def bds_70 : BList := []
def cc_70_0 : Nat → LPN := uC 0x72e18b060c0681 0xba5d37b3a7b2d4e80f 7 127 3 7 6 63 9 511
def cur_70 : Nat → LPN := cc_70_0
def hc_70_0 (_ : Nat) := 0
def nh_70 : Nat → Nat := hc_70_0
def f_70 := uF 0x1f6e87a3b1d4e80f 3 6
def ch_70 := dN 0xaa55aa55 g_70 ep_70 1 1 bds_70 7 (dT 0xaa55aa55 [0x550055, 0x22112211, 0xa050a05, 0xaa55] 4 f_70) cur_70 nh_70
set_option maxHeartbeats 0 in
theorem rc_70 : dR 0xaa55aa55 g_70 ep_70 1 1 7 bds_70 (dT 0xaa55aa55 [0x550055, 0x22112211, 0xa050a05, 0xaa55] 4 f_70) (cur_70 0) (nh_70 0) [0x550055, 0x22112211, 0xa050a05, 0xaa55] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_0 : tB 0 7 ch_70 = true := by decide +kernel
theorem nc_70 : ∀ i, 0 ≤ i → i < 7 → ch_70 i = true := fun _ h1 h2 => tA nb_70_0 h1 h2
theorem lb_70 : LowerBin 0xaa55aa55 [0x550055, 0x22112211, 0xa050a05, 0xaa55] g_70 5 :=
  lowerDagV5 (kn_nil) rc_70 nc_70 (by decide +kernel)
def m_71 := 0x3c3c3c3c
def s_71 : List Nat := [0x14141414, 0xc0c0c0c, 0x3c003c, 0x3c3c]
def g_71 := 0x10341c3c
def ep_71 := 0xc080000000000240020000000000000000000000000000000000000000010041000
def bds_71 : BList := []
def cc_71_0 : Nat → LPN := uC 0xcc61 0xae620f 4 15 2 3 6 63 8 255
def cur_71 : Nat → LPN := cc_71_0
def hc_71_0 (_ : Nat) := 0
def nh_71 : Nat → Nat := hc_71_0
def f_71 := uF 0x1bb10f 1 6
def ch_71 := dN 0x3c3c3c3c g_71 ep_71 1 1 bds_71 3 (dT 0x3c3c3c3c [0x14141414, 0xc0c0c0c, 0x3c003c, 0x3c3c] 4 f_71) cur_71 nh_71
set_option maxHeartbeats 0 in
theorem rc_71 : dR 0x3c3c3c3c g_71 ep_71 1 1 3 bds_71 (dT 0x3c3c3c3c [0x14141414, 0xc0c0c0c, 0x3c003c, 0x3c3c] 4 f_71) (cur_71 0) (nh_71 0) [0x14141414, 0xc0c0c0c, 0x3c003c, 0x3c3c] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_0 : tB 0 3 ch_71 = true := by decide +kernel
theorem nc_71 : ∀ i, 0 ≤ i → i < 3 → ch_71 i = true := fun _ h1 h2 => tA nb_71_0 h1 h2
theorem lb_71 : LowerBin 0x3c3c3c3c [0x14141414, 0xc0c0c0c, 0x3c003c, 0x3c3c] g_71 5 :=
  lowerDagV5 (kn_nil) rc_71 nc_71 (by decide +kernel)
def m_72 := 0xf00ff00f
def s_72 : List Nat := [0x50055005, 0x30033003, 0xf000f, 0xf00f]
def g_72 := 0x1007100f
def ep_72 := 0x80000000000000000000000000000000000000000100210000000000010041000
def bds_72 : BList := []
def cc_72_0 : Nat → LPN := uC 0xb146850932244890e8701 0x2a47d0f42927a8d9aa5991e1480f 7 127 3 7 6 63 10 1023
def cur_72 : Nat → LPN := cc_72_0
def hc_72_0 (_ : Nat) := 0
def nh_72 : Nat → Nat := hc_72_0
def f_72 := uF 0x2a41e8767d06a1985e2d0a41480f 4 6
def ch_72 := dN 0xf00ff00f g_72 ep_72 1 1 bds_72 11 (dT 0xf00ff00f [0x50055005, 0x30033003, 0xf000f, 0xf00f] 4 f_72) cur_72 nh_72
set_option maxHeartbeats 0 in
theorem rc_72 : dR 0xf00ff00f g_72 ep_72 1 1 11 bds_72 (dT 0xf00ff00f [0x50055005, 0x30033003, 0xf000f, 0xf00f] 4 f_72) (cur_72 0) (nh_72 0) [0x50055005, 0x30033003, 0xf000f, 0xf00f] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_72_0 : tB 0 11 ch_72 = true := by decide +kernel
theorem nc_72 : ∀ i, 0 ≤ i → i < 11 → ch_72 i = true := fun _ h1 h2 => tA nb_72_0 h1 h2
theorem lb_72 : LowerBin 0xf00ff00f [0x50055005, 0x30033003, 0xf000f, 0xf00f] g_72 5 :=
  lowerDagV5 (kn_nil) rc_72 nc_72 (by decide +kernel)
def m_73 := 0x6666666600000000
def s_73 : List Nat := [0x2222222200000000, 0x606060600000000, 0x66006600000000, 0x666600000000]
def g_73 := 0x4042600000000
def ep_73 := 0x422000000000004002200000000000404040000000000000000000000000000000000000000
def bds_73 : BList := []
def cc_73_0 : Nat → LPN := uC 0xcc61 0xa3a63600f 4 15 2 3 10 1023 12 4095
def cur_73 : Nat → LPN := cc_73_0
def hc_73_0 (_ : Nat) := 0
def nh_73 : Nat → Nat := hc_73_0
def f_73 := uF 0x18eb1b00f 1 10
def ch_73 := dN 0x6666666600000000 g_73 ep_73 1 1 bds_73 3 (dT 0x6666666600000000 [0x2222222200000000, 0x606060600000000, 0x66006600000000, 0x666600000000] 4 f_73) cur_73 nh_73
set_option maxHeartbeats 0 in
theorem rc_73 : dR 0x6666666600000000 g_73 ep_73 1 1 3 bds_73 (dT 0x6666666600000000 [0x2222222200000000, 0x606060600000000, 0x66006600000000, 0x666600000000] 4 f_73) (cur_73 0) (nh_73 0) [0x2222222200000000, 0x606060600000000, 0x66006600000000, 0x666600000000] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_73_0 : tB 0 3 ch_73 = true := by decide +kernel
theorem nc_73 : ∀ i, 0 ≤ i → i < 3 → ch_73 i = true := fun _ h1 h2 => tA nb_73_0 h1 h2
theorem lb_73 : LowerBin 0x6666666600000000 [0x2222222200000000, 0x606060600000000, 0x66006600000000, 0x666600000000] g_73 5 :=
  lowerDagV5 (kn_nil) rc_73 nc_73 (by decide +kernel)
def m_74 := 0xcc33cc3300000000
def s_74 : List Nat := [0x4411441100000000, 0x33003300000000, 0xc030c0300000000, 0xcc3300000000]
def g_74 := 0x11043300000000
def ep_74 := 0x422000000000000000000000000000004000000000000000000000000000011040000000000
def bds_74 : BList := []
def cc_74_0 : Nat → LPN := uC 0xb146850a14214072e0701 0x282868c142030f263e88c9d2d4494829108400f 7 127 3 7 10 1023 14 16383
def cur_74 : Nat → LPN := cc_74_0
def hc_74_0 (_ : Nat) := 0
def nh_74 : Nat → Nat := hc_74_0
def f_74 := uF 0x282818f863214b5630508052530f0429108400f 4 10
def ch_74 := dN 0xcc33cc3300000000 g_74 ep_74 1 1 bds_74 11 (dT 0xcc33cc3300000000 [0x4411441100000000, 0x33003300000000, 0xc030c0300000000, 0xcc3300000000] 4 f_74) cur_74 nh_74
set_option maxHeartbeats 0 in
theorem rc_74 : dR 0xcc33cc3300000000 g_74 ep_74 1 1 11 bds_74 (dT 0xcc33cc3300000000 [0x4411441100000000, 0x33003300000000, 0xc030c0300000000, 0xcc3300000000] 4 f_74) (cur_74 0) (nh_74 0) [0x4411441100000000, 0x33003300000000, 0xc030c0300000000, 0xcc3300000000] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_74_0 : tB 0 11 ch_74 = true := by decide +kernel
theorem nc_74 : ∀ i, 0 ≤ i → i < 11 → ch_74 i = true := fun _ h1 h2 => tA nb_74_0 h1 h2
theorem lb_74 : LowerBin 0xcc33cc3300000000 [0x4411441100000000, 0x33003300000000, 0xc030c0300000000, 0xcc3300000000] g_74 5 :=
  lowerDagV5 (kn_nil) rc_74 nc_74 (by decide +kernel)
def m_75 := 0xcccc333300000000
def s_75 : List Nat := [0x4444111100000000, 0x333300000000, 0xc0c030300000000, 0xcc003300000000]
def g_75 := 0x4113300000000
def ep_75 := 0x4002200000000000400000000000000000000000000000004110000000000
def bds_75 : BList := []
def cc_75_0 : Nat → LPN := uC 0xb146850932244890e8701 0x292874f0e30248263e88c9929548502d109400f 7 127 3 7 10 1023 14 16383
def cur_75 : Nat → LPN := cc_75_0
def hc_75_0 (_ : Nat) := 0
def nh_75 : Nat → Nat := hc_75_0
def f_75 := uF 0x292818f863274f0529148442d28c0920109400f 4 10
def ch_75 := dN 0xcccc333300000000 g_75 ep_75 1 1 bds_75 11 (dT 0xcccc333300000000 [0x4444111100000000, 0x333300000000, 0xc0c030300000000, 0xcc003300000000] 4 f_75) cur_75 nh_75
set_option maxHeartbeats 0 in
theorem rc_75 : dR 0xcccc333300000000 g_75 ep_75 1 1 11 bds_75 (dT 0xcccc333300000000 [0x4444111100000000, 0x333300000000, 0xc0c030300000000, 0xcc003300000000] 4 f_75) (cur_75 0) (nh_75 0) [0x4444111100000000, 0x333300000000, 0xc0c030300000000, 0xcc003300000000] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_0 : tB 0 11 ch_75 = true := by decide +kernel
theorem nc_75 : ∀ i, 0 ≤ i → i < 11 → ch_75 i = true := fun _ h1 h2 => tA nb_75_0 h1 h2
theorem lb_75 : LowerBin 0xcccc333300000000 [0x4444111100000000, 0x333300000000, 0xc0c030300000000, 0xcc003300000000] g_75 5 :=
  lowerDagV5 (kn_nil) rc_75 nc_75 (by decide +kernel)
def m_76 := 0xff0000ff00000000
def s_76 : List Nat := [0x5500005500000000, 0x3300003300000000, 0xf00000f00000000, 0xff00000000]
def g_76 := 0x100003700000000
def ep_76 := 0x10000040000000001000032000000000100000400000000
def bds_76 : BList := []
def cc_76_0 : Nat → LPN := uC 0x72e18b060c0681 0xb1e54b327d13969924c4a6000f 7 127 3 7 10 1023 13 8191
def cur_76 : Nat → LPN := cc_76_0
def hc_76_0 (_ : Nat) := 0
def nh_76 : Nat → Nat := hc_76_0
def f_76 := uF 0x33eb2c33933233133000f 3 9
def ch_76 := dN 0xff0000ff00000000 g_76 ep_76 1 1 bds_76 7 (dT 0xff0000ff00000000 [0x5500005500000000, 0x3300003300000000, 0xf00000f00000000, 0xff00000000] 4 f_76) cur_76 nh_76
set_option maxHeartbeats 0 in
theorem rc_76 : dR 0xff0000ff00000000 g_76 ep_76 1 1 7 bds_76 (dT 0xff0000ff00000000 [0x5500005500000000, 0x3300003300000000, 0xf00000f00000000, 0xff00000000] 4 f_76) (cur_76 0) (nh_76 0) [0x5500005500000000, 0x3300003300000000, 0xf00000f00000000, 0xff00000000] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_76_0 : tB 0 7 ch_76 = true := by decide +kernel
theorem nc_76 : ∀ i, 0 ≤ i → i < 7 → ch_76 i = true := fun _ h1 h2 => tA nb_76_0 h1 h2
theorem lb_76 : LowerBin 0xff0000ff00000000 [0x5500005500000000, 0x3300003300000000, 0xf00000f00000000, 0xff00000000] g_76 5 :=
  lowerDagV5 (kn_nil) rc_76 nc_76 (by decide +kernel)
def m_77 := 0x5555555555555555
def s_77 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_77 := 0x115151511151555
def ep_77 := 0x1000004000001400000004400014000000040040010404040004040001101010111010000000000000000000
def bds_77 : BList := [(m_12,s_12,6,g_12),(m_10,s_10,5,g_10),(m_14,s_14,5,g_14),(m_15,s_15,5,g_15),(m_42,s_42,6,g_42),(m_41,s_41,6,g_41),(m_43,s_43,6,g_43),(m_16,s_16,5,g_16),(m_39,s_39,5,g_39),(m_40,s_40,5,g_40),(m_17,s_17,5,g_17)]
def cc_77_0 : Nat → LPN := uC 0xb2691e71c7131c1 0x215d3495a5d249935a3958956791d547149c01f 6 63 2 3 10 1023 14 16383
def cur_77 : Nat → LPN := cc_77_0
def hc_77_0 : Nat → Nat := uH 0xc1f0000089710000820e7b0e3dfb007b0000 0x48022a25e06d185a7394ed2940ab640105a12a65e06f39d277a52095bccaf14ba40040611804211842105956528523414480264004612dce00052ac294ac6 16 65535 7 127
def nh_77 : Nat → Nat := hc_77_0
def f_77 := uF 0x215d191da5d151cb5a2958956149c01f 4 10
def ch_77 := dN 0x5555555555555555 g_77 ep_77 1 1 bds_77 9 (dT 0x5555555555555555 [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555] 7 f_77) cur_77 nh_77
set_option maxHeartbeats 0 in
theorem rc_77 : dR 0x5555555555555555 g_77 ep_77 1 1 9 bds_77 (dT 0x5555555555555555 [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555] 7 f_77) (cur_77 0) (nh_77 0) [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555] 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_77_0 : tB 0 9 ch_77 = true := by decide +kernel
theorem nc_77 : ∀ i, 0 ≤ i → i < 9 → ch_77 i = true := fun _ h1 h2 => tA nb_77_0 h1 h2
theorem lb_77 : LowerBin 0x5555555555555555 [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555] g_77 8 :=
  lowerDagV5 (kn_cons lb_12 (kn_cons lb_10 (kn_cons lb_14 (kn_cons lb_15 (kn_cons lb_42 (kn_cons lb_41 (kn_cons lb_43 (kn_cons lb_16 (kn_cons lb_39 (kn_cons lb_40 (kn_cons lb_17 (kn_nil)))))))))))) rc_77 nc_77 (by decide +kernel)
def m_78 := 0x3333333333333333
def s_78 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_78 := 0x111113313331333
def ep_78 := 0x1222020000001022000000000010002200200020010000000200020000000000000000000111110010001000
def bds_78 : BList := [(m_18,s_18,5,g_18),(m_20,s_20,5,g_20),(m_22,s_22,5,g_22),(m_24,s_24,5,g_24),(m_44,s_44,6,g_44)]
def cc_78_0 : Nat → LPN := uC 0x9 0x1f 2 3 1 1 5 31 6 63
def cur_78 : Nat → LPN := cc_78_0
def hc_78_0 : Nat → Nat := uH 0x850000 0x154010421094a52954c6318015442108c2 16 65535 8 255
def nh_78 : Nat → Nat := hc_78_0
def f_78 := uF 0x1f 1 5
def ch_78 := dN 0x3333333333333333 g_78 ep_78 1 1 bds_78 1 (dT 0x3333333333333333 [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333] 6 f_78) cur_78 nh_78
set_option maxHeartbeats 0 in
theorem rc_78 : dR 0x3333333333333333 g_78 ep_78 1 1 1 bds_78 (dT 0x3333333333333333 [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333] 6 f_78) (cur_78 0) (nh_78 0) [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333] 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_0 : tB 0 1 ch_78 = true := by decide +kernel
theorem nc_78 : ∀ i, 0 ≤ i → i < 1 → ch_78 i = true := fun _ h1 h2 => tA nb_78_0 h1 h2
theorem lb_78 : LowerBin 0x3333333333333333 [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333] g_78 7 :=
  lowerDagV5 (kn_cons lb_18 (kn_cons lb_20 (kn_cons lb_22 (kn_cons lb_24 (kn_cons lb_44 (kn_nil)))))) rc_78 nc_78 (by decide +kernel)
def m_79 := 0xcccccccccccccccc
def s_79 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_79 := 0x4040400040c4c
def ep_79 := 0x8480000040000000c4800040000000400400004040400040c0800000000000000000004040400040040
def bds_79 : BList := [(m_10,s_10,5,g_10),(m_21,s_21,5,g_21),(m_19,s_19,5,g_19),(m_45,s_45,6,g_45),(m_23,s_23,5,g_23)]
def cc_79_0 : Nat → LPN := uC 0x9 0x1f 2 3 1 1 5 31 6 63
def cur_79 : Nat → LPN := cc_79_0
def hc_79_0 : Nat → Nat := uH 0x1c4000 0x10842005510842005294a318c6555 14 16383 7 127
def nh_79 : Nat → Nat := hc_79_0
def f_79 := uF 0x1f 1 5
def ch_79 := dN 0xcccccccccccccccc g_79 ep_79 1 1 bds_79 1 (dT 0xcccccccccccccccc [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc] 6 f_79) cur_79 nh_79
set_option maxHeartbeats 0 in
theorem rc_79 : dR 0xcccccccccccccccc g_79 ep_79 1 1 1 bds_79 (dT 0xcccccccccccccccc [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc] 6 f_79) (cur_79 0) (nh_79 0) [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc] 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_79_0 : tB 0 1 ch_79 = true := by decide +kernel
theorem nc_79 : ∀ i, 0 ≤ i → i < 1 → ch_79 i = true := fun _ h1 h2 => tA nb_79_0 h1 h2
theorem lb_79 : LowerBin 0xcccccccccccccccc [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc] g_79 7 :=
  lowerDagV5 (kn_cons lb_10 (kn_cons lb_21 (kn_cons lb_19 (kn_cons lb_45 (kn_cons lb_23 (kn_nil)))))) rc_79 nc_79 (by decide +kernel)
def m_80 := 0xf0f0f0f0f0f0f0f
def s_80 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_80 := 0x105050703070f0f
def ep_80 := 0x2020a080000040200000c080004000200040000000000000000000001000002030200000105050400040000
def bds_80 : BList := [(m_30,s_30,6,g_30)]
def cc_80_0 : Nat → LPN := fun _ => []
def cur_80 : Nat → LPN := cc_80_0
def hc_80_0 (_ : Nat) := 0
def nh_80 : Nat → Nat := hc_80_0
def f_80 (_ : Nat) := (0,0)
def ch_80 := dN 0xf0f0f0f0f0f0f0f g_80 ep_80 1 1 bds_80 0 (dT 0xf0f0f0f0f0f0f0f [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f] 6 f_80) cur_80 nh_80
set_option maxHeartbeats 0 in
theorem rc_80 : dR 0xf0f0f0f0f0f0f0f g_80 ep_80 1 1 0 bds_80 (dT 0xf0f0f0f0f0f0f0f [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f] 6 f_80) (cur_80 0) (nh_80 0) [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f] 6 = true := by decide +kernel
def nc_80 := nc0 ch_80
theorem lb_80 : LowerBin 0xf0f0f0f0f0f0f0f [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f] g_80 7 :=
  lowerDagV5 (kn_cons lb_30 (kn_nil)) rc_80 nc_80 (by decide +kernel)
def m_81 := 0xff00ff00ff00ff
def s_81 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_81 := 0x1500370037007f
def ep_81 := 0x22004800000022000000480000000000000000000400040004000800100032003200200015000400040040
def bds_81 : BList := [(m_13,s_13,5,g_13),(m_19,s_19,5,g_19),(m_25,s_25,5,g_25),(m_32,s_32,5,g_32),(m_26,s_26,6,g_26),(m_34,s_34,5,g_34),(m_6,s_6,4,g_6),(m_1,s_1,4,g_1),(m_8,s_8,4,g_8),(m_48,s_48,5,g_48),(m_47,s_47,5,g_47),(m_49,s_49,5,g_49),(m_50,s_50,5,g_50)]
def cc_81_0 : Nat → LPN := uC 0xe507901e403900e30760bd7075c0d607580d60330acc03204c803143c4070c1c303081c203080c203080b82ae00b802e00b412d00b10ec01b002bc1af02bc0ae06b02aa0a849a102840a1028019b166c09a0664199026409512540940650094024c193024c08d1a3018c023008c02300890e105840210083060c083020818202080820204181020407f09fc07f01d0b7401c046e09b806a11a416901a0166099416501901620988062017065b056c05b016c057115c055095015401500540150054015004f153c04e053804d0518746011414501140420d08041048de0188001 0x10068078341ec2a0fed58764b43f2421acad0fa5084a0b4180561f0270f41081706a070341349401a0d0776943b3461a8ad0ca558752543a1261582e8841541b094060461c22e8d25286428c3905d1c11e03c4a02f0c8029281389e0160d06c69435b461a92d0d29586825a339251542e8821541a094050461862e8ca5286428c3185d07c9e0c24b02e0c80313c178a40b60d05c0b82d0501502687e1145d49e2ca47160a50a613c500961f0470ac2180e0ac0304e2a158159340aa5a053248278681242a0a20b0290a82823413cb609c0f04d058240341211a096d284a68c2485611c2308c0b84503c201241012e07e5202a08021b6c1092c0825603e248140500c51a0708d0344b8193500c522078d743b69a1d3450e52f06e9483649a1aa450cd1d0608d82f282170410a8aa04e110230681602c0981a0440902a2481485c094220420d0260881301409c9204a150220881101408c920421502b468141640902a0401101f0780f02c04caa0369681a2b40c85604c2282ed101309008a440452501a528102640584a03c1901a8d00b4680ac5a051ab026d381246a07234030ad0141680805803a340181e00a0b0032484ac5f2422b916d7c876ae4334a205a38f2d18784b639a5a1c52b0de94c6e4763695b198ad0c4558602a62f93b15c920a417c4c0b62205a0f42b85a1581d0a60e04b0602502c11c0908c0203b0081bc2ad3e1269705b47815a1bf693ded48ef623f7a11d3c68ddd946cea94f720a5b8a51dbd286da93f6ac9db104dd73266b712b5b093ad013d50096a40474dc21a5e0fd1c076748373501998e0acc504e5a01f2880d93405c010260001f 14 16383 6 63 11 2047 21 2097151
def cc_81_1 : Nat → LPN := uC 0xb82b80b71b70b61b60b24b11b10a89a71a70a70a61a33a30a30a30a12a109e394a9409048f18f08a58a08a08a08828808808628608608608428408408318127987727617607337307127107107017007006a66466406316306306126106105f25f05d25d05a35a05915905725705524d84d04d04b24b04b04924904724704524504234204114103f23c33483313123103012f12b42a12642602602602602152102102012001971901901901901361211110f20b4074070070070070025020002 0x7e9347d9247e9447d9447f2547e1447d1347c8187901882a4f822478194f8094b7f9477c1437b92b7b1277604a79028791407a2507995c788187714d7694577941761407584d8d45a8ba5f8aa578915b871538594c839417a9407812b7505a71064740546d82c6c0246b824731607286c708546d02c6b0247124d70a456fa4f6f2476da4f6d2476b8506c24f6b24773b5f723577185c700566e8546e0346c82c6a8246683c6502c6612c691506885c6582c65149679416604066a4a65a466514a64946538290302169a4b682475312b2f923670466402e63131621546185860a606016c3823c5f0185c264231245e0185d018231515c1413092e5b0156135f5fb575ea5b5da535ca3b5b9565192e5a85a59a5859054581605786c568263801e3092c5583c529645483c228145383c22851528413825a3095a2485658b5f573575625a5515b541535313b520565181e2f02050a582e8102d0102d0104fa604f1604e8602c8102c0205035f4e3574da5a2b8104ca584c1581d8644b8584b054402343fb444a260499604906c488601d0540a04447a58471582e9241b06446858460542e0142d8142d124448442c9244506c440601a8543ba5a3615a2585a1985642a50421504185c41050090444005c18844 12 4095 4 15 11 2047 20 1048575
def cc_81_2 : Nat → LPN := uC 0xbe05f02f05780bc05e02e85740ba05c86dc55e8af0568ab414e6a135082803400a0050027473a09a1cb8e583282911c8064011a38c0c602285121890448224112089044062011007f4be89a68d206713381944ca065030916ccb415812b855c0a645302981406a0050028013c29e04f023a11447a83d01e80f027803c01d08e806c43601b00d046803309980cc06033001800b845c02e01608b005422a0148485042020090007c23641b00c0c6002e11418a005002610f207803c01a20c085842c00c5060028414008104001840c0003 0xbf24fbea47bd24fbca47bb150bba4fbaa47c335fc1b57c115cbf956be154bd934bc018ba01491049b90419194a789465d12e029229104ab8046b89469084b780475c82f37023b7819b6831b5949b5148b494436122ad02e2582235922ac82e250223513034920ac02c0d120ab83caa02cab12cb0950b005caa82c90148aa149ae94134130ab040ad34aacb46ac256aba4aaaa46aa14aa99465582927021339202303cb3c57b334ab2b46b225bb1a57b124bafa478f94a751465a92e5512b36923331228e84aaf047ae046ad82fa902ea882722022a5a562495632820a681824d60a5950a5060320109c45da7a5ca7151a614ba4947310129f82e9f03c9d82c9e92ca2950a205ca08449e02c9d949a1141a09359e8409fb4a9f24a9e2469d94a9d146548290f82122819309222302ea3b4aa324ba1a475412b30123a00469c82e9c01e9ab5499b6c990609b3569a25f98a5798234971589685895860949280d83094028931289282891928910280d122900458f02e9635f9535793a5b9225390a3b8f95a8e85a0c0228d939831408cc588694c829408c0588b4608614c8214081140852508a15c898187c94084a508895c88144878188694f86147810287c8288525a84a527a23a841567785a8304877058810188025c7f14076848 13 8191 5 31 11 2047 20 1048575
def cc_81_3 : Nat → LPN := uC 0x81820607da1d8f7601d617581d417311cc07285ca06ea1ba06e05b806a218af620588062018805e217805c8d7205b0d66359816605981660580d600568d5a0550d448510144051013e34f813834c8d3014c012c24a852a04a812a046251423b50ec03a08dc63684da0350cd023400d003020b082c00b002b84ae02b80aa22a80a242880a2027889e027049c026089802584868218084121008211e907a01d0c7401b8c6e01b806a21a806a0181460017845e016885a016045611580560140c4c213004a1128048110103e10f802c9062818004100e1038004501000400100002 0x25c5291828c6192e2389125a129fe08cfe82e23411404d15ff292dd13f6c89db4c4dd86266fe0494d01fa580ed1706e738333080f96206ca002e458137e80c3f00b1f9292d89417dc24a56105f5080dc24e61521362529f428c6082d27812be606488022f89404c8a71cc508b02544e9264ac253e0119ef05c440227d9aebe4545b727ed813b6909bb064cdee0a29883f4a81da2a0dce40665f81f2b80d93805c87026f4a347ada7bd4d1de946ce994b710a1acc12d470864301321410bce064820224212279417104089e6282f204120409bc050ddf0863f8131f810bba0647a0223e92276c170f4089e2494f0a47779233a452ddc266b284b768198f204dd8092eb848758220ee085cd032258111d810b980644a022d7a484a024ba010475260e6b4a731a329a55929294899462f89709a48928094e5846114960e80c1d48aee9b4a749a335c929a248cd614a744a3b9e519640b6a605749c25a2411cbd05e560291e0118e6085ce036e50197240b8880454a2ac248567062eb8e971c60a2b184b524238e2045c00329284970c20a200d47004222819701a524c5290f28c5e12e0789124a129bf08c2302e711a5384519c125c9204b438239760bc6f046df0196edaa372db1b82c0de3566e92fb6e95db6468da2586ccac362581af28a0d8216b40cb64d7db06aed725a6b0ad2c416d460a66983b06008b540e59b080d445869cac3421319a080d2c6068026332101a329acf0416602034253da028ecf25a584ad28a548d2274ce85666ca432e1359308acb9585581632897193290c88406401a31c09190088c7044644aa31e1118d0689e82c3301633493d9948ecc14a65827b2a12d9208ec604362c15b1409da98b4d325f6912bb445695f0b6a185367c26338105890806802b604b230e5517a030bb8145d80a30a981842d8c01545e40c2ea0518149ac0245 14 16383 5 31 11 2047 21 2097151
def cc_81_4 : Nat → LPN := uC 0x330c0f00b4e85a028094e41902138060074d1c4411044110440c5300c02108020008 0x264218641925c112612285c2e25c22853457ae3a8614985849254138535678a4484e347834425021840192441177f4424d228342e244227aa3a7863677a346b1598455383d517514b47459838538305159c4b2401382a34825388213481c38818346cd59811514b45980c516d24a69e466cd4a805462cc2923c218001923411 10 1023 4 15 10 1023 20 1048575
def cur_81 : Nat → LPN := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_81_4 (Nat.sub p 512)) (cc_81_3 (Nat.sub p 384)) (Nat.blt p 512)) (cc_81_2 (Nat.sub p 256)) (Nat.blt p 384)) (cc_81_1 (Nat.sub p 128)) (Nat.blt p 256)) (cc_81_0 p) (Nat.blt p 128)
def hc_81_0 : Nat → Nat := uH 0x9d9074e60367180c000009c0034a29ee4605b21c0a904054800100000115e518a803c1c9be0bc150221e7e5163dc8b1ec012f4e0979c05bc9825e40060000073d29b9a025cbc0ae50076b838357825a443ccca2c0000032c03400000000006540232602188854acebb0000000000000000aac115410aa9c8214c410a5a045230528c8294480e0000051100a8501c00000000000000000000137c56000004db0226b81134c08000004c208a5187d2700e0000048e0724501000000910024840223e020000008f00446f04a3581118c108be0445b02203154ff8107e00e3e8041f2010000007c00400000000000000007b80400000000000000007a6093ca049dd83ce6c407220a388049c081cc5cd460c112d916800000af83655e0f2950d000000a440851c03247239218108c42445c0321d088b8ab05a4102c208157050a68284fc1c26e0812907013c080004e00000 0x7085842a6a9295292eb4ae319d2010993292e718de6319c79c1eef3bcec65949ce71e084e070636fcb2918d2938c631a52304a42118dde799c1e71e6728425285ee738c3983dbcde6f0de6d69ce5318c782139c6031bcc6fe5d69ced68ce718dad3835a109cede7b8c1e31ee328425285e6ffff948c6594aee529494a92a52928c6318c64c632a3195294a529294635fd9bff8c671fffffbc6f1e32bc9aa1095ef7ffd59be9c6338f4aff9eaaafaf57c9fffbc9a21284a50e1de0c19fffe4afffffde6f24af4a4e36a4f79bc95294974ae319d20c9284254b5294971aed26949938dff2fd4a47fd2bffe5db52a5275ad32718ce9779bddbbfcd929094254a5292b9d39cc997e94cc8c674cbdc633a5ffff8461142557d095292952528c636a4696946539ce969d2929ca738c6319c1264a9421294e738c635294a5294a 21 2097151 9 511
def hc_81_1 : Nat → Nat := uH 0xb6a010000000000000000000000000000b66022d8c06b61012c42a1b0983ac1e0400000000000af807ebbc1200000000000ade886b7204ab812685b43a1301e8181a9fd8467ec059ea08a6da679b48126b60e96822e5980495f8364429e8c326e304048bf0121da918748121ca0486e02607a9f79dc09e3e1c789831e1e04777085dd603731a21cba0600000000000000001cb4036f39cd905655fca2550b74000000000005328814be0652d81147e1c51d8114322250a8113fc174fd01139e2b4e5811292824a28111ee4e3c959400000000000ee4203b4824eca043a4870e8c0337c138de804369884d9e0435b860d66043440acd0804302200b088020fd940000020405c00000000000000001f58746bc8d0f75c03c80a0ed824000000ea01c362230ce850314130000002fa0d0aa0a42940a0a08240000009f8082421e0000000000008c8201fe1a03e20c0d41202c8440b00102603002a3700000000015 0xfa9f7f4e952956b5a5d69529ce739cae72a9ce52eb739dea756f1385eef31af5a7394d7fda10b5a739ce7394c6e1ce738d3a5ced294e1294e1294ab5ad32939c6739c67399495494e739ce555ce577a9ce539d2739df7fc1142f7f17fdde89142aaa00aaab59400aaab394e93a5ff73d11551284a5294de34a52948334e7769652ff73d5529556529495552929ceed2aaab4e53a5274a55442109556d6b595442109d67595442109d274bfeaa94aab294a4aaa9494ed3b4aaad394e93a5ffeeaaa52aa98c632aa8c653b4ed2aaab4e518c6318d554a55594a525554a4a769da55577ab4e53a5274a48aaa2aa952a25592a99574ff985216f557bbc4611ad8c1084a12944244a1084635aca956b4a17ba52856b0847ac2884210856b294655ad6b0842109421284215ad6b6b421084eb59d6b3b4ed084af1084273840842b0812210848842108423084250a856b6b4211eb0eb4884210856739ca32956b5ac205610840916842122108421284210842b5ad6d6b5a11842108421084e759ce739ce7084a108421095ee739de38509df7ff984277ff9e3c3bddf8707bbfd4250942f77f3b49bad09425295ad1e3dad1830e739ddad6b40ed084e7394c676a5a9295256b5a518c6968da928ca70e739c39739da72a5384e1294e739ce739ce739d2539ca319de6339c631bcde1850bc5feef108da523196527380d2108c6fff1cc7837f786307ffa84650942fc6926ca425094a54a460c18c787948c6948c6939d2718c631e19495084a338c694a5252a4a94a4a318c6318c631a4a3194e73a5274a4a728c67798c6318318c60c98c6919528c23094a318c6378604af3084674a46348c6327254212831873a4e318ce70e2529494a92a52928c18c63064d2318ca9461184a518c6318d2318ca31946319ce739ce939ce539ca319c6318c633bbcde4af91b4e90177bdd33f9a285e693b52331ef379799c009549e210a14952552b4aa538c674819495294a738c6ef10b7885f29af33a4212a10952d48c 22 4194303 9 511
def hc_81_2 : Nat → Nat := uH 0xdd581373a0ed7f27f4c69bd2f8134b604ce524738c04ce101337209c8d27f03102c0a80ef1a88bc500ee3072ad9d96a56889dbdd264694946a5a3dc9f87cbd61962e82e1bdfb2837d50bdeec347a9091e92097a300de4225783869e0c01753181d1a1900000000000742821cfe0600000000000000001cf803717935c361468d4058d0b26011997f4085e28d5782045de81171a305115ad3b8464e3059366134d800d3261d4bf8512e60c48a17c00000487018000004850100000048380d17a4a4281b4f16c53901ace3e01385054e1201383808dd01f327a64aaafa2a7818000002978800000028c05ca24060000009da25273818000002688589960600000095e1c25382088e600000007ec5115e4e8000001299a40000000000046c1d1190104381610c80c000000f98983e0030f20303c0040e187437e040dd81021cad08182c1de1406f04405cb000000004a090108100280d00000001c060000000000e 0x7f9bd554a555378d2555548cad6b5a5556b4a91a4696aa884212aa9ac6b2a884215ad6b2a8842148c697fd5529554d2349555232b5ad69555ad2a4634bffcd554a555348d2555548ca739ce55539ca719c673aaa94aaa691a4aaa6f548ca45551554a9512ac9d6b5a5556b4a91a46969574ae5b630421284a51091284215aca954a4a139da52856b5ac210f614421094a32842b5ad610842128425084235ac6b58d234842578842108108561024421091084250ad6b5a521084231842109c2150ac6b5a52108c61ec32922108465294215ad6b0815842102452108488421084a10842108c6b18c6318c6109421084212bed6b5a529484e1084210842118c636ac01ad6b4ab59400eb4a84250039ce738ce3595ab59401ad6b4ab594000e739ca7394e739d8c630048328ca00b2a56b28c631801ce7394e72b4009a000014082cad5aca00000306b5ad2ad6503bc001ce739ca7394e739df673fa6e5c9d943bdc6b4a569ce75a54a528c60b5ad652877b810b5ad39d610aceb498c1feeef19c637acaf73fb8c6f1bff4e33c8f79bfdda319cde39c9bf9c68ccc4a12b5a319ce44d6bdc3f8d5feef29439c2a84257bc60c7b833e81562cab2835a55aca077b9c0ed3b4ab59d6539ce73b4bbaa538ac2529cc6702105ac084216845ac084216b5ad0e700842739ce739ced6bdad1e1d695084a739ce0c1abeca37bcce37bddffc63595651871ce769cb9ce4d6b5a1ce1294e129ca50ab1656ada538ce738ce0d6b5a55aca001ce077b9da739ca759ce539ce73aca01de09a14280c68ff3123e6736ff706137a284fffca12adab5ac6368077a6eb5af3f582d60055084a0031bdab07b8d3ace70e4f4a842518de0b2ad65006b4ab594000ef769da559ca73801000500200030051151284a5378d2949c387395d2cf50bf44fa84ef84212aaaadad6b084212ab9ce7084212ab9ce75545515529555554a512ca5292aab24caa9494e739caef555729ce539ce73a5e7bbcd0257fe842f7fe4e37b47e7fb8d1effb85a177eb46bf439c2169ce75e98c286b4e768f46a1094631e8f4e952956b5a65265255253b4ed695dee72ab4e53a5274b5a35ad68739ca5685a1295ad48d23695d1b9c1e852b5a1284a31bce72271e253bff842ffde673bdf276fffff30e1f77fc9926318c98ca94aa529265194e739cb9ca63194e72bc77fce74a77a52949949549478652542129ce72b8ceb339ce4c6729bddff6ef68ce 22 4194303 9 511
def hc_81_3 : Nat → Nat := uH 0x20f122c080b100000101d018000004068067f50c0000001fc905bf80097dbca2000001f63063eb4097c28a0f05401d117cb97c537120ecdd5a75b23440000006a5d18000001a0c45b1158260110cbb9a4576805aeba0b5a917200000161e4300000056610ca842414744a27bc964d15329283d522117a3646f44bd0688a06d11300a1685f42683400000000000212e0341309681b854f31831cfeb23868ca6585a8c6a2318ac142fdcbe5c51b400000170e032cf49453c314a0e35141a0127e02a4fb8049f50113ac1f24f532421be883d030000002074400000008060b8ffe071e7cc000000074e288c293a0000002d61a0000000000001640382c60105770a8ae60414ac902938105230208eeac11982222b0403a7578000000e78121cd010379108000000db01a1b3018000000000000d601c1aa0100000000000000000000000034c04068c060d0808150a8415fa102b00704f83409604812702820a220278ce04d01008b0780008b 0x2840210028842118c10005e0002109421080000c021084250000380421084aba6a51631080114a250842319cebdde2a17ac210a50a201084e7617f8a84f610852851008c610a12842442125ac0002100bc42508421184210845ac0842109c2108422d604210aad9456c8a8842128bd55456b5acaaac932884215ad6b2aaba5ca21085294a5f01142942a2448c1a34e2808fa94214a556348d2949da76b5a84212ad944dad6b084212adad6b084212aca52955294a52a5265254a52b5a75a54a52b5294a50ad69494210bcf5854a44a512210a4e74a50ad6d694210bf43d854a44a5122318428158421166d6b221284212842129551284a517dad6b08c21084265244a1084212ad6b584e1084213ad22508421095a94ac21b2d92d62c215954b58b08565594a52a284ab580547d49a4695a4ca4bb4ed5b4eb4f21f43514a15945ac22d2332d6b48b0856d1996b5b45842b6a52ad6b0956b184217ca45ac08ca94885273ab5ac255ace1085fad68b5813952931842ac2b5954a55a569084ca4db56d084eb4ea529580025294956b28c6318019495084a318c60b2a56b28000c631946328025294956b28c631a439ce700394e55952b594006318c6318ca31952004900000a041654ad6501bc000c6318ca319400000e094a5255aca318c6fb1bde9993276506f3129294633292a52941273ad6b594a0de6042948c6b0856652424e7786327ee3123331284a948c644949ceff78c3b752831855084a0c63def30ef481562cab280de6301a4692ad63594631a4fbca95e1584a5001292ad6518de73bd082d604210a420c6010846318c5ac084214a52918c634a4f2918c78652542128c0631b18d23263192529483184a5184a32942ac5952b4940018c06f31a4631946b18ca338c6318c1294a4ab5946318c6b28037824850a240e3d14265095695ad600de9b2949ce94ac1e6246b1832725421280ce77b5802d60055084a31bc1655aca000379a4692ac65002000a0040001292ad6518c00e0a22a25094a60c18cae776b5a36b3d42fd13ea11be1084aaaaa6318c21084ab6b5ac21084aa6318d55154554a5555552944a6318ca6f555328c656b5ad2aaba5caad6946318c6d79e6f24095ff210b7ca44be418c2118ccbd1424e74a46348e46a109523738e4c952954a524d234a4a6f31955232a44a529063194a90a425295d6994956952d18d2949d2949d29198c1c852a521284a31911ce7c78946ffc217ffe90852918c65318ce77ff39ce9325cb9529ca72954a524c6319318c98ca8c6573bee519e5232eb4ca4ab4a33acc6318c38ca4a842519ca64c6379be523195d766ff69c6fa9f7e4c952954a524c6318ca632a8c653292a51ad318d8318c624c931a4a5184a5184a52a94a498c6319553194dea3195ad18ce318c631994956946d18c637dff0450bfde2ff9bd12285554015556328015556b2a4634bfe6f511551284a52943246f1a4ae776b5ad6a5a 23 8388607 9 511
def hc_81_4 : Nat → Nat := uH 0x23e0e400000886393d8b55d18d6d7e875d475add06800000a7a7d5230d00000129cf872d1132f3396419c954e63dc6717b39853b5029006142030452e0000000000000045 0x2560f31295ac00184e4a8425049ced583dc6b56b6800709e95084a3183e00000028102ab5900900060652556b2803400381d6955acad4a50043c4a1295b58c6691271bb46a80840aa96b0aa210845ac2a884214a5297d41401561556caaa94a252521555926555aca35a1555d2e555aca94a52f3391865237a46f9494a0cb24415084a33939de67a70eb4e7d3bf5a52b43974882a10946319d400507ec2528c4a50ab0d956b323199894a43292ab595a719b8d6b43ad2ab595a94aaa802a88421002a884214a529555005555aca005555aca94a52800aa00aaa6519400aa6318cab595554015556b28015556b2a5294a002a802aab94e5002ab9ce72ad657c01001554014a010002a80480c0ab59400aa01a0702ad654a5295b29442404a108463094e7095420108014421081ce 21 2097151 9 511
def nh_81 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_81_4 (Nat.sub p 512)) (hc_81_3 (Nat.sub p 384)) (Nat.blt p 512)) (hc_81_2 (Nat.sub p 256)) (Nat.blt p 384)) (hc_81_1 (Nat.sub p 128)) (Nat.blt p 256)) (hc_81_0 p) (Nat.blt p 128)
def f_81 := uF 0x2190330b14985c1742c1240169f09b5684d1a002d2e0c2a708019830a8c1814e0d05d06051005a3c0c8d206271031348181c40c0d0016870195180c28bf8d160028d000197f0a4bfa119fd05cfe04900527bf4061f7292fc02c7dc24bdcd75f5080f99467cc0cbdc545f1280f78467bc173dc1440148e00a3f7a5a7bd2d1de946c00a3a79c0cbc8505e505cf20410051bbb4929da48eef94377c21bb4919dd032ed13376c173b40cc0146ceb049758243ac1100129ee4c57725a5392d19c928ee8041724a339206dcb694e5b4672c23392065c902e0094b7192e38c1440128edf34a70c20b7c519be25cdfb4a6fc2337c06401286db3566edaa36c97db86d8dc1606d92bb6c8d00127ed9a586ccac358d7db12c0d63576bca2b58969ad032d615a0049db540e5898b4d3c5869cac31297da58c0c4a5768ca6b12569a029ed01476242633a9699d0acc484166ca431493d8a48ec514a65cac31413d8a096c9a5c64ca431411d8d2a8c80446342231c1118d068c504362815b1409d890800093761caa2e8d7d844c0c216c5d1abae85718049ac02455d0ab2fa93d7d48eba1545d09a2f293d7948eba0185d527aec5417548eba01400499ae41056f28cb80465bc0c8024ad6d062009275a4a4ad2521692880084f5462baa2d295168ca8a5b5452baa292d602a0b005c54523aa211d5d282a884654417aa6d295368ca9a5654d252ac1015348ca994a54ca32a20b95104e0084b5252e2925454d030a494b528a82941814928e008474e1a527092d442a0a205c4e123a825054126a9c0464e9a52749293d0809d2464e8a52745193805c9c01e00421a60d59356a89825f4c9b6264181304ae982340041fa5a5612d0b08eb5f4ac3023ad5d28250940284752da4a4a1250508ea53488942440a11d47690045474ad23c0b91d0b40083b46c9c9d5169188b08c0583a92fa2d180ea4ae8995c44c0c1d456d0f2b88794443c0c1d454d0c29e861473a8a6210969084a4841563a8a0a0c120f649e7b2473d8a7a04060f62968025c3d8a39f2950fd2887c9443eca21f24d0f90307b1433d8959ec49cea28078a503c4ae1e4500f10307512b3aca09da534ed28a759403ac269d41680106e74054355af9ca580e50d86ab573542e1c2934e148a6a856379279bc91cd50a86a834369279b491cd50586b24f35c281ac91cd504800833321259a2540d10b86424733ca0990118c94946604032523192528c928c6402e0041598c4c40104e6195430c2c16ad7cc04c06016c2d5ab97c060b54b65e0182d529974060b54765c1412d4ab16c054b50b40081f2c92c164150a36be579602bc36146d5cad04c51a5a2ac1e14656ca90785195329c1e1464eca50825185628c0f00206ca14b04db5f2753013a5809d0c04db5726d2d00205c964b04b1582582c12c150028be48a60244b01221b0910c0014572312c1185608c0b046054009af9101b08908844060009ab804d28824a0411502082e1041400268e4005c1e9ab0f49087a2843d04e1ec2a0f41080268c0125b1d1a50e8d18742543a1260092d0e4174024ac3823c009298048ec022b633b4a19da30ce968674ac3392d19c92804568632943194618c2e80455861258011530089d8bc5205849e2d05c16c1a0b41405848e2c14a008920a69a0532d02a15814c9200417c5105826a34134b609a0f04d0580105b115a508ad18450ac242341142308a0b84503c0105a0f9b607c9603e2b01fa5c0fca407c490020ae1735d0b9a685cd142e4bc1c2340b92905c9342e48a1a25c0b91d062d4031488172360b8a085c104020ac1602c0791a052490290b80f1640949204c050250a80f05408492044050210a80f0440781e03c0b0020a60104b0652d032568190ac0104a05da200411c0a8b405356029a70148d40f4940793203c190148d00d4680515a02d1a0141680208c0402c0151a00a0f0050580103b00c920040dc010260001f 10 11
def ch_81 := dN 0xff00ff00ff00ff g_81 ep_81 2 3 bds_81 538 (dT 0xff00ff00ff00ff [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff] 8 f_81) cur_81 nh_81
set_option maxHeartbeats 0 in
theorem rc_81 : dR 0xff00ff00ff00ff g_81 ep_81 2 3 538 bds_81 (dT 0xff00ff00ff00ff [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff] 8 f_81) (cur_81 0) (nh_81 0) [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff] 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_81_0 : tB 0 32 ch_81 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_81_1 : tB 32 64 ch_81 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_81_2 : tB 64 96 ch_81 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_81_3 : tB 96 128 ch_81 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_81_4 : tB 128 160 ch_81 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_81_5 : tB 160 192 ch_81 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_81_6 : tB 192 224 ch_81 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_81_7 : tB 224 256 ch_81 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_81_8 : tB 256 288 ch_81 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_81_9 : tB 288 320 ch_81 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_81_10 : tB 320 352 ch_81 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_81_11 : tB 352 384 ch_81 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_81_12 : tB 384 416 ch_81 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_81_13 : tB 416 448 ch_81 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_81_14 : tB 448 480 ch_81 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_81_15 : tB 480 512 ch_81 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_81_16 : tB 512 538 ch_81 = true := by decide +kernel
theorem nj_81_1 : ∀ i, 0 ≤ i → i < 64 → ch_81 i = true := bJ (fun _ h1 h2 => tA nb_81_0 h1 h2) (fun _ h1 h2 => tA nb_81_1 h1 h2)
theorem nj_81_2 : ∀ i, 0 ≤ i → i < 96 → ch_81 i = true := bJ nj_81_1 (fun _ h1 h2 => tA nb_81_2 h1 h2)
theorem nj_81_3 : ∀ i, 0 ≤ i → i < 128 → ch_81 i = true := bJ nj_81_2 (fun _ h1 h2 => tA nb_81_3 h1 h2)
theorem nj_81_4 : ∀ i, 0 ≤ i → i < 160 → ch_81 i = true := bJ nj_81_3 (fun _ h1 h2 => tA nb_81_4 h1 h2)
theorem nj_81_5 : ∀ i, 0 ≤ i → i < 192 → ch_81 i = true := bJ nj_81_4 (fun _ h1 h2 => tA nb_81_5 h1 h2)
theorem nj_81_6 : ∀ i, 0 ≤ i → i < 224 → ch_81 i = true := bJ nj_81_5 (fun _ h1 h2 => tA nb_81_6 h1 h2)
theorem nj_81_7 : ∀ i, 0 ≤ i → i < 256 → ch_81 i = true := bJ nj_81_6 (fun _ h1 h2 => tA nb_81_7 h1 h2)
theorem nj_81_8 : ∀ i, 0 ≤ i → i < 288 → ch_81 i = true := bJ nj_81_7 (fun _ h1 h2 => tA nb_81_8 h1 h2)
theorem nj_81_9 : ∀ i, 0 ≤ i → i < 320 → ch_81 i = true := bJ nj_81_8 (fun _ h1 h2 => tA nb_81_9 h1 h2)
theorem nj_81_10 : ∀ i, 0 ≤ i → i < 352 → ch_81 i = true := bJ nj_81_9 (fun _ h1 h2 => tA nb_81_10 h1 h2)
theorem nj_81_11 : ∀ i, 0 ≤ i → i < 384 → ch_81 i = true := bJ nj_81_10 (fun _ h1 h2 => tA nb_81_11 h1 h2)
theorem nj_81_12 : ∀ i, 0 ≤ i → i < 416 → ch_81 i = true := bJ nj_81_11 (fun _ h1 h2 => tA nb_81_12 h1 h2)
theorem nj_81_13 : ∀ i, 0 ≤ i → i < 448 → ch_81 i = true := bJ nj_81_12 (fun _ h1 h2 => tA nb_81_13 h1 h2)
theorem nj_81_14 : ∀ i, 0 ≤ i → i < 480 → ch_81 i = true := bJ nj_81_13 (fun _ h1 h2 => tA nb_81_14 h1 h2)
theorem nj_81_15 : ∀ i, 0 ≤ i → i < 512 → ch_81 i = true := bJ nj_81_14 (fun _ h1 h2 => tA nb_81_15 h1 h2)
theorem nj_81_16 : ∀ i, 0 ≤ i → i < 538 → ch_81 i = true := bJ nj_81_15 (fun _ h1 h2 => tA nb_81_16 h1 h2)
theorem nc_81 : ∀ i, 0 ≤ i → i < 538 → ch_81 i = true := nj_81_16
theorem lb_81 : LowerBin 0xff00ff00ff00ff [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff] g_81 9 :=
  lowerDagV5 (kn_cons lb_13 (kn_cons lb_19 (kn_cons lb_25 (kn_cons lb_32 (kn_cons lb_26 (kn_cons lb_34 (kn_cons lb_6 (kn_cons lb_1 (kn_cons lb_8 (kn_cons lb_48 (kn_cons lb_47 (kn_cons lb_49 (kn_cons lb_50 (kn_nil)))))))))))))) rc_81 nc_81 (by decide +kernel)
def m_82 := 0xff00ff00ff00ff00
def s_82 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_82 := 0x100150013001f00
def ep_82 := 0x12000a000000140000000c0000000000000000000100040002000e0001001000130010000100150010001000
def bds_82 : BList := [(m_14,s_14,5,g_14),(m_33,s_33,5,g_33),(m_20,s_20,5,g_20),(m_35,s_35,5,g_35),(m_51,s_51,5,g_51),(m_2,s_2,4,g_2),(m_7,s_7,4,g_7),(m_53,s_53,5,g_53),(m_57,s_57,5,g_57),(m_52,s_52,5,g_52),(m_54,s_54,5,g_54),(m_55,s_55,5,g_55),(m_56,s_56,5,g_56)]
def cc_82_0 : Nat → LPN := uC 0x420841082013b5760e85d03736c2d81b03606a2c5188301600c0169ac1580b0158ab04e89c1382614668c1182303e87c0f09e0384700e01b1306600c018028850098930224440881102203500e001 0x36279a83cb928c6906647bba39d11ae44d316933341c0a2d6092b6837451b52758496a04940449daf4cd4a506b092485a14714a24bd01247c12b8171d492da4560973297982bcb8250c0aaa09146a4983d40a6228e4f46a582e352718494b09c1016249210d08727a2a3a1119064f8207d9b43bd27d290e447ef23368a7ac4bd224e703f28178c09c102e001f 11 2047 4 15 11 2047 17 131071
def cur_82 : Nat → LPN := cc_82_0
def hc_82_0 : Nat → Nat := uH 0xa2e4e5a6300002598100002324f8ae34000000002298488c35f45e00001f2830000000007254dc40a00001c2046e24c000061b90000000001820955d5800005482800004b52800004ae0c000041338000000000ff8a34770000000000cb0d2678c00002640400001c148688f00000620d174282fdb0017c0000 0x23fd340782004a190bcc97023199c6d0841e283cae1c6718c6ff17d06280f14212814a632946329c6d5842f1584290a4c95331bfcfac245584217828561096d65b49b18de68a42f7941e20213a338c67fca90856564afbaee8c677824214944275d5f368d17f0188c76d324042f1184232ff8b8142158c6d2b8c631becd663781c62118ce90b3598c6ff37be6ff7f40ed0852d68424c819532fc00210321095701842318c99 18 262143 7 127
def nh_82 : Nat → Nat := hc_82_0
def f_82 := uF 0xd11cea4f35079a23505a1e44d3069381450527d5146a49d5125ada0d40901487404495af4ad4a506a0a3f7e293e97a1684f9247c12828cdb492e05c6d228253d74bcb95e5c12824bd50489b524c1e8249cf472814c3d1a820fcb49c59252c27020bc92483b421c9e8209c24741232089f040f8102e001f 6 11
def ch_82 := dN 0xff00ff00ff00ff00 g_82 ep_82 2 3 bds_82 56 (dT 0xff00ff00ff00ff00 [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00] 7 f_82) cur_82 nh_82
set_option maxHeartbeats 0 in
theorem rc_82 : dR 0xff00ff00ff00ff00 g_82 ep_82 2 3 56 bds_82 (dT 0xff00ff00ff00ff00 [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00] 7 f_82) (cur_82 0) (nh_82 0) [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00] 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_82_0 : tB 0 32 ch_82 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_82_1 : tB 32 56 ch_82 = true := by decide +kernel
theorem nj_82_1 : ∀ i, 0 ≤ i → i < 56 → ch_82 i = true := bJ (fun _ h1 h2 => tA nb_82_0 h1 h2) (fun _ h1 h2 => tA nb_82_1 h1 h2)
theorem nc_82 : ∀ i, 0 ≤ i → i < 56 → ch_82 i = true := nj_82_1
theorem lb_82 : LowerBin 0xff00ff00ff00ff00 [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00] g_82 8 :=
  lowerDagV5 (kn_cons lb_14 (kn_cons lb_33 (kn_cons lb_20 (kn_cons lb_35 (kn_cons lb_51 (kn_cons lb_2 (kn_cons lb_7 (kn_cons lb_53 (kn_cons lb_57 (kn_cons lb_52 (kn_cons lb_54 (kn_cons lb_55 (kn_cons lb_56 (kn_nil)))))))))))))) rc_82 nc_82 (by decide +kernel)
def m_83 := 0xffff0000ffff
def s_83 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_83 := 0x153700001f7f
def ep_83 := 0xa48000000000000000000000022000000600000040400000e0800001032000010200000150400001040
def bds_83 : BList := [(m_21,s_21,5,g_21),(m_32,s_32,5,g_32),(m_27,s_27,5,g_27),(m_36,s_36,5,g_36),(m_58,s_58,5,g_58),(m_6,s_6,4,g_6),(m_9,s_9,4,g_9),(m_59,s_59,5,g_59),(m_64,s_64,5,g_64),(m_62,s_62,5,g_62),(m_63,s_63,5,g_63),(m_60,s_60,5,g_60),(m_61,s_61,5,g_61)]
def cc_83_0 : Nat → LPN := uC 0x420823041f1be07a2f41ca390702e01a9b506a0d0582300600c01802e25c0b45682c14ea9c13823446088510202400800f89f0386700e01843005c4b81522a0540a0940226440881102203500e001 0x370813a4dd922ea126246b9a5d851ae454310a379509da6dcd16d2930236adaebe8daa2a34850949c480e222a100509e2f4d16a38a50b567d2b2c8e9d26c2821700cb40c1926cc01954242c96942bc995628a508489108c802e38a01a118c05c494828ad1017870ac2a5a10ad0617820ada34fc1a3d893e848ef2376ca5ae50d2256784b2c218c0ec1026001f 11 2047 4 15 11 2047 17 131071
def cur_83 : Nat → LPN := cc_83_0
def hc_83_0 : Nat → Nat := uH 0xa500c00009c91000009b030000090b4c000090804000084f740000000020719743b4000000000000000001c59670e11be8a6f211b888619940000000015f4e000015d83000013ac64d03400004b43800003fd70000000000ce6200000cd8100000a1d82722800002641c00001b75c670d188285a8f000002dda0016c0000 0x6f50a04255cb9c18dea04a1407894214aa54e5328d840217d85612998c691a521584230a10a2c2b0842f1366c6358d6918de2f137dfffff40810020f4d738126f1a41a42bebb9545381584ba636b5d7c147381189731b5fe2f11a0217a2b186e0488464d236b1bcd66918c630a056909746beb31bc42318f029484ba35ff9f3079810955e0c2f484e5d07f9bfdf37b03084657f5a34e05a90932c20428e4122318302918465 18 262143 7 127
def nh_83 : Nat → Nat := hc_83_0
def f_83 := uF 0xdc206a91750920b4fc52ee254310a20b47bca85ad16d2920a4fa5aed254690a00a477e2f3f16a427120387e2944541f6ad00507d2b028ddc26ce01904a5b40c1826cc01904a1a69695090995e4cab024ad008c802e04259c500c08c602e04218e5689290385e1c2b020ec24b4115a082f041581026001f 6 11
def ch_83 := dN 0xffff0000ffff g_83 ep_83 2 3 bds_83 56 (dT 0xffff0000ffff [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff] 7 f_83) cur_83 nh_83
set_option maxHeartbeats 0 in
theorem rc_83 : dR 0xffff0000ffff g_83 ep_83 2 3 56 bds_83 (dT 0xffff0000ffff [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff] 7 f_83) (cur_83 0) (nh_83 0) [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff] 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_83_0 : tB 0 32 ch_83 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_83_1 : tB 32 56 ch_83 = true := by decide +kernel
theorem nj_83_1 : ∀ i, 0 ≤ i → i < 56 → ch_83 i = true := bJ (fun _ h1 h2 => tA nb_83_0 h1 h2) (fun _ h1 h2 => tA nb_83_1 h1 h2)
theorem nc_83 : ∀ i, 0 ≤ i → i < 56 → ch_83 i = true := nj_83_1
theorem lb_83 : LowerBin 0xffff0000ffff [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff] g_83 8 :=
  lowerDagV5 (kn_cons lb_21 (kn_cons lb_32 (kn_cons lb_27 (kn_cons lb_36 (kn_cons lb_58 (kn_cons lb_6 (kn_cons lb_9 (kn_cons lb_59 (kn_cons lb_64 (kn_cons lb_62 (kn_cons lb_63 (kn_cons lb_60 (kn_cons lb_61 (kn_nil)))))))))))))) rc_83 nc_83 (by decide +kernel)
def m_84 := 0xffff0000ffff0000
def s_84 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_84 := 0x115000013370000
def ep_84 := 0x1222000000000000000000000014000000240000010400000204000001100000133200000115000010040000
def bds_84 : BList := [(m_15,s_15,5,g_15),(m_22,s_22,5,g_22),(m_28,s_28,5,g_28),(m_33,s_33,5,g_33),(m_37,s_37,6,g_37),(m_4,s_4,4,g_4),(m_38,s_38,5,g_38),(m_3,s_3,4,g_3),(m_7,s_7,4,g_7),(m_66,s_66,5,g_66),(m_65,s_65,5,g_65),(m_67,s_67,5,g_67),(m_68,s_68,5,g_68)]
def cc_84_0 : Nat → LPN := uC 0xd003400cf073c0cf03381c623180c603141c503101c20b080c203041c103040c006fc1b722a0fa802a00a802943a502901a402843a102801a0028009f067c09f026c493224c0920648092023458d023408a0e2808a02280870e10384021008402100810e0407e0df807b0dec07909e407805e007801d827601d807115c407005c006f05bc0642d90064018c1600d80060017c15f017815b0d4c8510940150013434c052c14b0124249012404901240480520048010863c18f003b04e423804e00350cd013304cc03108c403100c403100c013000c002a1890624008c10188001 0x1f4a00d88d08169c3fb421f9250f89187b27a391351e8948f248476268369301cda00d84807048036a301b11a0ee938754843a23a1c91b0e25286f28c3713e1ac99152d3ca769651347279a193a93c9b4964b247249219208fc8e47645a3721d199041387806c35026178268cc1145b02a3205d178a68c45145a02c3015d1749a0bc9785c4a42d95e1682f0d0d2c676862ba3e194a78c651c6109e2f8471640b8ae070558a02a04c138220a20d04d0482913d1389a8a24944f474272361349b0a68dc5006c260261211b88e4dc4024e1f14d114a286c4943e49a21a450d09307ad40416901fb480f6280780903769c1ca4e0d4a70600d42a02a1ba300d5180811483e6bc1db520e9a0870d00364bc1a15e0cc1e8560d42f04a148150c1a00624f42b26a179250b1a8054d002d47415a360a49b094d3849686233421112788453c3224e170270a00b83c1301c0480d824095220340d0240480c8340601203c4f42026a0d9340792703a9081c29c0d1420649d0304d82649e11a430891d8428dc1f09c0b8260541301613009068040340491a00e11011068030440141a0168f40d46a0412402da7014d080949c03a420189680a4941369e0834303d1f81c8dc0c09c020360081b430d3e1269706347815a1bf893df8496f9a477bd21bd48fde7476ef23771519b6253dad296cf947658a1b164fd88276bf93756c99aa44bd482567c9273909195412c690862c03e1581d8960cc270640b02b0501180606c010260001f 14 16383 6 63 11 2047 21 2097151
def cc_84_1 : Nat → LPN := uC 0xbd05e82e496c3b50cbfa5c12c1950ca065012618f247823c11a28d0450e28112189040260010007e13e85e48ee27703b05d80ec07603b01c88e40710b881b48d626b03505a80d406a03501988cc0650b281848c205f12f81744ba05d02b99582ac0550a9894c0a604f227813c09e04f027053809c04e023211808c046023011808c0450a2811407a82e79684b405622b01580a8254025292809404a022190848403e21f00f807823c01928c806403201618b0050428012109004421a40d005882c00e407003041800a10120080040001 0x8025e7fa527f15e7e93e75a30028340c02475230a1c5b9f4539eb5f9cb5e9b35b99b5796b539335292b4f91b4e913438f3428e25f8aa5e8925787a528695f8215e809577e152749206285b458532c84e29843190427d83b7d0331082b0701b7c1447415c78a40782407ab5077a407a15c7985078b407804077b547395c77028760247ba4f7b24b7924776a437314e6204b448437582b7502374149739417312474a347295e6085b438535e84c5d83471034705606fa5c6f2506e85c5d0346da386d2345c8446c8345a04c580246b0246a56069b5c693506885c5782467a4c6724457034668245b84465834568346482463c60622306304c588445b034560246182461a3462344610245ea3d602355a13d5f9355d1245eb4e5e3425da4e5ca425c13d589355b92d5b125579345a24e59a425923a58a365814e571425693a5613671b4f70b4b6e3476c3436ba4f6aa4b68247662436523f6423b62a3760a335f04e5a836558264084c3f044540343e8345356052a5c522505185c3e03450a38502344f8343b84c388344e024380244d5604cb5c4c3504b85c378244aa4c4a2444982448834370243d044478244512046c6044a304604c390444503c3603444b443c84435834440244314c4224c40a3d42a353b93d4193540124 13 8191 5 31 11 2047 20 1048575
def cc_84_2 : Nat → LPN := uC 0xcf1cf0cc3cc0cb1cb0c74c70c43c40c31c12c10c01bf1bf0ba5ba0b91b81b71b70b61b24b20b20b02b00ad3ad0ad0ab2aa1aa0a1997a9709529329309129109108e38688608428408138107f27f07d27a37287207207207206d56c16c06c06c06576146016006005a65915905455225024a64914904814444313e53e03d13d03d03d03c131b3013002c42a22a029129022722021121021021020120020016a1601601331301300f40f00e10e00e00e00d10d00d00d00d003a030030003000000 0xb6924bf254be954b8934b4924bdc60bd26cbc96cb8134bb946b7926af924baa456784b4a843b6944b495cb9352b8a5eb8256b795e12829b6944b095cb3240b2a40b5350b2240b495cb4050b3340b2840b2354b015cb1828b0949b01410d824b624fb5a4bb3a47b1243af94e6704b4a043af02bae823be35fbc357bb25eba15eb993cb7136ae1346605b490531183bad24688925aa1559d145abb547f124aab6c9d26caa25cacb5eac25eab15fa9957a49256505b480530781ba8a5488934a7a6c9d96ca595ca69467f126a5a559da459bb5288a5e7f15ea835fa7357a625ea515ea49366405b470531103b96360a3b48a3344a2a44a21442084095b6090b50a1348a0b44a02449f944200509c368872548e9547b9201f8409bc5e9e3499da459d1452f03e1f03298a549c46c8db6c9ba4c8616c7b130993507a92098350799209ac6097b508126c8996c791209a06078930781309945098a5c77930980507712097c648d36c8596c76930970281e850942409645995c518a3559524e8195563859468512e04e1d8429482a938268fb509235e8fb4d8ca5e8515e8fc5c1d0501c83090c528c35e9025e8fa4d8495e2a8411c0408e9541b8308da598d2518ca3e8c2328415e801528b94a8b1462d83e1b0328a35088a6c8996c88a5e8823e8395e7f952872541a8308625985a518523e84a328415e839528314a829462d03e1a03281b508126c7f16c 12 4095 4 15 11 2047 20 1048575
def cc_84_3 : Nat → LPN := uC 0x850202976d1da07681da0750dd40738dce06fa1ae86a89a6269819a666819816601942612184061017c45f017825e017805d097025b096c057215c0558d56055055025401500519542250054004f853c14e853244c813204c812e24b812834985260452500a4000fe13f80fa23e04f423c08ee13b80ee03724dc03700d633504d403500d21330ca542900a4029009e32780983260088822008802108840208482020808011e106881a0064219005c41608580150854012184801184460118040310004000f083c00e082880a00280081020007081c0070018205081020400008 0x193692ff341678a93244f97e264a892a474930cc0f8450650235380da5c02d25ed682f5a3e7711938057d9d2a69c94d800a5bfe51dfd28ac893f5f099ab24b5502568e127454928ca0f844064fd9287e892bf24917b282c813d7dc9abead65906a29da5563c9f2f44c94f254899261901f3ecd45f24bafa15d6389faf04cd4e2568912718c1f2745151124a9ba52670a93e4979bf2becd95343c9abe2495f0050f71357b1a52324b5ed6a4f5a5e6dcafb4c55d2327a7185b2a42982606de94bc7085b29c29bd00a0e00b2530517901dbc60ccdf096528433782594810de68b0f2c5278a283c2531e02806e05b28829bbe101dd48cec125754923b6514db09650843761af3ae949b32bcd09560480cba6525ce282da24474dae39a501cc280e8b506892e396501d00a0e6b407302039cd71cb4a8e50180201a3aa939d429ee914b73ca3b9250cda096500437200db8e04ddc6bced25e6c8afb4055dd9250eb125718921b016c9e0a60801b634a63728f5c246a841246edaa20e4d13b4a88313441492372d65bc6a2dda426e11f36c8c95725a871251881f0860c9b96b0dc2544289e368491b4488db3546d52a366491c46a6e1b4b705a4b28d05c04bedfa534e526b7c92dbd48edd2456dd1fb648cd8c27cbb13255897a984a90d24e821261841f0840c9b0278d79366b89a34a905a847ad62356a9a4b50d05a747cd22324e8a2aaa4b50224a3003e6a1b034e9b1a2248d125c69630348db1a34d8d09246ada8b52975a647ed0233668aeaa64bd0124e2f83e6792a2008d0ff488ce234664a226e4d13b48a7f1264dda93329499d6becdb533f11b3345799826ccb8186551ab26d6119478c9154641b031e5b18d6948512d651a932297d8e4ae91a3d630af1ae16c9d0a61302b628af1aa16c9b0a6c48183502c93414585076c203334c2593210cd20964c04361e2c30d149838a0c124c605201a016c960a6c0040 14 16383 5 31 11 2047 21 2097151
def cc_84_4 : Nat → LPN := uC 0x2d0a8ea0a82739c2437d5f07c1f07c1f069591641635455048c6c180511403204801 0x10bc5e864240940c21627aa313551492c288f54646aa212685da742a8d61326aa19271a027422972104a10795c838a841a140480a10513d5049aa80494470a103a3d5051aa7e49a044bef6a3d82d1bc128d5c42beca13d8209bc0c4d53e24e3384e1242108c101ec498c993d8089aa2e8d13a2a88b124 10 1023 4 15 11 2047 21 2097151
def cur_84 : Nat → LPN := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_84_4 (Nat.sub p 512)) (cc_84_3 (Nat.sub p 384)) (Nat.blt p 512)) (cc_84_2 (Nat.sub p 256)) (Nat.blt p 384)) (cc_84_1 (Nat.sub p 128)) (Nat.blt p 256)) (cc_84_0 p) (Nat.blt p 128)
def hc_84_0 : Nat → Nat := uH 0xd2201748004d1704b44a09d0e02400000ce3954000000000033720ecd802400000cd402334605ccf81331e10cc302400000cc101000000c9715305703bea15eebc76000002de46c000002d6241000002c886d000002c064100000000000aff812be80baf482eace82a6fa228809f9a3be665a1a9960065ea370000025c413929a3c00000923832468138d3a36047847ce21de1691780829dee0a71f2e4000006df2000000069ea040000069604400000695805a4e0468f025a280a68283c0000065e9219740365782d95a0265102d938066111e80000060f80d8240d5c4a2400000000001706065c08096ea0c5762254b49251f0714600e51700941a214f10ad372294db00d2588a00000125402492018000000000012400448c81d1487539fd94d6c892a15d0a4c1c28c038a2c0227a8849942b2500a893a03209a28000002088088160600000000000203810800071c51d844b650cda2804f7400009c00000 0x12ff4bfe5ff2a052fad2918c0a90810a578a5f2a497f97ffcbe814a213da520548c1852ac16b05ac16528015ea5294a9294a5294a5294a9499329485294a4291a52948c07c142a0450a0702706836883ea52ab280a529ce709c2d6b46d1a12e5ca52956502f040e7294633a0e502aca1c00bc0d8ce9d294a55942106f0c1ad295a86940ab280468037d786f05ca072b94a529caa518da55284211846755294a529ce72b94a52b5ad2e94a529da7556d6b5acab6b5acaae739d294a4aa94a5294a52aadad6b5956d6b5955ce7394a52955eaaa5294a5294d9115544ab9532ba554f2bfd5fb95ea92a52908de634bc1652aad673a52319d252a4212292894257f94f8852e1652a842b5b5ad4a5252a4632692994657ed66d6b5ad672bad6b5b4ba769ca52a4a52a4a5294aaaf5295252952529525295295a4489494a5485294a4291a52948caecd82cab60b2ab9ce75824b6b4ad2b4ad2a83ea167395ce13856d6975a368d6b2a50a95c7d1d6c58b38dc762c5b47a3769d6b05a4a51654ad2b4ad2b4a15acb9702f040e718ceb5ad2b494a94b1ad674e8420de1835ad5ad695a4a54a5bb4effaa72c89dc6eb42308ce5ce52b5bc35e0aae072e57394c6d28842308ce52a5276b634ad6b0594aab59ce948c674aca5084290a5f550a56b582ca550856b6b5a94a56528c6348d2fd9b59ce575adad2e9da75a569294a74a5a94bfe5a91bcc6bc5e6348dff2518d251a54bcca518d6c07295ace7295263494a54952528910842bdfa56b385944a50ad694a4a548c23094ab5ad6b5856159c270ad6b59ce1094a9294a5294a5484257a9421294a54ad2244a529326525295234a52918421584e1672b84210ad67384210952328ca52ad6b58561084210842b5ad6739ce108425294a5294a548421084257a94a50ac204084270912210842118421084250bfe4e90bc42bcde21485f257885250b2a5e252842b60394842b5b5a52a64a52a4a9294c98c635efd2f0596d694ad650942929521184652ad6b5ad6b5b5ab58d635b46d18c652a4a5294a529525294a3195ea518d2b4891294a4c994a4294a521294a318de0b69756b6b46358c2308c632a425094a55ad6b5ad6b6b5ad1ac6318c6318c6318ca5294a5294a9294a518c6318caf358c18318da3264c6308c631846318ca35294a5294a 22 4194303 9 511
def hc_84_1 : Nat → Nat := uH 0xa7405d358267e8e33d80e9dd07c6e40635011198088bb08c5b8122bc111560489e068000000000112c088920244004a1e0110e00886704bd6ae8000000000078613b7e229636deada2056c00aaa06154008a9804548022a081d4a430a4a0451c048000013f0409b8204db00a618612fc08976044b70225801d260309280448b048000011ac400000044b100000010ac4084e0442202a03070fe41a00000000001f105cf7c067b8033802e000000000006f40600000000000000000000036f059990f4000000000000000000000cb00c0000000000000000c84165c83d23b5491205c88c02406201f3080f7810798123c0061c0100de0106e0083680419d0b8c305c614022ca20156078a901052412286061231008f81046c0822e041000b87e010380381b8040c00e05b8240000013e180000004b820000000f41d0000003a814000000e20400e31800000000000000e 0x782f16b41ad6b463194c2308c2d6a5231aa4a9295ce072e44270b4ed08c6318da339ce30842108c6108ca529ca52a4a5484a11946ffffff15fffff7abfffec4afffff5739ce739ce7384210842122442b17a94a7394e729421085096edce73a12e4c420409c23183067184211952549cee739c21084270842118c6319c6318c21084211842040842709122108421184a529ce539c210846318c210a425085fea90e05ff9290ffffbfea909fe2ff928420ff548d06ffc9487fffdff5484ff37fc946307fc942107fc9463054be4a011bfc5f25082d8463029525494aa64a92a4af3c3500319521284a52bcf0544200548ca3294aaf005294a5494a9294a52a4a5280004010001800147fc9d2ffc94264fa2f7f8bdff549642fffff1485ff2d4bff251993e99ffcdeffaa4b237ffff9a46fff14846fff11a46f57aa5297ff88c290b3363502a52108c6052a4a929443e46 21 2097151 9 511
def hc_84_2 : Nat → Nat := uH 0x7e600be984df300ef94027c900bdd839ee404f2626000003afccfc26acdff0a6fa02f78029b9c12d1e580000034600da160d0000000000000001a0608000000000033fc0800000cf306000000000019a81fcce036650130a9415cf43ae50154d12e86cff42e049f90f4fa8127c4093b616877b24398121444509a048370b41a00dfa098fc80476340b71a015fec8aea0a000002b502d57c16a78230000029783546c28a10134df14a6c01c0000000000000002568ad2a40893e0a48e08800000000008fc100000023d01000000000000000022d080000008960f44204a1f01000000872053e42a9e287ceec146ae6432a16987070000005fe0f2505792203086456000002150210502c7e024000001f5018d2940684083300917a0f0b782c598121ec700ec050618a40000017e040b4058510482601411a0b000000458080e8a206c0402b058068780081600002 0x2f37bbc630bfcffbe6f030bf194420368c631b5a91b1b46683f0846308a94a92a5ad5cb8421084a2318c632984212a529cae70842118c6378d25786f9bc6fb10bc0e5739ce5718c65109119446b31846339ca92a4a53bdf35d57c65632d8b5af7fa75a5d18c6318caa635a63194a56975a528c631ba74e7395c6318c631954de6718c6318c18318da31846318c630955295a5d694a718c6318c6919463509404e118ce709ce90a139cb931081027f039c21294a92a4e77ce7805ffff00837f39ce10842108421384210204213848910842118ce719c670846f108421094a539ca73842108421484a108ca37f9bfc780df1bc0c6c6510b5a0368c6d6a46fc6d69d27ef06b463020463294a92a5ad781cae109c6118ce108461084e72a4a9769da109da1385a318c6318c6338c211bcc6108c60c18c6d19326318c21094a569cad684a118c6318c6919463495e1bc1780e168ce8a97de635fc42f13370b46778f29fbca92a5f254630bbc2bfc184232bdebd4aa5ef794c318710215292952e746709d256e72e9da573846119ce72a4a9768ca6709c8bbfcd7bbcf7739caef037298da33ad2bbc46119c257084b9ce54952f02f780de23085fe1bcde2d094f03018c6339c214a5fe2f018f30bc378b9c0e70944e708423084273a5210bc2fe010bcc637f82f179af0f056329e02010842d68c694bfc178040bcde0a 21 2097151 9 511
def hc_84_3 : Nat → Nat := uH 0xa2cc0543512676582cd8e9e99010f2d8a3e4b97c494c139134b322580a40a20c67ccc8b58d11389961ba5bc09f6b000000fff941ff9033f385d798e72efc9a9d5e4db8c8fa6fd4dedb522db660236b00e6ae53ed13a499884fb1da9b5fae04bf381179c258000005cdccab45ab1679092cce1256ed58ace87959802800000562c1a000000000002b0608000000000000000002afe04000000ab903556c032ad0045321409c2d0d359162682184d000296e98d2b11624fa3449a82692a059252012492094800920000011fa0323ae230000008ea80800000239a0846ac4485540500c4f1f008c3ba92c6f8be4dde099af86235e80469c904000001a660634782a688038d0c021a140200000067b84ccdb0e181ecc3018125e88d4bcd0217442b2ce4d259a810acf331430b722b2d800000085b2880000021540c4180940000010540620502c40681c7af2f0ced39182cd62b826c4767d080e6f0df1161bc01036b06859a9e08f1220cea7c1024d800102 0x140250409fde5495252a109c1e5cf805e02100e13841e378ce7084a0b29569295e92acab0ad650acab2adc0021084006318c2108400a75956b0842118c6372b84210801ce738421081d6549525595684210039ce7084210029d655ac21084ab2adc02f001084200700802001ce7384210800c0000a75956b08421012140ab2ad1f54af738d72e319d6b5aca92a55f084000a92a56b5a000000000bdc2708000c00e708428009002acab58565095655a5c98782070bc630952549d6b0bc0e570210ee70842139ca92a560b08042108560b39ce7084214825274a529084225294b870e7084002f138421084213848910800739ce10842108423084250594eb2ace10ac21084210a421294212acab71b8c4237198ce72a4a95f0973ee077a082118ce73a52b9739ce1c38421384e13945ea212bad395ce719ce7184ed384e5294e57394a7494a7484e5094ad55441081025d69cda30b4a92a4b544210956d6b59544210a529495544210a5294aa8842128bd554455513ad6b4aa21085a12a674aa52aa884212ac954a55695aaa00aa0027384aaa002b284ab2ad55453c27094c71ad6b4e6d19da52955254bfc5eaaaabe1384abad6b42739da12aaa9427284ad2b5ad6b4aaaae1384e1384aaa52b4ad2aa89ca155709c2555318c655118c63094a55513942318c6ab61584ab6b5acaa27385294a4aaa29485294a551455555c27095caaa2fd6b5a5d2aa99544e73b4252954a55592aa89ca12b4ad7c250138463084273a4284e31c188422e63294a92a4e75cb8421084a2318c632984212a529cae70842118c637d98dc5254ae0e572230913ad395c211ac4210842739525494ad425b339dff15d57e12bdfb9708421084aa272b91588425294e5738421094ab970842108425517884081084e12bad395c21684210842118421094a5395ce10842108521284252b5bcd4c9f99ed9cdf0dd1980c662118dad08eb4a92a5185ef17bccfe2f08c2f33d95c5e62f398fbd5832fbde0409525494af7b8c5fe6d5797b885fa3631b40ee9707138b5a037818c068da318ca0b29569294f2559565595635aca35b8004210800c631842108014eb2ad610842318c6d2e8035ad680046118c631b565495255956d6b5a000318c6318c60056acab5956558c631b401ad6b406f00318c6318c600d0080200003000ad5956b2acab18c630121413d54b421006fd68dd3ab5ad654952a800784254952b5ade700bffcfffbe213c5e02f3400000001006b400006fd1b46318500120055956b2acab1aca37abfcde108c2f595f84230acab2b3a4fc2107860d18ca92a5ab58dfe0d2ebdad18c20418dad2a4a9582d60b6b5ad180c6318c6318d2094b5294a5294a46318d1a35a0d6b5a31800de6d18c6318c6318c6368c99318c2318c6100a0b2b5655b4ab2ac6358c6318c6348c6528c6d1e8cc42318f5ad2a4a97bed1f88deef341e6fdf8ce9fd06bd0431842d6b52974eb5ad1a346319ce72bb4e16b4e168da3694dea632ae71b467294ad2eb4a56a4a56a4a538da51aaa239de138463060ca672a4a92d5b5ad655318c655318c694a5255594a52318c6aae739caa6318ca6f55318c67194455512ae54ca94aaaa729c6318cab255296a802a8038ce32aa802acab1aca355514739cef09c27368ca6687394a554952ff33d555739ce5557368ce339ce32aaa94a729c6d28d55ce7395746d1955c67194a5555394e36946aa21084aba368caaa2108421294aaa210846d28d56d6b5956c6b1955c671a5294955652948d291aa28aaaab9ce72b95544aba368cba55537b8ce738ca52a94aab25555394e36946 23 8388607 9 511
def hc_84_4 : Nat → Nat := uH 0x484a26069def5e6b000003a618c00000dd06460d6dacf1bd4b4e297c6f44d389f319cc41ac5ec1a0000013d1f098034000001e53d86a4442a0581201808f008169880602a00018 0x20d82cab60b2ab9ce74824a2b294a5294a541f0501c0e544b955741a54ce9555ce7394165592a94aaaad9565595655a07880e3138468cda32b6b2a4a946ae0f04e7018ce7595254ad6c6ba1083c36b41ad595254ad6f800000039cae0040001ad2e80300ed38014b6b012140ab2acab2ad5401ce738015556558015555655a00aa00aa2108400aaa21084ab2ad5401ce738015556558015555655a00aa00aa6318c00aaaab2ac6318d540155ce738015565294a5294a000f838000400aa1a0003002ab9ce702940012005555595655956f1138ce085c8a784e17b9c666339ce5495252bc4da33861d2282139b46fd68cf5ad2a4a9295401f5401c39ce571b8462346b5a5d1e8c66769ca0b29b36b29569294725595655956bcd449f8bd6bc6f82f18804662139c226339ca92a5fe308de23de 21 2097151 9 511
def nh_84 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_84_4 (Nat.sub p 512)) (hc_84_3 (Nat.sub p 384)) (Nat.blt p 512)) (hc_84_2 (Nat.sub p 256)) (Nat.blt p 384)) (hc_84_1 (Nat.sub p 128)) (Nat.blt p 256)) (hc_84_0 p) (Nat.blt p 128)
def f_84 := uF 0x21909000b4f84da742c4f61346b0a23d84c9a802d2e0d4b906a50834ae41a5420d0a000b478191bc144f60646b0313781d1ec0c4d401686feb537f5a5c044d5fd692fe94b7f4a3bfcd05fd28a00a4f7e4943f2495f924800a4b7dc9abe8d45f56b2fa15d00523be0979f024af802800521bdc4d5eb6a4f634a7ad2f0028fde84bcf40280051dbbf161df8a4f183b78c19bbf141df298ef94077c200028dddd48ce335e76ca2b8c979c6250ebb5e75d2938c495c749ce394f74dae38e52dd06a0e805071ca3b94d71cc680e60407292a394061c7286e381b71c09b8c49001466d93536c9a5b848d5b2692d925f6c929b6492db248eddb516ed21364915b86b0dc2546c91fb66d51b34a8da2446cc923648cc0129ed713c6b89b35c4d001296d6235681a8b54d25a04bad3b6069d363408fda18c0d0b6c68536344971a1248d0233004a3b3c951976bece23465da9b2e579994a4cb93665c0c00250d9546ac6352649ac3245518c4bec7b6063cb631895d8d694c615e0049fb12579890300093b6022c30114984076c20336022830093180480c00400049bafa9517d2a8ae35f5e6302f29b1792d8ae3575dca32b89797548aae15e5709e2ded496f4bcb7a565bcaf2b84d96d288aea4f57525ad0d41682b8b405057523acad0165080b1b5458c142ba90d60292b0141574a72ba0ad5d046ae13400499ab4919536bca9a5e55daa2a657d546d8aa25c54cab8024bd514a8a4b5f53d36292d5d4d28ca4a5e52d2aa925794926c0092b511a4288d1144488a21443ea2da7ed213f6889fa444fca21f514cfa6be9d3494e922a74514fa6bc9bc6c4dd261f4d6d348c09a0603e9aba61141304b8980504ba3225c0a0fa6a693c5949e28a4e939270549424049c131f4d48fa69e9235e3e9a71f4d0d1f8a48fa5e47d269f4d091d2a87d25f4592ca2c9451647c8b232458a522c518fa4bc89b5044cb61f495d104bc8823e3e92921c950fa2be82a5941528a0a8f9054648295e414a920a5290528c7d15e409a82049b0fa2ae7ea5e3f5291fa578fd27c7d1523e81d9f40cc0124e7c1443a9279d492cf36a07995c3cc281d491cf0680780403b9aa1dc0a0ea486760243a8159d408ce54687394939ca09cc490e52bc009232ada79c40d0ab6966ed603752e1ba940dd0b855b473651c1b28d0d906855b432ad279ac090ab49668d60345ae1a2d40d10b855a473352619a910cd04855a4332c1a1568fcc904855a3b31a3018c130ab46e6134430d1a184090ab4665fa352fc9a956138b669c5b3422d927174490b64845b13d2d89696c494ab06c5624e2b1211588e8ac46c5614e2bc9a158508ac274561362ac1300212c6a69e540341a9a5947580a34b851a5028c2e0d4d1c9f4704fa3427c1a0d4d0c6a49e4e0241a92592f580976b84bb5025c2e0d491c9349849a4424c120d490c910683523f23c120d48ec8c8c04604c1a91b9140f088688440241a91990c5308346a4224c20c9a8d41387969c401241e5a10f29287d2803ca461e49e8f24a479242350361ad270ec4d06b48435a3a1cda00d68d86b294382401aca30d64f86d460362341ac990d4098010862cb4b165a18cc1145929e3205d164a38c45145909e3015d164238b49785d2682d252168af0b41785902e0083e15c0e0020ec548a02a04c1311b8a24f45124a260361351d09a8d84d26c2602600419850d382868623a3711c9b850d084528a1424f10d2285053c4169019c520fda4066d783c8a01e0240cda9066d043949c19b400dd18066978354601995e0cc1e85049c2f27a183400bc9285009c29474163500a51b054d002926c140170041902e93c244881202405d2182e8ec1746e1013505c27030938184840c14e06c9a030508182740c13605c130020ac1504c00823011a78228d011068023430111f8088dc0d46a0204e015a700ad080549c041240152100a4b40524a020360040d8040d8010260001f 10 11
def ch_84 := dN 0xffff0000ffff0000 g_84 ep_84 2 3 bds_84 538 (dT 0xffff0000ffff0000 [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000] 8 f_84) cur_84 nh_84
set_option maxHeartbeats 0 in
theorem rc_84 : dR 0xffff0000ffff0000 g_84 ep_84 2 3 538 bds_84 (dT 0xffff0000ffff0000 [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000] 8 f_84) (cur_84 0) (nh_84 0) [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000] 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_0 : tB 0 32 ch_84 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_1 : tB 32 64 ch_84 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_2 : tB 64 96 ch_84 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_3 : tB 96 128 ch_84 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_4 : tB 128 160 ch_84 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_5 : tB 160 192 ch_84 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_6 : tB 192 224 ch_84 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_7 : tB 224 256 ch_84 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_8 : tB 256 288 ch_84 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_9 : tB 288 320 ch_84 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_10 : tB 320 352 ch_84 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_11 : tB 352 384 ch_84 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_12 : tB 384 416 ch_84 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_13 : tB 416 448 ch_84 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_14 : tB 448 480 ch_84 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_15 : tB 480 512 ch_84 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_16 : tB 512 538 ch_84 = true := by decide +kernel
theorem nj_84_1 : ∀ i, 0 ≤ i → i < 64 → ch_84 i = true := bJ (fun _ h1 h2 => tA nb_84_0 h1 h2) (fun _ h1 h2 => tA nb_84_1 h1 h2)
theorem nj_84_2 : ∀ i, 0 ≤ i → i < 96 → ch_84 i = true := bJ nj_84_1 (fun _ h1 h2 => tA nb_84_2 h1 h2)
theorem nj_84_3 : ∀ i, 0 ≤ i → i < 128 → ch_84 i = true := bJ nj_84_2 (fun _ h1 h2 => tA nb_84_3 h1 h2)
theorem nj_84_4 : ∀ i, 0 ≤ i → i < 160 → ch_84 i = true := bJ nj_84_3 (fun _ h1 h2 => tA nb_84_4 h1 h2)
theorem nj_84_5 : ∀ i, 0 ≤ i → i < 192 → ch_84 i = true := bJ nj_84_4 (fun _ h1 h2 => tA nb_84_5 h1 h2)
theorem nj_84_6 : ∀ i, 0 ≤ i → i < 224 → ch_84 i = true := bJ nj_84_5 (fun _ h1 h2 => tA nb_84_6 h1 h2)
theorem nj_84_7 : ∀ i, 0 ≤ i → i < 256 → ch_84 i = true := bJ nj_84_6 (fun _ h1 h2 => tA nb_84_7 h1 h2)
theorem nj_84_8 : ∀ i, 0 ≤ i → i < 288 → ch_84 i = true := bJ nj_84_7 (fun _ h1 h2 => tA nb_84_8 h1 h2)
theorem nj_84_9 : ∀ i, 0 ≤ i → i < 320 → ch_84 i = true := bJ nj_84_8 (fun _ h1 h2 => tA nb_84_9 h1 h2)
theorem nj_84_10 : ∀ i, 0 ≤ i → i < 352 → ch_84 i = true := bJ nj_84_9 (fun _ h1 h2 => tA nb_84_10 h1 h2)
theorem nj_84_11 : ∀ i, 0 ≤ i → i < 384 → ch_84 i = true := bJ nj_84_10 (fun _ h1 h2 => tA nb_84_11 h1 h2)
theorem nj_84_12 : ∀ i, 0 ≤ i → i < 416 → ch_84 i = true := bJ nj_84_11 (fun _ h1 h2 => tA nb_84_12 h1 h2)
theorem nj_84_13 : ∀ i, 0 ≤ i → i < 448 → ch_84 i = true := bJ nj_84_12 (fun _ h1 h2 => tA nb_84_13 h1 h2)
theorem nj_84_14 : ∀ i, 0 ≤ i → i < 480 → ch_84 i = true := bJ nj_84_13 (fun _ h1 h2 => tA nb_84_14 h1 h2)
theorem nj_84_15 : ∀ i, 0 ≤ i → i < 512 → ch_84 i = true := bJ nj_84_14 (fun _ h1 h2 => tA nb_84_15 h1 h2)
theorem nj_84_16 : ∀ i, 0 ≤ i → i < 538 → ch_84 i = true := bJ nj_84_15 (fun _ h1 h2 => tA nb_84_16 h1 h2)
theorem nc_84 : ∀ i, 0 ≤ i → i < 538 → ch_84 i = true := nj_84_16
theorem lb_84 : LowerBin 0xffff0000ffff0000 [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000] g_84 9 :=
  lowerDagV5 (kn_cons lb_15 (kn_cons lb_22 (kn_cons lb_28 (kn_cons lb_33 (kn_cons lb_37 (kn_cons lb_4 (kn_cons lb_38 (kn_cons lb_3 (kn_cons lb_7 (kn_cons lb_66 (kn_cons lb_65 (kn_cons lb_67 (kn_cons lb_68 (kn_nil)))))))))))))) rc_84 nc_84 (by decide +kernel)
def m_85 := 0xffffffff
def s_85 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_85 := 0x13371f7f
def ep_85 := 0xc4800000000002400600000000002040e0800000000133210200000000010041040
def bds_85 : BList := [(m_16,s_16,5,g_16),(m_23,s_23,5,g_23),(m_29,s_29,5,g_29),(m_34,s_34,5,g_34),(m_0,s_0,4,g_0),(m_36,s_36,5,g_36),(m_37,s_37,6,g_37),(m_8,s_8,4,g_8),(m_9,s_9,4,g_9),(m_69,s_69,5,g_69),(m_71,s_71,5,g_71),(m_72,s_72,5,g_72),(m_70,s_70,5,g_70)]
def cc_85_0 : Nat → LPN := uC 0xcf031c8c7031c0c7030c4c303042c103040bf0af81bc0af00bc02ec1bb02ec0b51ad40b406c82b202c41b102b44ad02b40ad02b40a912a40a902a40a902a01a802a00a802a00a02244f90064008e0a3808e023808b0e2c08b022c08a061458502140840610083060c07b21ec07a05e807a01e417511d407501cc27301c427101c016c11a826a01a41690194465018c2620588062018805f0d7c05e057805e016455901601580160057055c0560558055054c253014c052052883b3ce423804e00350cd013304cc03300c813200c803200b062c00b002a0890624008c10188001 0x104d74806aa3e34d1fda28ec564712a23f149164a08f91787b8a42c1491e8a08f09505f2503b36c1d49a0e0540734d8379501c12e0e2db06f4c82f2381b8a20b24e06d26835a441751c0b04e05c2503456819eb00cc9705b2503216c18cb20c4510612682e45017d2f0bc9485d4942da46168af0b2548582942b94623a2f91916c888ae41c531f52f0f2918772be3a15b1c8ab8d854c6a29e3494b194a38c050c562521fb50121b00a6d20516c02816c13cb008e940466c026b48131220965204a28823944114a0091164468a21fa4a11123076574352aa21929064908825203e2b82025e0fd2907a4a4182421db600e9ac044900382980e1200d9b006ad40332a0109300c89e0384c0322a819a640c4a60325003026817348080980305002bad0155600a5a803e4c01e4801396c098b204a530242680e14007d2a0364d01b2880e254068a202f140224b410a560812703c9081d2bc0c952060a502c518548be2945b13a2b89314c426a41e34a0e4af86e56c342ae179530b4a785852c2828e119430549881a5b0062b80625c049300225b00b2b804a6c021360185400d6ba05b55019a6814d14092b20415101a2f00b148138be0845703d2d81c94c072bc0214600929432d3e1669701b477e9a1bd493de6496f1a4777521bb68fdd5476e5a3771519b7c53db9296db9475c4a1adc4fd63276a29374f099a704bd092567e127390919a613cd108e6803f2f81d1660dc8f06c2a82f0501380607c0102e0001f 14 16383 6 63 11 2047 21 2097151
def cc_85_1 : Nat → LPN := uC 0xa34a309d69b29a19a09649609339309039009008f18f08f08f08f08788708708708438408408227a87a07827717617607607607067007006e26d16d06d06c16936366306216116105e35e05d15d05d05d05d05c15845805805805535505415404c84c04934904904904454404404404133e33e03b33b03833803803803803533413313303123103103103103102c52c02c02a21fb1f01e11e01e01d11a31a01911901901811530d80b20b00a10a00a0091054050050050050014010010001000 0x80a5d8025573a3d7f93d843528325f8125772a3d7f1527e83c7996c7595c7915c7d2607c96c7895c749447ba447796c769247aa447716c7393c7915079b5d78b5575b4d783457795977151769496083a75c5e7545274b5673a527315e7dc5f7c4577b25b7a2537615e741467292e6004a6d159719516f9586f2586fa5e6f2526da4a6aa466d14a6e9466da586d1586b1586b4506c4606bc586a958713457095f701536e1496c93b6a137691515f834649516794961941669296403c64b5d62a3a6193a6393662a526215e619526095e6724f6624365a3b65237631436112b601235f8365d9515e9395a9315dd605ba505d15c5a9505c9445ba525b15e5a9525e4525c1535a14154851590294b82154051580494884156343530435583351844510345384c4f02451a415114d5093d4d8224a81a4fa404f13454c515425d532354d1424a12a5284e4b84252035500344882a4e8264d9344c0244d1524c85e4b8524a834490344a1524985e4885258b435794f5712d56927551254e0434b0334801b4126c3e25c46a4440a5c45a6c4025c4516c4496043b4443244429484214440950 12 4095 4 15 11 2047 20 1048575
def cc_85_2 : Nat → LPN := uC 0xe00ef0b781ba1dd06e07685a86d406987407a00cf0d8fac41620ad25682b41543aa05502a05500a8054029093889a14d0254b281930c9824071c28e0468634118188243861c0fc97d0be81f40f81791bc05e00f007803b85cc8e60720b429984c826403109880c406013001610b005802c01546a43510a8813869a14b125812c092247123051808c0450a28114076a3b01c88e407203901b88dc06833401984cc06603209900c8064032014a4a404e226090188003e11f00f047803c01c104501840c004102001000800020000000000 0xbf944c0254bf134bd124bd144bda54bc934c2364c0a447716cbe954be13cbc014bb15cbab640416c6f13cb9b64db35fd9b5dd8b55d7b53d534bd2b47d1a5496a3b93a3a7f2367a233d114bb214ad0947ce946cc93fca13b8893ac7137c3136bb9337005f6304a5c0474e0463603f178370702fba01fb9017b8235b78343502f16827b6a58b3960b6158b5238b4938b3b5d9323ab3145b2936b5b5fb435392a3ab21528793a6c85f3483f160373402f15827a925da6a51b0a359212a6c05da813891938ada3091128ae84cad244ac024ad234ac234adb44aca54a5128ab8246b138afa3faf23bae237ab2339092aaa83faa0373382f15027a8158a8450a9460a8c58a7958a5128a5450a6d60a625ca5a44a4928a3b5eb1458b0452a9c50a725fa4253a324d8f92a6a05f3282f140273202f138273182f130273102d12025a002f9f827a215ca1954a113ca09369f1343003f118379e8149da5e9d25c9ca54932508e16c8615c8da5c9b2609a96c8d15c9626095a508c15c73c5e981458ba6c7393c8b26c4a8349635d95b558f25d8a2559314a951469493d941356284a4a046872459315291a3a912369245290c509014d8f2608d9508e35d8d3558634d8cb458c2558b9598b1516203a498368a2507316c490347315e89146829367692e6184a488468815e872488645e85c529bc5f9a45799b5f9935798b4797a5e9725b96a5393a5292a4a8fa468e95f8a95e89957889528794a86947851466104a480468235582a36809608395882b60823508196080150 13 8191 5 31 11 2047 20 1048575
def cc_85_3 : Nat → LPN := uC 0x820a042800a0007c21ec27b01ec07b01ec07a09e237881e017801dc27685da07225c4267519c067019c0658d922648186660898205f0d7c05b215c8570156355815035401500528d40550013e14f053c04d8d3604d053404b8d16c4581160458116045810c5430108242010234080fe23ba0ee03a88e62380cd083384c643104c403100b0a2c00a842a00a232880a202880a2026149802600961258088721087291c046c21a846811a005a716805a016044e513804c112844a0109042010803c30f003a10c143000c003000b842e00b802c105ac16003900a202800240004000 0x20005eff8272141789609c8403e250178091c4028d5fe468fe9387f09a3f60d08305e248277c9ab2ce505f625afa9257e22ebee545f42a0f935c5b0acbe0545b54c0e225e655292da9294f48c83a365b0a53da518cf094580463b62e368581f96baf9b5574da6be2d1def68ae7a3770cafb78565b62a6d99517b8a5bd8525eb28e889415ac9da9c4dd33256831273381d15e0d9e9252f412879c922068d90526cf125d794a8b6250532256811277902e360544ed292b4949784a0a964d5c24bcbe2525a925292918e62bcb494a77ca319a129e24bcf0246704afb5e54d68296a414777894998129d846a570447701a35c545da292d61416b5293ae579ac2a4eca5e7612335454dd62526584a750a4958111a92a2e893969898956111a84a4e695e698a93a7179d28a6e845273d2fb4a54d0f292e7143730a0a624acca074568362a81a394971c94a8e412871c9238c091b0ad8e2148701aa1cc951c22507345170121375179c34bee0a536fd22a5e4a8e10be3b82f0e413b7a559b025c769313dc90b60d74e7474829366f1aea5c8ecf6466dd9366e8970e80fc3706e0782f690a8370975a32803902f0d013b2a961b54b4da2564b11d2028d967294d01466709eb264d4c9094540466c1aea568e90046cd915d6c1b62f88e18c288d736c6b51c316511ac270d593429c1a353581a84a0d395c698a833c5118a2685304466c96b24495a449acd12f65c95b2249d842463782f0cc13aea07d7302eb3254598a4148110a206850844599a73409759f49acf2354a8951720d4a0068cdb5c6723633499129490cb1484149a33057182268cbb646592622c5b195278c925c60c903200f1902a8c9b6c645322508e181260c784c2781a3101118d694c625262d25314918f52426384a274233120f9870643702d0c012b068d1852b8c01445ec0a2fe4d17a028c1a545f8a23044f179028bf924 14 16383 5 31 11 2047 21 2097151
def cc_85_4 : Nat → LPN := uC 0x2f8bc2f0ad2b0a8682a023588611841e3709c06c5b068564545503242a0800200000 0x7e65d74e4d591414dd2b3ed232382f1502704c1f8623585c342302f14827855592281f140177df5d4da3a3ea32849360482d7db5c46d5c7d65c831208383c82d348241482d2482524832343c95c82944820140315c7d24d8412f83d2b8352781d232242f13c278181f814178525d7ce4d84d5c84551811504d12b3e1232202f138270401f21c2d13025 10 1023 4 15 10 1023 20 1048575
def cur_85 : Nat → LPN := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_85_4 (Nat.sub p 512)) (cc_85_3 (Nat.sub p 384)) (Nat.blt p 512)) (cc_85_2 (Nat.sub p 256)) (Nat.blt p 384)) (cc_85_1 (Nat.sub p 128)) (Nat.blt p 256)) (cc_85_0 p) (Nat.blt p 128)
def hc_85_0 : Nat → Nat := uH 0x65a13c0000196203cae01e1a1e8000018202400000000002fd43600000be5085ec830000017a208bcc02de4012ea04174e01b8d0d5b389ad8c096b8070000059c88ecd40966204b2d0259301ec184000000b000357d01800000000000000057c0080000000000aa32acb74d655c2e0000093a0ec9b0124c80925c0491d08c8b01e42c1720e049030247088a374091b2048c7090000022e81b162098552e00000213410000000000042500df78d8fac087d2023de855ee408f461600000000001e4026f100800000000001dfc12ec61c76200ba187dcb02ee500472402390011c282ce0c046ff03b7c01dba81cd8a256bc04800001ae008d68046a40834d825a5c08000000000034602c000000000068404312181406469d0194e402000001330309542248910a420140000000000000002400111f00881a6f0000020500ce150a4416519c420145d00005000000 0x425108102319ce70e24eb6122442118ce93a4ae72e939ce109d2c2179a4eff107c9d3a5f85fff2ec210bdd2c4fc9dfe61585ee97ef8c2f33a5ffff7fc425f93bcf6840a210842149ce738ce3421084210842040842442109108421084210846109ce739d273a4e738427788421084e739ce74bdca77f83893bffffdc1ff7cffff8b9149dfdfef77f79bdded39ca4a418ce749c210811337460e73292633a4e738421091497bff38dfffe61c7f006fff97f385f276e7cd277fd9ceffffe31bfff7fd99ffccb917c9deeeffeeff77e42effa0514a4273a4e109ce11846e73870e72e739ce85a1685a139d2719ce719c2d684e739ce749ce70842109ce109dee739de394efff3038ff1c48f93b04877c9dffee72eb5e16844896b4e71831273a579da1189932b5b563494c65d2739ce918d6b6b5ad5b5ab18c6b1ac6d68dad39c38739cb9ce72e139ced384e939ce739ce939ce739ce748c67798ce718c6b5b5a31b46319b5917b420c61ce939c38b5ad6d6b5ab5ad6318c18319358c632611b4631846318c6318c6368c6318c6739ce73a4e739ce738c6718c6318cef94a5294a52 21 2097151 9 511
def hc_85_1 : Nat → Nat := uH 0xc5c1bafccd2b2ce36c8019b1983400000b0c86ac2a04afe066bf004aee072bae05000002ba604000002b9e04ae581000000ab916400000aad85ea9a0ea6520e9880600000289a7798351e60a019431fe4b82a91b89646604917810000008e01be374060000023401a8ca03000000000000000008bd06a06f437e19d1d9af66ea3e4000006b41b00000068816193c726129e58320c000001828055cc1f1724060000000000058e9d40000055f9794409f4cc22000000489a15204114808051cc1b45a0c914e0d00000112c11404238d0984000000c0482000000b0480274a648aa9422502c8780e1b7b346c40d1ab0300000019f85c670071958346500319280c000001719085b40916b0105980a12c1d0000001280200000000000048a0b0dea20000000db8180000000000036c01096a241369203c08c0000002e86c0000002c8100aa0401c0740680401681c0520401281000a200000140000000000000000 0x2d630185b58c635ac610ad6319ceb5ad6739ce739ceb3b42d0ac2b09c2708c6318c6318463184630ad6b58c63060c64d6318c885615ad6118c6318c631ac6318421084630846fd4b52b4ad6b48c6718c6318d290a5a11b46318dfe0942e3e79bc043fe61008fde23c02ffffc251081020f085ad3a4e96bc4b275fff610912210936d6b084237ba4e95ad6d6bcd63085e610793b2230856b68ce93a56b084210842118c6b1ac21084211bc420408424421091084216a5a95a5ad484210b46348421484e10b224e7295a118b4a31892820e939ce74b8d2379be4ec6919df277f6b5ad4824a27d09ce939d2738306f77bacefc6fc671bffa4e5029ce72e73ad06b4e7384ed384ad6940e339c67394ad6b5a077839c039d2739ce739ce939ce768052b5a0054a44fa1049ce738ce35000801a000468014a528300000a5295ad6b40e00077b9d2739ce739ce739d555222aaa5294aba5513a55294a5556c996d6b59ce7395deaaae739ce739ce84a529520bc1028c694a5294952805ea12252023095214a4294be2540244a2b0ac61321485290a814254a544be6b1ad6b4a4e132d4a585f2aa30194b631952910825254a5294a52f2d6b08de61036b263085694a5294a50846f0122b221585690a521739ce555ca94a539ce72ae95294a739ce55b5ad6a54a94b6529b59b5a5294a5294a5294a52a539c4a42b5e1684a319c0ef9390728e96f33bf257cbe8ce732f749d2f07485e6d6b5b40ca489f4273a4e749c633bd319ca6e73870e52a5ce9694ad3b4e139ce13ad6b4d94a719ce719cdacdb56d39ce939ce92aae93a4aef739d2739d2739d2739d2e077a94e939c04a4ab4ed2b5a1684a31a139ced3b4a529532902f041ad2b4a31b94e52aba54250b4270974a5295673acaa2b58540a149d252a44c952975a544be6b1acdacdada87b09d46e53b42949da9684a5284aeb4270b5652ac67673b42b6ad61671b0be9563149a326db2a5251980ca556b7cbf93a59494a3019565b18ce72a54a4420e0c85d276adab19ce37dad6d018cca48b5a139de652d6adab39d6b08de61069ced36b263085ca7295329494ad69ced3a6ca559ce6d66d6d782509d2ff0449dfffe021d2ffbfffe244c9dff 22 4194303 9 511
def hc_85_2 : Nat → Nat := uH 0x2f3a02bcb81af260400000000000bc880af0011bbc022ee008bb083eeb009ba483ecd2e0afe9b2ac49ba343ea8c40600000288022a1d01800000a0f0728240ca0203a7f6099c91a64b3398ee1f63941289229a23c068888340000088482220a04000000000000000000000087e8221f00587a0120a8a082482c000000000000000081507e02a1500000200811000002000047f1078000007be995c77426d5245a8a6565526d83c8c60d01181e0b5b8a795ac9b4ea409256a9427b70f6c9931c5f8c2e21308818000002fa870b9e262d20acaec2e2b980ca4e4c2830849b82a26a02099c062608340000025e8108da50232024806611fb830000000000007b41d1eb0107144c0000006e6171b701400000000000000001b28246c2041ae01461e4d0000005fa120000005a42b000000512491400244cc1a0000004c6031031741c52403e1980e6090248a80800901e010070040060b000c0600200800004 0x5e7d2bd2ffff949df293a545855814a31800c6558ca518c63194a91080092a52948c693a5274a5e052aa94aa6518461298ce93a4b55ce7395554a52955ce738c631954c6318c631aaaa445554a52955512a6318c6529bd554c6318ca92a4aaaab292b9652318c6f7d46f3d63f7fcc2b0b0bebcfe955180ca5b2aca11894a529d274a952a536b26528cab29bcc65358d6b5aca1458c635856b5ac2564a932b5acca5631a5674a5674a5529004c6400c63199294a40252318c6de74a952630a50a57842306b0c632a0650d25494a749d2f7ecda5f65ffdacb6b2a632a6b318c6318c6656b5994a52318c6bcd8def51bfcf98de2ffff1184f9bc9d9b198c89118d6b3a4e94a58c60c60c652a4c6b2946308c6309b5931946319553194de6318c692a46718c631a4cad6b32918c63555294a55328ca55358d65495255594ac634aa8002aa9ac6b002aaca5631a5544210954ca3295442109525495544210ac634bc0a555294a5555294462b19cd65749d294bf3fd55294a5532946529554ce6b2a4a92aaca5631a5554a52954ca32954d6359ce739555ce739c633aaa94a52a994a3294aaa6f358d654a22aaa25555b2a92a4aab2958c692aca4ae5856b5ad66c8842102046318c60c085a96a4e93a56b5ad6b084210842118c6318c6308421085a96a5695ad690842118c63421094200318c610842005494a54842108c631ad6b58421084210ac21084081084244215848842318c6318c6108de21084211b52d4ad2b5ad2108421085213842318c6fb1bc751f9e6b7839ee6ff060f799fcc1e352f33fa665336b6b58d61080ca6319d6b7f827f0231bcc09c11ebcf379ff6b00a6318c2f1021039de2dbd31ac630adf612212dace7785d2cc6b5bf18c6b084065319c6b5b0bdfc7fe5fef797c60c0205293a4e96178fe4df79d274b180ec763b1dace93a5e68de9b9ae664cd8d122b58c6749d2b5ad610ac2118c6b1ac211bcc6109c1ecbba63184216a5a95a5a90a5a16b4636a4ee94b4e94ad6f18cdac9e0c61022d6749d2f978c1ef37ea5d2ffc008c2d4b52bef 22 4194303 9 511
def hc_85_3 : Nat → Nat := uH 0x84b91b0579fe02246bf32897aa5e0f2517de46023c6c10000000000001e1c0d3bd03477880cee6855dcc00bae858756834000001d0f25b9fe106fea0adb3251aca4e34629964e9eec7315184d4cae95035bacbeb6a05d6553f80000057f0b2a6bc9543c4da677010000009619e125338000000473d08843d2000000207a4a40a02a000000faf3c9f16243db83a000000eec411b7d2e348d3665c1acc1d4d96fc9f2b71444eac1c9d1021352282694084c586898702120c811f12840000007861f0e3e671adcd02eab885693608eef211285a22380c0000007e4550fb8081cc15838c0606d0240d70181ab018355008698090c9050188050302070000000bd01c1670982ab118450830830380f40901d90780000006e44008a2940000000000004181c07a8440ed0401ca0803840806d01c0d00501980400000005e83c0b90200000002783604a8240910200000002081e03e8140000000f2040098a600f0200100700100800100800000000002000000 0x505f0285542855956d6b5941255594ad2b4a0a814aaa052a5ad6b2824aab295a5695053060c615502954c6319412555318c694a0b81c2aaa052ab9ce72814aae739d6b5ad401f5480a052aaa89554285595556ca65b5ad650495555652572ca5695a510954fa00a17a846329ce52bf1afe81ad4aa5040018ce14af213f798119a94220a3319d27494aff7811b8804a2017bd293a4e95e6f4212815e53e405e02100a1083c63794a10b5a0d4bce94b4e94952d4852d0b52d4a0014a528421080152910842052b52d49d274a0010842005294a10842005494a5484210b52d4a1084a10018c6308421002a4a52a4210846318d780084212840080a00400294a5084210001800152529521084202438352d4a94e00a948bc20529d274b9ce729c00e138400a1284e739c00a52942d6854002280000005ea1294a106000005294a1081c001291a005494a54852d0b52d4a506a90f04018ded0e93a4a578264ec14a50842017a20846329d27494a56b508420f28210216b5a749d2a05084002f108421084884212002942108421084610b41254b5a9084210842909c216a5a955739ce5555094255709c25294a55739ce15ac2aaa9115550942517aaaa94a52aab64ca2b584a92a4aaba556525728a5a15a56942528c500bc102505463694e93a4a560a12252a25f319ac2b3a4e92bad5ad610bcc204eca244232215adab3a4e952a44210942517884a21020421095b294dac8842158421084610b5254996b4884210842909c216a569519a80d4631ba4e929598af1a5198211e057a0a514634a4a53a4e978c14fcfd799d8c26d6b19ec6f04424465b2233b5a52749d2d418a5488421294a12aa2128beca558c6666d6456b585a92a5a74a46e949d4b5a452d0b52b4aa884212aa94a52a884212a4a92aa884215a5695550055108420055510842b4ad2aa21084aaa5294aa21084a92a4aaa21085695a55442109554c631954421095254955442108c631aa884212a89739ce555108425294a5510842739ceaa21084aaa2f54a22aaa254a529544210956ca655495255510842559495cb695a5f7846f17bcdf1842f37f8b26dac637ad60408c6319d274ad694b19560b28c6326b190318c23184ab59406f03180318c6328c6318c12318d2338c654ad6b4a52318c6a0632940a102943aa3414a005285e13a94e93a52950600328c1952917840a53a4e95000a529406f0032946528c6004050020000015252952948c690121c141aa400031846128c633a4e929540022800000400a529406000318ca318c6318c38009002a4a52a52918c6378063085e17b50318ca518423085e2073be2946005285284200529cec2ff0c2178c2c2ff3d2af156308429bcdef71264eaf51ac668a85da94a54005294a0bf5294a52801525295294a52a328b29d65228ca8f31fe257abed84358ca54fa9423128c06528a81b2afb3a4e9294ab3ff0185fffffe3c2fb3e5f80c2f4ba5fe7de5d80c9bef78408773a4e94bffd52ffff 23 8388607 9 511
def hc_85_4 : Nat → Nat := uH 0xae31ba2c5b95e677c6cc000007225262a7c6100d4f48e4e00a4d406000004c00a4b804000000000000000000004ac064a40449c043ca69236ca1248901a850120400009 0xa83e0a02814a5284a5284a94aac0a528ca528ca54a6d650494e9494e9499294a65295a500154140b19cd6b595d274aaa802ab9ce7002ab9ce75ad6b7c00010015401000059540b060b5ad600555009481c1295a5696a9005198cee93a4a54a5932006318c00a9498c6300325294ca5dd281ac0054a6d60c002a5227102952b49d274acff312fcbfe002a525802a5200c94a53294a54000f800080054a40c0005801529b58700120064a52994a5694110095140a551084250495544210ad2b4a982853c0a555558ce6b5ad6b2ba4e94a5fef 20 1048575 9 511
def nh_85 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_85_4 (Nat.sub p 512)) (hc_85_3 (Nat.sub p 384)) (Nat.blt p 512)) (hc_85_2 (Nat.sub p 256)) (Nat.blt p 384)) (hc_85_1 (Nat.sub p 128)) (Nat.blt p 256)) (hc_85_0 p) (Nat.blt p 128)
def f_85 := uF 0x169f0ba3585c1a002d2e152b30225d810ae4244da042a30292f81495c1c0f20524f0423482c92410512092490401481491c0a07e0502f02150005a3bf68e1fb46aff82f7fc13bf68d1fb270fd9347ec1a002d0deb6bafa45d7d0a8bea4b5f524afa1507adaabe4d71eb68ef81517ada2bd652ded28cf59497aca380293de7252f392879c9200292de42a2f205c00523bbc979e1282ef24677ca33bc4a401486ee0340051fbb4525d64bceb24675caf3ac4a401476ea1497322f39914dd1272e64527312fb9850dcd2bce61410051bb8c971c64a8e31287189238c09001466e21486fd2fb844a1bf4a6e02426fd2280253dbd2acdd35d6e89b3744b801296dc25d004a3ae4d7db44b4da2565c9aeb64575726aad836c5c9a9b56db1ab470d59386ac9a2e4d2da6ac0d3250698ae34c5417268ed224d5c92a2e452d7228ecf25d67926b3c8d57228ccd46c66dae3349917227ecc15c655b232a93195278b913b63db63249718f4c8c815463c262e44dd87694c3a5261d2530e9198707cc404461c192e44d9852b8bc3646092a3044f178488bf2545fca22fc4d1782a8bc13c5e52a2f451179268bc0145c899aec571756c8b901f5cdb22e405c01286b7a355bc1a0024fd6c4b0b6158591afad28e169270b2353595aeaca5156526cb21520049da8d1616146aa34525511faa88ed5d098aa23755da22b48d1574a8ac23455c122a88cd5407eaa03751a2829f1814f8b0a845053cac28c97d49ac0a4a5c5252229514149250a325351daf28c9340126e9e95c4f4aa27a4f13d26c9f82f4fc13a7a4d13d028009334e52f272971394a80092f42a2fa6a981352d885457429afa14d5d0a68e981454292f21496d0a4a69435d4a1aaa505192827a941354292924c5490a494904524891d2448d9208a09014d4292323c9810a2be8b35d46ca822cd551668a8b255458aca2c5450a2bc8a250428aba245190a2a48815e428a521c9210a28e85c5e42e29214518012567eb5241cac1fa97d036c081b5040cb01fa95cff4ba7fa553fc9e9fa548fd078009273962f9f2980f92d872c573dd221ca96cf548872a533b5ae9e4540ed6aa76b453b4ac9da544ed2927295e3a62f1d3148e96ac72946399291cc578e525c0092338ca89a8d14d42be6a1533752f1ba948dd28c6a1493692c1b4560d42766ac603562c1ad140d52b06a137004279a45440108e0083f33ca497e93ccd2525fa432fd1d97e8dcc76ba6403c31c9b17e50cc34a46195e30ca917e4acc12bc5f9232fc1b0020e8bd2725a4522e6b0172570b92885a1532d52916a578b52a45a1410041b9640a49068658049240a79204b49024e55b432ac199204949d8a24ea5d29c2613a8d49d09c4e83528520942534a127a4e8342792013c4d09d04c4804326c9a12e548970bc4c02425c291200cc95068489522442f1240d0910a44801b0041b0ad17c8d4882b45b225361125b0892c02b457211a2108910842904214415a298fcd74812a03f3551f9a28fc524564bc3d45e1ea290f45045648c3c254158af8eadb0752682b15b1cd360ac55c6d6d83825c1b5320da5106d2682b1531ad220ac53c562963356819ab00cc9705628e3096c184b20c2510612682b14315d2f0ae948574942e45015d230ae578572a42b94a15ca30ac4a40105e0ac5f14da402b16c4f6c02796c13cb002b15c4a69025244128a4094510158a621c5911ca20871444528021a4610c9482ad48412901ea5e0f52907c5703d2520ab4a0e9b0074d60152be1c14c054ad86ad80356a00a9570c1320645503029818134054a985cd201529e0a94b0a6b4053580296a00a947090b60485902429812134054a182c968164ac0b24e07d2a02c908162bc0d25406ca2034510162a40b14a05e2802c51815262008270122f822980112d8024570112d80894c086ba06150021aa810d14082b204151010af00b178058a4021460040f8049480102e0001f 10 11
def ch_85 := dN 0xffffffff g_85 ep_85 2 3 bds_85 538 (dT 0xffffffff [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff] 8 f_85) cur_85 nh_85
set_option maxHeartbeats 0 in
theorem rc_85 : dR 0xffffffff g_85 ep_85 2 3 538 bds_85 (dT 0xffffffff [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff] 8 f_85) (cur_85 0) (nh_85 0) [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff] 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_85_0 : tB 0 32 ch_85 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_85_1 : tB 32 64 ch_85 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_85_2 : tB 64 96 ch_85 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_85_3 : tB 96 128 ch_85 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_85_4 : tB 128 160 ch_85 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_85_5 : tB 160 192 ch_85 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_85_6 : tB 192 224 ch_85 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_85_7 : tB 224 256 ch_85 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_85_8 : tB 256 288 ch_85 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_85_9 : tB 288 320 ch_85 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_85_10 : tB 320 352 ch_85 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_85_11 : tB 352 384 ch_85 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_85_12 : tB 384 416 ch_85 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_85_13 : tB 416 448 ch_85 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_85_14 : tB 448 480 ch_85 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_85_15 : tB 480 512 ch_85 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_85_16 : tB 512 538 ch_85 = true := by decide +kernel
theorem nj_85_1 : ∀ i, 0 ≤ i → i < 64 → ch_85 i = true := bJ (fun _ h1 h2 => tA nb_85_0 h1 h2) (fun _ h1 h2 => tA nb_85_1 h1 h2)
theorem nj_85_2 : ∀ i, 0 ≤ i → i < 96 → ch_85 i = true := bJ nj_85_1 (fun _ h1 h2 => tA nb_85_2 h1 h2)
theorem nj_85_3 : ∀ i, 0 ≤ i → i < 128 → ch_85 i = true := bJ nj_85_2 (fun _ h1 h2 => tA nb_85_3 h1 h2)
theorem nj_85_4 : ∀ i, 0 ≤ i → i < 160 → ch_85 i = true := bJ nj_85_3 (fun _ h1 h2 => tA nb_85_4 h1 h2)
theorem nj_85_5 : ∀ i, 0 ≤ i → i < 192 → ch_85 i = true := bJ nj_85_4 (fun _ h1 h2 => tA nb_85_5 h1 h2)
theorem nj_85_6 : ∀ i, 0 ≤ i → i < 224 → ch_85 i = true := bJ nj_85_5 (fun _ h1 h2 => tA nb_85_6 h1 h2)
theorem nj_85_7 : ∀ i, 0 ≤ i → i < 256 → ch_85 i = true := bJ nj_85_6 (fun _ h1 h2 => tA nb_85_7 h1 h2)
theorem nj_85_8 : ∀ i, 0 ≤ i → i < 288 → ch_85 i = true := bJ nj_85_7 (fun _ h1 h2 => tA nb_85_8 h1 h2)
theorem nj_85_9 : ∀ i, 0 ≤ i → i < 320 → ch_85 i = true := bJ nj_85_8 (fun _ h1 h2 => tA nb_85_9 h1 h2)
theorem nj_85_10 : ∀ i, 0 ≤ i → i < 352 → ch_85 i = true := bJ nj_85_9 (fun _ h1 h2 => tA nb_85_10 h1 h2)
theorem nj_85_11 : ∀ i, 0 ≤ i → i < 384 → ch_85 i = true := bJ nj_85_10 (fun _ h1 h2 => tA nb_85_11 h1 h2)
theorem nj_85_12 : ∀ i, 0 ≤ i → i < 416 → ch_85 i = true := bJ nj_85_11 (fun _ h1 h2 => tA nb_85_12 h1 h2)
theorem nj_85_13 : ∀ i, 0 ≤ i → i < 448 → ch_85 i = true := bJ nj_85_12 (fun _ h1 h2 => tA nb_85_13 h1 h2)
theorem nj_85_14 : ∀ i, 0 ≤ i → i < 480 → ch_85 i = true := bJ nj_85_13 (fun _ h1 h2 => tA nb_85_14 h1 h2)
theorem nj_85_15 : ∀ i, 0 ≤ i → i < 512 → ch_85 i = true := bJ nj_85_14 (fun _ h1 h2 => tA nb_85_15 h1 h2)
theorem nj_85_16 : ∀ i, 0 ≤ i → i < 538 → ch_85 i = true := bJ nj_85_15 (fun _ h1 h2 => tA nb_85_16 h1 h2)
theorem nc_85 : ∀ i, 0 ≤ i → i < 538 → ch_85 i = true := nj_85_16
theorem lb_85 : LowerBin 0xffffffff [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff] g_85 9 :=
  lowerDagV5 (kn_cons lb_16 (kn_cons lb_23 (kn_cons lb_29 (kn_cons lb_34 (kn_cons lb_0 (kn_cons lb_36 (kn_cons lb_37 (kn_cons lb_8 (kn_cons lb_9 (kn_cons lb_69 (kn_cons lb_71 (kn_cons lb_72 (kn_cons lb_70 (kn_nil)))))))))))))) rc_85 nc_85 (by decide +kernel)
def m_86 := 0xffffffff00000000
def s_86 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_86 := 0x115153700000000
def ep_86 := 0x1422000000000014002200000000010404040000000001101032000000000115150400000000
def bds_86 : BList := [(m_17,s_17,5,g_17),(m_24,s_24,5,g_24),(m_30,s_30,6,g_30),(m_35,s_35,5,g_35),(m_2,s_2,4,g_2),(m_38,s_38,5,g_38),(m_31,s_31,5,g_31),(m_3,s_3,4,g_3),(m_5,s_5,4,g_5),(m_74,s_74,5,g_74),(m_73,s_73,5,g_73),(m_75,s_75,5,g_75),(m_76,s_76,5,g_76)]
def cc_86_0 : Nat → LPN := uC 0xe113840df0b7c0df037c0df03685da03680d907487ce13341cd03340cc07300cc03186c507140c016f82bc0ad86b506d01b402c04af06a85aa02a41a902a01a802a00a60a980a602980a602980a50668b970e58196025419502501940250093064c093024c0930224a8902240860e1808602084820204181020018001fc17f01fc07e05f807e01f807e01f807e01d0a7401d00710dc407101c407101b446d01b014e793414b0928149052404511140440510044010c141090404004fc13e04f413d00e443900e403708dc0340cd003304cc02a24a802a00a0227048c40188001 0x3b45d1fda48944f83607c3ec601d9b60929387946c3a94e0d4270f00d8754a03dc511e9a88eed404849c3b15d1d0a70681386a4b01d144138220280406f4a037b5c1c5af0d2d38704bc372521b49a8d80d4622883535c11d2e0d24f0330b80982019128024040634800881019eb00ccd40614801595c1042e01e0400e04006820192280c6d00622980602002c080c2d50464b83014c0c82e0140805a6a02e14416a280b24d0536a02f45e176290b6d78586a42bb49159a0884914552bc2a13d1489a858114242681e0340200800e0804e08824950125280989784b4a42515e120a908e524462821884e0a42108a0e84406c212400fcae0821703f29c1f12e0c0270501083c0681d1440d4a806a940384bc1ba520d8af06854833292191410c4270601082f074170360b120056570270b81494e0a0a104e1382605c121342762f93114c976bc49353229a910ad2c816864025f1f92f0f894c734a43924f1ad270d092c6548e2fa43145210a08fc4f4662694f10ca708051c3d2841d93f0e42785a1382a08e1284208c1f80c0401b0280d1240841a02e490172480fa340789a02c4901d0680d824060a00324a0172480a8340142601c5000d26009450045200184c01009807340035180189100b2780204c024120348ec164660a13f04c9d81e4dc0a2660412f01c918060f8050720203100c0a040d2c1c686031240082742ad3e1269706347815a1c0493a00496fda437c5213ce8edd9466e994f72ca5b6c51d99286c113f5f89daee4dd73266b712f5b091aba13d55096a004744c219e20fced0766e8373501998e0bcc50465a01f2880d84405c010260001f 14 16383 6 63 11 2047 21 2097151
def cc_86_1 : Nat → LPN := uC 0xce067033439a0c44e203085840c206103081802bd1d4d2a41520a90530e981463a20d00a8014009f0cd926c13609b04d826c1341924452228110288042120850408204009e8cf407813b09d80ea1721b901c80e407203885accca66503205900c806213101880c026002f09704b805a12d01680ae35702b053909c04e026093009804a12501204900451a28110288042121010047a33541a80d406a03501814bc25e02f01780a0e48424012009004801f28f807443a01d00e046c23410f587803c01e00f004982020e10510090002000 0x7e8148145e80c528025e7fa527f15e7e1527d9325d81d1d0157ca5d1b04d7a8397a0317b8367b016798148945388b5f87b5e86b528625e85a528515f839538314f829433593d8213b819377d1357c05e790525d01f5301a1c817168167802c7782677024741517193d761357113d71c507094c7014c745606fa5c7395c73014700147235e71b527125e7095e6f952360355c81d1581575c527525e7495f729536f14d6c04d5b81f150176e14414924141346d1246b03434824369351381634a426b1426da4f6ca43129266c04e6b83c6a8266694d6994566a5c659246512464a3468134678146501466b5e663526595e649525b01d120156925e6895f67153641255a81f1181763026622346193460934600345f1361f8155c045360355da44138145ca5c3615c5c14c5b2346134b5fb435ea4e5e14e5d04f5b8475a83f5181559934590345823457834569441f8245595c3685c5284c549345383613816529453693534a421f94e1384e58b4b573435624f552475423f5314e5204e5182650a58502542f2404f9544f05448b50483603da602ea504e2484da444d1444c8443823e2da322613e1c03e3d2604b2384aa344a134498342d25048a48473403c9503c150484513ea513ba503724e2c24247a3a46a362594e461361b84e458362ba5044a384423443934430340d0100c8200c01041a500b8102b25042238412340b0103b260 13 8191 5 31 11 2047 20 1048575
def cc_86_2 : Nat → LPN := uC 0xba3ba0b73b61b60b60ae8a68a42a40a229c69c09a29a09468e68e08d18d08d08b28b08a18a08a08738708708528508508327b87b07a17a07a07827807807447407227207207027007007006c46c06c06b16656606606426406406316125985815805445405135015004d34d04c14c04844714704434404314304304124104013f13e13953903813803803713613513413403043003002e22e02b32b02a12a021917a1701611601421401311030d30a30a0091063051032012001000000000000 0xc0818c0015bf8149b851b183dbe835bc83dbd45eb1c52bca5e36945b105e9b0525581a20816be452bda5ebb14db085f9a053bc04d5501b20017360351f815349426d042bb14eba93c8284f6c8431e825ba015b004db9045b025eb8252af85e998525481a1e016b8a5eaf05f98853b78255401b1d817b6815b5a5cb5024b425cb335c2515cb2834b1c50b104cb025caf82486b41b4a3bb3a333f14db213fb0937af12f7c03eae034ad134ac834adb4bac343ab84eab03ca7249a5a41a923ba8a33a7460a6a6ca396ca2160a1850a5c60a526ca316ca1160a4824a392ba3123a1824a223ba1233aa35ca9b51a8350a7a50a623ba4233a295ca0950930149f9349f0349702c928249e0349682c92024918149d1449c844950248f0149bd609b15c9a85c948248b814999349903494024981359723b96a33918348f04c8b82495a429514e949469413e7b04e93024918347a84c8e1408d930904508fa408d1308f04c8e3408da308d2448c93c7a04c8b82492a3b922339113f9093b8e9378c1338b12f8a9237983e9eb4b9db439c24f9a24798a3f7914e9784e9602c938268a0247c86c8114d88145871353812d801251c0163713d7f9351b8168135c7f1341b05c7e9347e2448494484014188147da4418024369441782417014 12 4095 4 15 11 2047 20 1048575
def cc_86_3 : Nat → LPN := uC 0xf11f883b87d63eb07583ac1d60e81f403947ca0e21ed23681b40d626b035819c8ce067031916efb705b06d816a1b125882c03600a8454029c34e09f4483e4012008e147023430a885042061010808214102080fc47e03e09f00f807a13d01e80f407623b01d80ea1702b801c00dc26e03701b42d626343105880bc45e02d8d6c0b415a02d01604b00532a981482a40510a8053c29c14a22501280902480228d1028803b498a8c406013001708b805a12a1938c9c04a225012809404a0231100c7843a11d00e8074028900a0000000000 0xff82d4a8254a015fe92d4a92549816ff125fe02549017fc137fb83748017fa83d4683546015f993d4693545816fd349fcb43fb341c893ffa1278583ff902745017ec14df8145b584df7845ec25ef6a52eb95eda952f602d440256201d43815b5a5ef5252f492d44125b505e9f8525981a43016f725eeb15fe895be1157d9953f5925b485fad85ba60579e853f40256101f5881b4281710013f304cf214cea94df2945b404df1845f0824eaa5ef0252e815adf956ef82d41025580190f811ee924b425eee252ed92d41125ad05aa48566001e0f012f125eea15fe715bdf157d8953ef125b385fac05ba40579d853ed0255f81f5701b408170e013ec25ceb924eaa5cc9b41eb23bea233c793e3f04d8503f748376882fe9134e8234e7934e8b4be7343e694ee613ce2249e0a41e423be3a33e2460e1a6cde86cdd060dc850e0c60e026cdf924de06cdc060de92bde123dc924dd23bdc233e535ce4b51e3350e2a50e123bdf233dd85cdb850d4814daa34da134d7018d4014d9134d6818d3814d8035d723bd6a33c6a4ed59428404e730466783ed49247e934c624cd0840d0030d2450d1a407014ccf830d0b40d0230c5a4ccf944cf03c65124d423bd3a33c513ed303fd283bd1037ce833ce02fcd823d9b4bd8b43c4a4ed794e8384f728476703fd6018d5015cd014c816cb304dcb045ca0353802dc2825260153703dc203525815c825d2504dc6039c5831c7136c6815c5014229243604422014b335ec3352c2a5ec2252b285e9d0526e0425681a27016cc453cbb5fcab5ec9b52c925ec8a52c795ec4952b205f9c0538304f6d8433583dc403bc3837c18355e81d5601b2681721815 13 8191 5 31 11 2047 20 1048575
def cc_86_4 : Nat → LPN := uC 0x300b4ed0a8e559425088e208822088220755c1701936058054c9c240900601000400 0x864269401149f02b0b94d280a293c05a148bd0225e860a2c2c1149d02f0a34e7e9284268e2114a10815c83ca841c1720d0a0fc2608281e9360d49a02afba6081c9e9364d49902d01a5e7e5293ec9419829ec993d82c9bc124d51209e8683d8201bc0c0d49802f00b4e81127c0690d9225ebd927430179d409c9702f00a3c 10 1023 4 15 11 2047 21 2097151
def cur_86 : Nat → LPN := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_86_4 (Nat.sub p 512)) (cc_86_3 (Nat.sub p 384)) (Nat.blt p 512)) (cc_86_2 (Nat.sub p 256)) (Nat.blt p 384)) (cc_86_1 (Nat.sub p 128)) (Nat.blt p 256)) (cc_86_0 p) (Nat.blt p 128)
def hc_86_0 : Nat → Nat := uH 0xae334d69842a985b5141ca6f0dd358129a00744048a1107800000000012c4af95b038000000000000000000000000000000126c259320249402a44c2b2240191100c8084000000000008fd02000000000011ba200000046703c00001198028c80245f8262e00f16c028ad04c5301e290040000089f02c251560f81905e0f823063fb8b1fb016fc20b7d605be9011f0024000007bc02000001ee008ed64d767023af025d003ce6a0b72c04b5e1c1ac018d0e2967d053290ad91c16c780b63105b1700d87024000006180230682d80816000005ff01ad89396b408b440b5840f2bc82d5cc0cad00b55f04a771c539014976293ba80800000e8c2e0000000000000000e183a0000037906800000000006ea0436d041b2820d741069811348021a2010cf01065e0d00000000000c9c106460431407986020c10105fc062445d000000000004402419446012dbc0004a00000 0xa53528521482ca502956338ce57065559c0e51941abfdb7abc5e2f576a518845ad6338ce50af3d54a52940af5294e421481ceb38b02bec6719ca3028c63cfe14852f7be4299ce3742f3fe12e319def1eff172bc54a9780fde948421497397326690a4217837de57799c637aef5debbbfdc6fec67d5cae9494a739c637f9bcae7dc6f5de6a5294a52ca406318ca518c6718c6906a4210a5ee378d7f298dee73bd37a6f4dbfccefdebe9b739f5329a52b58c6339dfe1bca64deef4d37a6f35ad6b5acb295ace7039ce719c671a46a4210a46f75284a1084a142c84210a4a35956318c2119ce759ca529ce7084e318c6339c633be424cf99d234bcdfffffffffe6bffffa17fffdf66ffffbe94a5094a129421294a52942118c18318c6318c2118d66fc65294abba033194a14852518c64c994e73972e318cea529425284a50846518c6318c6318423394e739ce739ce109c6318c6338ca3060c631932631a4210846918c6338d084210842 21 2097151 9 511
def hc_86_1 : Nat → Nat := uH 0xc43018000000000030fa09c1a92305809be697ef9204bdb84800000000002f361cba9126ca102ad42a2a2894a37a966db029ad04e5d27195191a51c1594003a4fa0393584a4a01b92680c0000000000248e06000002486048ff116254d48908261d835874012170308259b5f2ab67c8811e56666e05ac0000069b229a341c68c009a180c6758840000067400d9c406000000000006381c96176554221d22174000000000004780811d80447182518e1c46200d0f8483fda04fee043ec07cfa8043e8010f72173da810f182931459000000000000c10202ff824bf6042ef870bb6042dc888b6a042cf05cb34042b78acad604291124a3c0424da0c8387f15bd9455a0a0000005460a14c8284ec230000004d20d12b04c4881210d8a43328200000031c0b0bd84c2d0130998d40000008f85023a020000002320408503c1f60f0409e80f80503d8040e00b03282c08e1e000000000000218100521a00507c0000a 0xf3c572e14852f7bc21264deee736b3e16f411ceb5a52b18dff66373ad6b373ad631ace574a4e73b65cb0ee738561684ba10b52109e56b2b99cda10b56759caef57395d6842769ceaaa84a5094a55318c65530846739ce557084e318c6b5ac165590852b5ad655d085a55338ce739ceaa2b5856b2adad6b2ae842d39ce72aab842739ce7556c2b5856b2adad6b2ae842d39ce72bbd55c2139ce739b222aac9512a6555573052f2a8a5ad6d685214ac635acabbccb161216448954cd9577d4f9bfdffde633f994deede7d5d0a4292aeb4be31aa22aaa8ac2d6912ab255b59554caba10b56759caaaaefd084e73bc5feef18ced08defe84bb42319c6b01aeb585214bc6359cbeb974e76cda5694a5292cad6b5b4ba94a52739ce72ba5212e739df6b582de590852b5bce71932e76d66d615ac2b584bab5ad65d085a759ce739ce5577bb42139ce739ce759c38739ce749c21084e13a4e339ce7195949d26214852100890a4231ad610235614a4a979bede2f348d2f76f3cba14a4210842d6a5210b5a10846d5ada10842148429084294891294b5264ca4214ad6d6b5a1084294a4694a56759dad3b4ed0842f108521084e752b05bcba10842b5b5a10a52d38c2109ceb5ad6108421484210ad6b5b5ad6842109ce739da739ce148421085ee739d2b4891294b5264ca4214a4694a5290842f348499fff97c8d277ec652946534a4a539c6a5280cc65284214852319326529fca637e77ca6ffffca65dffa4290842ffa529425284a50846318ca318c6318c2118ca3060c631932631a4210846918c6529ca729ce109c633bcc6318c6f77c84b9f97f9be4e97fbbfcf95df9deae7fddf2148421773ad6b58c6b395d293bed6b01b9d6b084290a56b7bcae7264ce752940af2c84291946719ca718c6718c6b295615942b5842558ca358c6108ce739ca739ce739c2138c677b9c633ace1c39ce72e5ce74842109d2738c63485f77cdea994eb2a0a5fe73bdcc6f13351ace550940a10842501094e700856318ce33953e3e5277ca46bc90852948ce54d56553293a5235084a140a594814a7382d6318ce33952faef4dec84a674fa294a5459ca32a42 22 4194303 9 511
def hc_86_2 : Nat → Nat := uH 0xc9a40b24213c581c70d645c3400c00000c11916e9ed4b719b2c5ab6ae49928bd6b0000027a88a9e880e6be728fd5962e886800dcc000007fd819fbc1d000001f8e17000001f82067ce094000007cb019f0215000001ef6067af871c4d39000001c1c18704814000006f4881b2855686221850e45e298d6a8715a80116860d55da2146688517811456045090654060f4ff8113de104e7085394044e301128a814a081127a0449a025156893d9be000000000000f26203c7810ef017000000eea033a7898e820e39e810e740338f86c0000038e808df821000000d2669347810d16042efab0b96142e002cb5a132cf8389e0af0000009ce092718100000026e8189a00d0000000000000000099804000000000002640100000025e0300000025b01896404208a8459b4414f8b850c1900000044a610000003a8510b29bc1c48305f88c1780305982411c250308b405a3400d04c006170000000000300000000000 0x2aaa1294252954c63194deaa6108ca9115564a89532a5294aba10b46318caae558291f54514a56b4290a4a52a6f31429cea120a4489552a6f576aba14852f18caabad54455551285ad225564aaa328caaaa6fd0846529555caba10b463501a652852149465f4cba379ce354aa4a94a5292c8c6318ca69484a94a56975294a46318d4a502bcb210a498ca94e6318d5295284a5094a12e8ca318c631954de6d0846319460c18c631a4610842308d2554a529742168c6318c6319c631a5274988521484022429094a10234a149ced4a42075d084216b42108dad08529694ad084210a421484214a44894a5a93265210a4a328dad1b46d0842f108521084a56b5ad084214a5274a5231a968ca053ae842108461094ad684231a52a529421084290842118c631b46318c29084210be4a91225296a4c994842908425294ad6b5a10842318c694a4e94a5e52f6cfbbe5697f9eb19bfdcaf367fdde4ad2ff7739d60b59b5acd8560b5842b4842b4842502aca35aca329421281de0e7016759d6b084e529d672bfe42425fee90a41485252bc65181ce5cb9ca94a52005294a94a5200739ce94852739ce8400a5294a10940ef00739ce7084e739ce53800040900081006014038aa00aaa109400ab6109ca729d08521494a52bc65181dd671b654aff73c2005294a5084a0007759d6109ca7294a74a52900294a54a5290059d674852929ca77fc52f07fc73fff97c52f097bbfe94a50000942508400a729d6759d6109dffee84006318c6108c0016759d6109c6318c6340000004200090000840a000300294a528425058001df6759d6109ca7294a77fba425cfffc9d2dfee579ce37fbffbfdcae35fee93a46b1d80dceb584214852f18ce7227fd0284a0528423018c6318c2119c0e739ce7084e318c7a4277aef779de2752940af2c84292814a5084a7381c63067019d6e719cef77f9eeb8f8cef3ec161582d610ac16109c00e739ce7384273ac739d60b0ac16b084a052942129ce0077b9ce739c2139ca739ce759ce72e5ce74842109d2719ce739ce301e638707af73f31cbbf3b18e1d6b0a42918d6b2239d63b1dac290a466339c76b0ac1610842738c6b58425deb96d6d582ce7085ad6a5a918d6b2ef5cb295ba8fccefb6def99cc6fb3b38def37bdcfe6f19c6d0bdcfcdee779dcfe 22 4194303 9 511
def hc_86_3 : Nat → Nat := uH 0xdee23000000da8a2f39985ca321b16a91c5483313a0cbf4ad000000bb0a2000000b6c226c8a9300000000000aeb9b800000000002b284300000000000aa890e918c50000029100400000290a03a1118c00000a0a03a816099dc14c000009d6032746099a894a49f02000002492069160740000090a85e1bb3800000218a1886001400000850082098547e2221dc0e473e98dc1871704011bf40e6b8a259d2886728119c2046640659701065a011944126408858fa0463c8117de8a5f58117ce045ef0256aa8952ebe00000000000147a2051c81144417000001376674db81136604483ab11e8134232b80000041e8250720441a8110500d0000000000041201000000000001040040000010280c408011018043b6280c53432fd0bcbbe1b000000afc61000000a5c502601b887c8221a8247ae5e1e981078212000000000001d306c6bc481a48546601919680c000000000005ce460f041c270a8052a4c000a5 0xa5210805e5d0210890a52b4210a5f2939caa5210804eba0421120c6b5ada10852f94ada346b421084002f108521085210852d49932900a05695a50a421084294a5234a52b05b56d58521084214a5293a5292acad1a590694aa0092952b2d80256b494a52a0078802d6848a4a05294a328d60b5ad6759d1472c7ad2ea4213a14b4a9528d47256a5a6cdac76395b5255955a100b4ba10a5a3494a56a5291a52f73956d0805a5d0852d3a4635ad6d4a5274a5f6d00842d4b5250295a54952b05adab4ad2559555104290a4201121298d2139d21520551084251095cea40aa21084632884b544210852517aaa88aaa2554521084254caaa8a421084ab95ed2968c10210a429081154c673be4e97d2501289109f6842949cedf297d2501289109319f4214a5d3a10842148425517ca4489484212ba5d084214a5234a52d2e84210a5293a529794bd53e6f92a5f8c650294a94a54250294212a4212a42101bc0c601465194a108ca05294e5294eb5842b19565195ff21212ff348520a429018c9935aceeb38d694a5200318c69485200b5ad694a52318c68406f00318c63084600010240020401800b5ad6b0856318c6b1807160aa00aaa108c00ab610ac6528d08521483c6518d536b5aceeb3956ff37a100078ca328423005ad6b5842b194a558d294a400a328d214a4016b5ad294a46528dff14bc1ff0deff7cbe29784bcdff6b5ac002b0ac0002128ca30028ca3284237ff9a100028ca3284230039ce73842719ce738d000000108002400021028000dea328ca108c160007005ad6b5842b194a558dfe690933fff234a8d40663294210a42918c88ee77fd0284a0528423018c6318c2119c0e739ce7084e318c484e6a501940a75908520ce306140ab5842b18ceb318c631bcdffe6b8f9c6ffa050940a5084600318c6318c211940a1083598c6a050940a508463001bcc6318c6108c6518c64c98c69084211a4028156b085631ac6318c6319c6318de618307af37bc61937e6a30c194a1485252910c673a8d46a50a42918c6a373a84a050842118ca50849bd32b9caad281463085ad6a5a92949bd32ca4e72bcd8ca94f82bd043194a9494e77fdb9d8ca55bb194a5194d2939c631bfce33de67ded94c290a49933fbc2154f851e318c250b425d085a9085e928ca329bd4c6575a108da5297cef3b42168c6aaa84a5094a55318c65530846739ce557084e318c6a52a814ab210a46318ca5294aba10b46318cb544a5094a55318c6555308465294a55d085a318c6 22 4194303 9 511
def hc_86_4 : Nat → Nat := uH 0x2c54e000000aa5384e337e56cd71ca767fa75bc49c5c68ded6e6364837af298d43dac9ea1a0000023c9f117c34000003e43d969c449f8aa4187218643078258001e000000 0x18290432a50a429294abe9b4a739585904736b0a42918d6b2afaed5ad41f050041ad2b244aaaa052a65555568425582cab95556da10acab2a078801ad0a4292a3328cd8dd67496400a554a52900596d294a4a5295f00000000d097401201080014aa00c2814212802cb601c582c21594a52a000aa00ab294a400ab294a4a529554004a128001554a5280156c215aa802a98423002ad842b18c63550015856000555294a00555084aaa00aaa109400aae109ce739d0007c04200090002a828000c00aaa1094160007002ad842b294a57a19467044c8a14a1485252bc651bccc427395e8eb19c117258b5852148c6b59dd677998856a00faa008d1ad0974216a4211c940a54a946a319b4212ac166cdac7671bb42159565422448788904ca552eb2dad2078842884205294651ad6b3ace84021084a050842129560b084215acab2b40294a52005294a94a5200b5ad694a525294ad00bc004210803402008005294a1084200c28002d6b5842108071605294a 21 2097151 9 511
def nh_86 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_86_4 (Nat.sub p 512)) (hc_86_3 (Nat.sub p 384)) (Nat.blt p 512)) (hc_86_2 (Nat.sub p 256)) (Nat.blt p 384)) (hc_86_1 (Nat.sub p 128)) (Nat.blt p 256)) (hc_86_0 p) (Nat.blt p 128)
def f_86 := uF 0x21909b0b14585ca6c2c1140169f09b4e84d1c002d2e0d4a10695c834a841a1720d0a000b478189bc140f60626b0303781c9ec0c0d40168701a4f80d2180293a0147800a4b7fc16bf8495fd25afe02500521be4d25f2686fb9377dc1bbe4d05f507af91277cc9ebe409c01484f79457bc22bd0979ec4a4f602d7a092bd2949e925af40250051dbcc131e328af214c78c22bb4979e1048efa5277c16bb4495dd248eda5276c96bb409401466eba5c75c923a88edd54b8ea233004a7ba44d1cc696e7a3473c9a398d0dcc29ce613c004a5b6ed71b76a2e3a3b71d19b6ed41b74a0e1c6070d3636e8edbf8c0dfa6c6fc9236e8cdbc256de1236dc2e3708edb9248dc2336dc2800251db4468da134669a5b644d19a686d8035668a735a8edad466cd0186aca1334055a9248cda3b66d19b360fd9b076d1c5068d203360dda0680d0230678a233c0f19b066cd82f66c11b3405001286c1c5360dafb2c115836bcca03560da9306979834a4c825d60caf3144d98a02ac583962c18b14051832a4c183b60c1bb08d49844bcc225260c1a8024fd7f030bf8155fc0a0024ed7d06abc4525e12f2f3179794bcbc04d0049bae853974278ba01500499ae41156f4bcb82525bc128024bd6d02a009235a92e2d40915e476b425c57919acad7165068af13f58a282c41315e26eafa5c57c122bc4bc0109eae034559a5ab24d159068ab343558272ac0f001096a0b5c505a8aa28ed51466a0b505052829b1814d4d8a0a3b526302929b149048a0a3351895a8c48d412b8a123b50c122848cd412a0008474f89a27c0d1146969e034451a1a72511390888a24f4d6b026a571350b88a2474c89a2640d11447e981354502725a8ed2d4668a02c4a1212505392828c9413e4501324c091154768aa3348c1a22a4fd152768f4504792023c1311526e8db4046d18232911192788a93345c1222a4bd152468a024004219e514cf26be881453c9af21c4d4f26a47925e3c9291e457d08288840143c8a99e453cf22867913b3c89b9f7178fb8a47da5e3ed291f6578fd0287d9523ec991e44d4f94ba7905e3cc1b1e6058f40727a0313cc0a1e41480107e7702c3b8131dc090010767613537a291bc978de2be73560398ae1cc050de2a66fb5e37da91be978df2bc7001437ca91bc5340106e6e144355279b4490d54866a84e3541e1ac508d504c0083334ca2990978c82be6793433c0a19054cc96bc64b52324af194050c92a4641250041798c0980104661a3430c9a16ad2cc0268600342d5a197c4d8b549c5a94e2ed2216a13cb84b85c14c2d42396c8d0b507e0081f2c89a1640d0a369657a342bc1a146d0cad28851a4f2acae14691ca926851a3f29c1b146538a528a5184e28c1300206c9e4b04f254278aa13c150238be4ca48265221325109908811c5308daf1268e0934684993424c1a046d4c9149045c5122d1d11cd008b46c4593622c1b046d4886470432342189a10c0d0236964123820d281048d02368611a5f1fda48469787d8c011a531d2288e8d447846c3c0361d1a80e8574754a03a14e08d2904693c6c6bc3625e1bdae0d89486c26a3603508d270d2d706927811a4b19ab00ccd402348e31450189a00c4530606a83014c08d218a5178528a42e144149af0b31405926829352149a48a4d04522bc2913d14da80a44d42348411a3f08d1989c1102329e2225e11129088578494a022152110a4888504440742203608ca7082900410b8119470f8a707c4b8232841e03408c9f8745102309e1725e0b92905c578354a0171520b8a485c5042e09c170420b81d05c0d82309c15a400acae04611c2629c131420982704c0b8230841213408c1f80205c210680134b0751a03a4d01d0680134306c1200e8ec172500c14005c9200e8cc150680393f01c9d821140104800804c01c9b81ad000d46005a4402c9e00e4cc090480392f01c91804490040720203100c0a004138010260001f 10 11
def ch_86 := dN 0xffffffff00000000 g_86 ep_86 2 3 bds_86 538 (dT 0xffffffff00000000 [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000] 8 f_86) cur_86 nh_86
set_option maxHeartbeats 0 in
theorem rc_86 : dR 0xffffffff00000000 g_86 ep_86 2 3 538 bds_86 (dT 0xffffffff00000000 [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000] 8 f_86) (cur_86 0) (nh_86 0) [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000] 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_86_0 : tB 0 32 ch_86 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_86_1 : tB 32 64 ch_86 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_86_2 : tB 64 96 ch_86 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_86_3 : tB 96 128 ch_86 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_86_4 : tB 128 160 ch_86 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_86_5 : tB 160 192 ch_86 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_86_6 : tB 192 224 ch_86 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_86_7 : tB 224 256 ch_86 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_86_8 : tB 256 288 ch_86 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_86_9 : tB 288 320 ch_86 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_86_10 : tB 320 352 ch_86 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_86_11 : tB 352 384 ch_86 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_86_12 : tB 384 416 ch_86 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_86_13 : tB 416 448 ch_86 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_86_14 : tB 448 480 ch_86 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_86_15 : tB 480 512 ch_86 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_86_16 : tB 512 538 ch_86 = true := by decide +kernel
theorem nj_86_1 : ∀ i, 0 ≤ i → i < 64 → ch_86 i = true := bJ (fun _ h1 h2 => tA nb_86_0 h1 h2) (fun _ h1 h2 => tA nb_86_1 h1 h2)
theorem nj_86_2 : ∀ i, 0 ≤ i → i < 96 → ch_86 i = true := bJ nj_86_1 (fun _ h1 h2 => tA nb_86_2 h1 h2)
theorem nj_86_3 : ∀ i, 0 ≤ i → i < 128 → ch_86 i = true := bJ nj_86_2 (fun _ h1 h2 => tA nb_86_3 h1 h2)
theorem nj_86_4 : ∀ i, 0 ≤ i → i < 160 → ch_86 i = true := bJ nj_86_3 (fun _ h1 h2 => tA nb_86_4 h1 h2)
theorem nj_86_5 : ∀ i, 0 ≤ i → i < 192 → ch_86 i = true := bJ nj_86_4 (fun _ h1 h2 => tA nb_86_5 h1 h2)
theorem nj_86_6 : ∀ i, 0 ≤ i → i < 224 → ch_86 i = true := bJ nj_86_5 (fun _ h1 h2 => tA nb_86_6 h1 h2)
theorem nj_86_7 : ∀ i, 0 ≤ i → i < 256 → ch_86 i = true := bJ nj_86_6 (fun _ h1 h2 => tA nb_86_7 h1 h2)
theorem nj_86_8 : ∀ i, 0 ≤ i → i < 288 → ch_86 i = true := bJ nj_86_7 (fun _ h1 h2 => tA nb_86_8 h1 h2)
theorem nj_86_9 : ∀ i, 0 ≤ i → i < 320 → ch_86 i = true := bJ nj_86_8 (fun _ h1 h2 => tA nb_86_9 h1 h2)
theorem nj_86_10 : ∀ i, 0 ≤ i → i < 352 → ch_86 i = true := bJ nj_86_9 (fun _ h1 h2 => tA nb_86_10 h1 h2)
theorem nj_86_11 : ∀ i, 0 ≤ i → i < 384 → ch_86 i = true := bJ nj_86_10 (fun _ h1 h2 => tA nb_86_11 h1 h2)
theorem nj_86_12 : ∀ i, 0 ≤ i → i < 416 → ch_86 i = true := bJ nj_86_11 (fun _ h1 h2 => tA nb_86_12 h1 h2)
theorem nj_86_13 : ∀ i, 0 ≤ i → i < 448 → ch_86 i = true := bJ nj_86_12 (fun _ h1 h2 => tA nb_86_13 h1 h2)
theorem nj_86_14 : ∀ i, 0 ≤ i → i < 480 → ch_86 i = true := bJ nj_86_13 (fun _ h1 h2 => tA nb_86_14 h1 h2)
theorem nj_86_15 : ∀ i, 0 ≤ i → i < 512 → ch_86 i = true := bJ nj_86_14 (fun _ h1 h2 => tA nb_86_15 h1 h2)
theorem nj_86_16 : ∀ i, 0 ≤ i → i < 538 → ch_86 i = true := bJ nj_86_15 (fun _ h1 h2 => tA nb_86_16 h1 h2)
theorem nc_86 : ∀ i, 0 ≤ i → i < 538 → ch_86 i = true := nj_86_16
theorem lb_86 : LowerBin 0xffffffff00000000 [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000] g_86 9 :=
  lowerDagV5 (kn_cons lb_17 (kn_cons lb_24 (kn_cons lb_30 (kn_cons lb_35 (kn_cons lb_2 (kn_cons lb_38 (kn_cons lb_31 (kn_cons lb_3 (kn_cons lb_5 (kn_cons lb_74 (kn_cons lb_73 (kn_cons lb_75 (kn_cons lb_76 (kn_nil)))))))))))))) rc_86 nc_86 (by decide +kernel)
def g_87 := 0x115153713371f7f
def ep_87 := 0x12220a480000142200000c4800140022002400600104040402040e0801101032133210200115150410041040
def bds_87 : BList := [(m_82,s_82,8,g_82),(m_77,s_77,8,g_77),(m_83,s_83,8,g_83),(m_80,s_80,7,g_80),(m_78,s_78,7,g_78),(m_11,s_11,5,g_11),(m_79,s_79,7,g_79),(m_12,s_12,6,g_12),(m_46,s_46,6,g_46),(m_85,s_85,9,g_85),(m_86,s_86,9,g_86),(m_10,s_10,5,g_10),(m_81,s_81,9,g_81),(m_23,s_23,5,g_23),(m_21,s_21,5,g_21),(m_84,s_84,9,g_84),(m_35,s_35,5,g_35),(m_20,s_20,5,g_20),(m_22,s_22,5,g_22),(m_15,s_15,5,g_15),(m_42,s_42,6,g_42),(m_59,s_59,5,g_59)]
def cc_87_0 : Nat → LPN := uC 0xdd06c93641b20d716b834c9a60d20e80b385925c906483203808c006002fc37e0b935c82e416e2b41da02cc3622b10578abc1583ab0d5069c74a2a02d0028013849c04e026c33609b04d8250f280940490a4811c48e047023051808823c41e00ee17703a89d40e056f0b781bc0d456a03501a04d006613301980c636303181844b665b02d05642b205902a91540aa05502a05500a614f227813449a04b1248924092047123811c08a23f31e0cf007803c01d84ec07413529a80d026803401908c806403011800c006002b28d44072001 0x404590ff1543f25401291803a540f69103e47d0f51c43ca7c00c918313620c31c83b25c0e2dbc303630e11fc2fc730ef1643ac550e895038a540d99f82ee7d0e55fc385730dd1e42ec7104097809a560da9103757d0875bc1b5670d9178092660d691034c6f0d118c2f47d0ce9f008a560ca9b0325740ac9103125c0aa91030d640c09902a2440209580fa6e0b291027848094110270380920d02da7c03c9b02c24409a120240440b2db82c3660980e0238340ab1502b56f0a958c2145f06915c29b6f0a4d7c28b5709c9b00e25c09f1b826c660349b8262440925b00c95c094db82436602e5b8239340c79fc2fe730bb5f420d6f06759c2f47e0bb1f42e46f0b519c0b26e01e998022540ae918282440961282304606b1901bc640849102257e0871ec20c7307d1a42025405b1901f56d07b1f812a7e0069501e2440749581ca5406f1f01927c06b1f018a7c0689101936b062d8c1c67206d1ec19c730591441826c01a9301725e05b1b0165650571f811a7e05491013364048d901445b04f15c12b4b046d0c0fe7d03edc40e0380320d00d8380300d00e364036d500ca640309500fc7d03edf40f36503ad540d03a02e0d810c6e040dbc0b363020df40837e02958809b6f024dac08b6701ed8c06c56017160053580111c003b700135ac0356700b18802362006d684156f0fb5ac3c5670e758c37c6f0d51ac3346708b18c1fc5f07716c17c5705314c1126e02a978072560189380124683517e0ac5b82315dff4537f2d7dfa35b7e2d5ddeb53758d3dd034b70ed1db7b436c496d9fa535ca92d4f2434f08ed31a3344657cf895731c53c909471ce4fc439370024bc0003f 13 8191 5 31 11 2047 22 4194303
def cc_87_1 : Nat → LPN := uC 0xa80d402a014c2a31d1828c1460a304f927453a09d04d8a683321980cb865c12c1950c89238706b83041060810028004001f84fc07c13e01f00f237903b89dc0ec17603b01d80e637303905c80e216e1b39d9c0c836403109880c025c22e01700b42552aa81540a62520a901442a20500a7853829a14d026052c28e44512281102880430a1810068004001f08f807823c01e00e467203901c04dc26c13509a80d026612d31490a4052027113809824a125012808c44602300f147803c01e00e086841500a004841c40e00228100004000 0x7fb647ec6f7e4638047e7f27e7da447cc7e7c27e7ba547b2447926479a5479b6c7935c77c687635477d6c75c507635c75d647845f7745b76c57754537a46e78a6674a448ed6f8d5638c45f8a45789b6e88b5e87b5680a637d25b7aa537424b734686cc70724587123b70a33704706fa706c4706ec586e3586d3556923b68a396b26e6aa626a260682646835c6967968c6e67a666cd696c5616bb5f69b5754a5b4b2536723b6446b62c636636e6536e582635425b4a2536456a63b5c53a6b49a635325b4925362d6a6236661b5c5226b4826360a3b602335fb5c5eb5c5cb685b3545cc6c5ab505b35c5ac645d35f5c35b5bb575a3535da6659a5c58a4457c60585625726656a5c55a46552445446c51a6c5346c5126c52a44503784eb645047c4e3604eb6c4e47451c6b5146350b6f4fb6b4f3674db6354d7253c7b524734d25c4c2464ba444aa444a46c4946c48a444b57249c7b4847347a5c4724c45b5f4535b4626644a5c72d6f71d6b6f5676dd6366c6265c5a64c526336b613635f35b5e3535926b562634ca5b46a534423332b623247242a6c3947f31c73434694246541a640525440a44 13 8191 5 31 11 2047 20 1048575
def cc_87_2 : Nat → LPN := uC 0xa615286903442a2051028433c39d0caa2541281930c69a2c51608b0448a24110188044021470a0840c2021010808024001fc2fe07e0be85e48f207903c05d84ea17503a05c84da56d03681a48d01670b289940ca06122d996c0b415a02c855c4aa25502a81540a815212901442a20500a7853c09e04d1268124892047123811828823a51d00e807403811c00d466a03409a00d0068030210408004001f08e887403a01b10d806823401a00c085c22a2150090c48022111007883c01e00d106042c214109084802020e1032000c000000 0xbfd70bd37da7263bcb6cbe454bc37cbcb44bc563af263a6a53aea63bee70bdd73b946cbd37ebbb6cbb35cae273a4a53a3a43a2a53ba56bb9c6eb9362b2a6ba225392a31a1a5396a49b7c7eb746cb6354b5e72b537eb4b6cb3a56b3670b2c6db226cb1a46ada6cafa5cad26caf47caec6caca7caaa54ad36cadb6facb63ab462ab460abc60aab72b0e70b047fae473ac26caa246a7471a9256a8a549ea4ca0a6ca6244a025c9ba44a6670a346ca036ca5b60a7780a2d7ca6c7c9fa7c9b254a5244a4264a3244a3d7ea2c729aa549ca44a035ca0b6f9fb639ed629db6c9c4629c4609bb6c9d4729cc609b3729ab6098c6099b6c98c629936398351a8672a7c7fa4c73a246da1c61a127e9f26c9e24c9a24697a449656a95d6896c609527e94a6c93a549367292c6c9227e91a6cc6562c4c6bc3463c236fc0b6bbf367bab63b8b5db8351b6b4fb4343b126ba9a63972439423b912338fa44903648f26b8e4548db548cb548ba4b8b2438ab6c8024b7ca438946e86a637a23b8856285a64872548636c85b5c8446882b548456c8245082b5c8256484c5f83c5b8345781c5386c6e8526681244 13 8191 5 31 11 2047 20 1048575
def cc_87_3 : Nat → LPN := uC 0xb805b86d836a1b40d986cc1641b10d692b41581a91d0268013e19f04f827c13e09b24d0650d2809404a024092008e147023811828a1440a2010a383141060810407f1bd15e80f407a03d01e80f21742ba01d00e807403985bc8bf05f02f81744ba05d02e81686b405a02c09600ac25602b01542aa051228053c29834c026012c292249024812028e1422a0850407e23f01f80fc07c13c11e00f007613531a80cc4660330180cc005e12f01780b445242901480a404c31680b003901c00e0058c2c014106203000c60600300088040001 0x7f92a3f71a1f88a8fdd6c7de283f11b1f7ac8fe45f7ea2dbf315df68a6fa5707f6b8bea9f1f34ad1146d88630c40db61f6c30e34f851a3c1492dff486f923b7c2323dd1f1ed6faf63717ad383248cde5cfcf067d79dbcbc0dc5b54e6d4a5b79e3ebccd51e569cce24b78e3e3c2df5d9472ea03874c1c39a0d1d2070e60347611cba20e1cb068da26366d1dbae991d76b8e80387281a3b31f1d88c8eb26473c24392111d04a8ea36c74db33a4d91d16a8e7a39728aa39a999cc4c8e5a5472494bc11f5c18cef0b7e781bebbedb5de6ceeeb65771b23b6d55da6a8d9a7369d35b3292dd5476e703a7201b38cdf9c56a8e1e7270a36382dcdbeac4dda6b6f136372931b98a8ddc556e92a370939b748cd92546b522369191b04c8d62546c5b6364dbdb06c6d6b546b1b936b1fdb38e6d7a546b927356919a54a8d1a646a122348db1a56ded1b63682393531fda78e6d327e6892a3429399f48ccb26467522337191954c8cd2446623332cdad956c6ce47b66639b2e9f9944a8c957e6453f320951efadef55677a6373d0dbde46d6f136771db1b88d6dc06aedfb496f5a2b6c9adaa4c6cf25b64d1db1e8cd836d2beb615ada9acc9a5614c2a825363525a4c8cd8b8d8ba36d629a2af8dc9888d8c2b7f5edb9b0ed15858e6b027353d21b079c1826d8c0243 13 8191 5 31 11 2047 21 2097151
def cc_87_4 : Nat → LPN := uC 0xb205902c81640b01551a6a1340990cc066013009614b02581282911c8824031e18f047063051808b0c582206fab7c0bd85ec0ea6750390dc80e406e23701b42da06d03399944c62601b0017c2be05e0af01742ba05c0ae016c2b605912c81640ae25702b815c0aa255028154009e14d126813409624b0250520490048024012008084001f84fc07e03c19e00e847403a01c84d864b125012048843e31f00f807443811c00e006843401a00c085462a015009884c026011108804401e20b205802c012209004802401200710380182006 0x27c6d93db5c9fab14fadae7a6c71596f7ccb39e24fe9cadf4c56ba5ab3d2958e928d747c63a362dd1314e824dd3fa5e9e52b4545bdf22cec995f4a0ab9d053e774c9381459d0a7ce651e714d9382549d52b4e49526f2af3694f9b12a4d49b19129e9214799e374cb58a252de461379dab7cdd58e6b8bf34c579a1374cc97a644ad1216f63cafa4455c8828f3046897ab24c15ba5c6df2c36392131c5a8ee284672f45296dafcaed4e5c8d32dc6591525c7890e596a92c56995eb2ca7192566ad21a5b8e929c8496e394a720a4b8dd21ca6d4a3f4971a2439463249ed924dad125b649252a4915a6474ad20d749112248318a404f922c7f90e39c851a63f8cb1f2648e23246f5d23b4891b27c8e12246cd4a378c51aa7c8f23fc751ce398d31a4658cd3e46499231499182448b92a45b5a62c4c915a5689932452952268d11456989d3244a95a628df30c6397e2ccbb1565a6df2ab63951acca4d565069f2734b931a3c94d0e464c71ea4b8bd21c548ee24466fea3b84d25c1290e1d8bd08a5b81d29c3d1f21d6e10ba6186925c3290e17d010b28c86eb8c315c2154a70625484922420d7e0f6af06c70831b84271f6118e30727c82d23406952084890247080db8402d86098fb03c718193e40a9b20248d00244 13 8191 5 31 11 2047 21 2097151
def cc_87_5 : Nat → LPN := uC 0xd60ea87487a40d2069034439c3cb1e5832c1960c91630f1818a1c506093003800c005e8ef41762b7253c29c1483a40510a8813a59734b065812a195048164012008c246022c31608b0448a18706383041820c0f877c03c8de40f017803c01d46ea0740ba01d00e23627b101880bc45e02f01704b805b0ab915c0a455012801400a004b2a5812c0922480a4011c27e83f01f80f827c03d09e80f4068922911008424202100f887823c01d08e807023611818b0854220510007843c01e00d106043001610a085002420e20228100080002 0x5f2992f96a97f464be1325fa912f96a97dc6fbea31df0d8effafd7e473bdd2a5e8dbef36c77ac7ebbd3f5e4912f06c977b43bb8abb4c53cfe27ed095fba2385d7162ea6b174569680afdd35aee78c50596767cafe715af2dac79546fc9635e4119f008c77b45fbc629dda9baec49d732468f4b7c1459d9e2be7d14f264a3dc8992b149953244ab12a55a912e28fb70c71b813e55691aa44896de7eb4b3edbb1e6d28e31e17f53cabdab1d2dc4896ed7db6e2f552952da48849957b62be5a71f6d48c36ba7cb563e5900e2c306968a7cb1c24584112ca26b63038b041a57315ece6df1d96f528ab92251ecd27f66137b292258a122c00896426cb1e3358c912c528b6196cb09b35824d2c006b6957db52bad7159ed38fd6947db4233d50952cf48d65a448e8bfa9259c902af64947b102557e11abd8fd5a27ea852a578912b74f95ca44addb1d759cab88e75b26cac126568d2e332db02965508a39f04feb08ac47145ac62fd60d1e312be9e147abc9bd5b1c2ac6e09d1574d8abd5759eaa8c554b6aaa1b1542d6a022ce9a1573dc9ed4ad85322af5345fa922bd46d6ea26a750b4b8c0afc0055d2f28f5013fb8eb7dbf59ede8df6cc6bb5a33d7d18ebb8b75ac57acd3756493aae49953a46a7d2245e5bdff2ce971573d4a791a51e9d4c94d94fa68a3d32952974f94aa54674afcfa99a93488ce16f9ed324f89519a2bf48c6ea01374f499a90488cc96fa39225184fe8b26f45244a10aad0b592858a143461a122ad1116e878af4195765ca7a5451e818dd40363 13 8191 5 31 11 2047 21 2097151
def cc_87_6 : Nat → LPN := uC 0xd706b835c1a64d11670f3819c0cd0e6833419a0cc0e6032c36d5b605a86d416a0b315982c07600af0d782b45562a24d0868033849c04c8e4cd26091148823c51e08f045922c11608914406201100880440210908084042021010428203d9dec0f227713b81cc8c516013001800c005f0ae89648b20580ab85582aa1540aa014c2a414c323951c08c13f39f04f807a13d01c90e407203901b88cc86413201884b865c02d09680b405812a1138c9c04c126012849404a01d40d886c02e41700b045802c0150890c480240110878801e000 0x6fc92f7d487be14f0b497ef6d702c25f7aa4b5a8a38564bf778ddb8945dc51cf0b5bf758bbb9c5ae0e2beff15b7a8abbcb6ede1b16ecd7b756bbba34edcda6ea298ef14b744a4bdc91dc945bd682ae5e147dc09b8524bf6e4a9b6256dacabed59c3694d9b2a4c2ec9becb159b82bedb95f58cabedb17f688afb3a5ed992b6c893b6348cdb15f588ab96451f504b9a5a64d3d2f694959b52beb0157d21326bc9515d2cbaec6ed393768e99b424a8d996f570b3e8c9935b4a9a0a54d65226af9c3564d9a6a5cd11266a84ff5326fa9244d42b769edbf4e6c7a6b55d25b6690d734b8c5a536fd1db1e8cd36472de8513f2b89be89159ae2bed615f554abe84d8b416b4d595f550abec35bf60ac7afc6fd7231eb517f588b7aac57d4629e9897b454ada1a4ed012348c5bdaa2bea9957404a795851eea4a975a44ceeb8678d3f3a68f9f459cf62ae72952e948d8fc72cd1ac662d13348b998340cc5a66611532c6df8eb63cd5a7e66d2f3268f97b43cae3fe391cf378b39b455cb92a65895327cfd8c67dcaeb9e531e7188e32297f6a4afe371d32848994d7dc9e2f64c910a72af9196fc88b3e495c3198fb8d461c853e6289131e6b98fd64c75326269131b8f985038c5d326121230c26b84038c101a629153128c989d63bf62fe22dbe442ded415f294a3e204ff0f26f83848c0c2261a9730c48983048c08226149530749984c6ec212260c5170329982134c081ae399cf18afb8d575bf2b7e331fb188fb8b46fc552361c912432fed396f290abe1651f0509580846 13 8191 5 31 11 2047 21 2097151
def cc_87_7 : Nat → LPN := uC 0xb56ed21b30ecc0b302ab1a816a00a8029849fb67c19e8668999865e4960e4c6920a4238e163048b861c987021258482120830e0827cadf207a15e427885e207805d84729dc627181c607105c216d1db406b11ac06b01a066801a00668d9a0650d848608582060817665d817225c816c3572127b498126048891e2460d12344050c2418d060418100340010004000fa330f0c012f84bc12e08b232c80b012c00ae12b80ac120d480120007a31d887411d00702189c620180460017845a216045041400500140050012104801200480108c0bc0280081020006101800600088001 0x206d6f8175b60756581b1be0646e8171b5fe36f7dad8dd5b5b72ad5ddb34d814d2e04b49810d1e03b456f0d05b026365a96e0224b5288ed372334c25bcc31577fe51c8d13f1b64dc3992f0e44bd95a5b30a55c3812f7eb5b9f4d6d7fb1bdfe46373f175fdc597f5155db4517f0da5f4b616be98d9524b5bc90d2d16f3d053cc21470de4bdf636465296d6ea533ce57c3712f64e96d6da533ca57c3612f7f11b5dac5f72715dfbb5e7ecd59fab4e64a96d6ca5352492cf215f30255c631470d44bd6c241648965f9c6d7e5185f536d7d6d459024b5ac90cf114f2fc51c3312f0c84bdf84646eed91f335c0c64bd8fa5b2f855c3092f7dd151efb6473cd518e26b2f659c2f92f63692d6aa437d8db18d25b5a894d8ca4b5a690cf094f2f451c2f12f63096d692533c057c2e92f7a2121f23667c8d598b26b7d096deea393be5b42e12f7a00e1e30347cd5b9bbc6e6ba98d48a3b2ec555f1c7c79e121e284479c0e1e20347c8db9f235e7c498d682537c25bcef15f3ba575eb1350b44bde68387860d1cf5627bf1892b16f3b8534621377b4990ec96d7980e1edc5d7b4d71ea1357960e1e10347bb1b9ee26e7b2998ea96f7a6515e5048782111e4848780111eab607a8999ebc6a7acd9985a6b59298de9a397900e1df83461296de8a4b3a85742792f79e94d63a4379c57ce994f3a45342692f798979e5a5639e57de4b5a60c96d62a537a0d79e6b5660a96d622537948e4e715f7904d42592f09407de295358450de205f39a13ce604d09007de115639217de035a60456d6015378c979e1a5660256d5f9537824a4e405f77e0942301f7df5bdf6d637d31b5f5c6576917dc8c577d4db9f4b6d7ced7df2b5e74cd69f03577bcd59bc3526b898d8025b57c94d47a4b7b08ed2a96f38e57cba95718451de913708a4bde383a77c0d9c347c7769c1d9a497605157fa4b2de51c2212f6ef1f1d924975e515bbc6e724d502192f728d517e26b0824bdd9d7e7655d9d71557611f9d7c7675c925de56f77559ddcc6f7711b9dbc6776d189d245e6eb175dab6b768d8dd535b752d69d4359720d59bab51720d19d2b456da9adad2635ec96dd8a4b4d68cd2816f43859cb695775a51c8c13f07e4bdcbb54708d51c03446f6d501f12f57a90ce314f07a4bdcf562744515d123975758dd545f753179d445d71f155b9c5274edb9d336274ad59c7b55748d39b9b4d6b098d5da5351a92dd1a3b49c5bce215f17c51dd09370764bdcf56e73d1b1c72617165b5c6a617145b5cd1556d69e5cd2496d49a5aba6157494dcda4b38657dcc9470704bdcbc6c06e4bdca36c06c4bc1a92f724db15c25338257c1992f71d9e9c6e7242a5ddc496d7179e9c5672712985cfd6e73b5adce563731589cb46b72b18dc7c5e6e9175c9b6b722d8dc835e6ecd75c834e71ed25c1b436fed09bd3416d09adaaa6371894d5aa434d28cd2616f42859dc415f38053c8a13f05e4bdc3364708db1c145f70314dc035c 14 16383 5 31 11 2047 22 4194303
def cc_87_8 : Nat → LPN := uC 0xb80b61b60b03ae1ae079b7617607226c358a5234c346330b3002e12c12a12a02a02622031c21061001000a30a00a00a00a0005 0x10c4bdbbd627e0d884212f23c53e06d6f8315ba05d6d8331a606c63817185feb6f7ded8dcfb5d840d6e0fb5983cd5e0eb5574cd45de34f70ad0db0a6383896d71a435388ed3b2334c45be0d9573de53c8e93f1ca4dc4112f81f1919f25b1004bd9ea5b31455c3f92f8335b60c45e72cd5e0bb4982cd159c25b5308ecc49571c64dc3e92f5c490cf694f0f84bd70a533d857c3d12f776d3cf594f1be4de0646d81d1460a36d826d85dd34f8249816fa4352c8ecf514f1bc4dc3c12f820d7e07c6c806516032598045559ba5b1b85143b92f80a9260094573d189f736266c96cc39572384f43a92f80d16602c5580055601c7e804d2600b4580092537a33 12 4095 5 31 11 2047 22 4194303
def cur_87 : Nat → LPN := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_87_8 (Nat.sub p 1024)) (cc_87_7 (Nat.sub p 896)) (Nat.blt p 1024)) (cc_87_6 (Nat.sub p 768)) (Nat.blt p 896)) (cc_87_5 (Nat.sub p 640)) (Nat.blt p 768)) (cc_87_4 (Nat.sub p 512)) (Nat.blt p 640)) (cc_87_3 (Nat.sub p 384)) (Nat.blt p 512)) (cc_87_2 (Nat.sub p 256)) (Nat.blt p 384)) (cc_87_1 (Nat.sub p 128)) (Nat.blt p 256)) (cc_87_0 p) (Nat.blt p 128)
def hc_87_0 : Nat → Nat := uH 0xbfa0b4de0a71ae8b9e772d861b79675da555dac49b855e2909ae3637d60944aa3c323491a32a3ce2fd1c508a8b10c73d0e1f9c7c82cde316e66ba192db16b9380d649b00424d00212101608cece5467001a32f82317cc6c8bda0345c00b62be089141c75884c70c38628219c09d0c7c1985b62242c705215802f0748de836c0e00000020c6853060c0a82e6084163041ff9ae0ff541e0000003fba06dfb50a0fa04e97cc60f0000001f1f848f7945a79f6753add879cfd1c6e73c2b737c08b978119be0370d5f24468cc8b33773bd8e6b54bdb2615eca03af041856f5234b7341d5b261d2d810496b183cb4604b5a0e08ace009d59ab56a3426551700c27b840134aa469698ef47d2dea18e96d0569c27ef4f03ec02e9e47464ef50ba73910636ccbf19cd664c6021a62c80e313a0a989202c00000000000030e410186c018c3300c6118202e429295776a89f2b244b411523fe68913233488d0303f4d471c74cc8cc25e05813802aac5714d22109853904920c22370480fd878064d67c271ad40da979037cd600c63e000018c000000 0x1555556520005595939266b69335b4aa00a0aa00aa21084aa21288421202ac934e49d69b699e9b760fd60010842a9e6aaaa9aab2b2725555500544500555524028155414552c0000aa21084aa25d44251084201660002559269c956df2d83f580000c3c04210aa9a4a32aa8c0060c018b00ab21418b060c0084210840b300466ec63580fc52954ca519140042108f6cf6ea94aa652a4a00ab21468d060d1a02c000210842102cc01076b37e6c0fc555552800155f35b4f9ada554d4ab2aaa80aa0000212aaaa884210842120807cf7db7eb7db554d4a4ec1fac0021085557d5553cd55555352aca16aaa0aa0000a2aaaa82aaa92014058000112aa2551084210842016600027caab6aa9a949d83f580000cf0084215ad295954a8cca4000e52428d1a0c38d1a01c38001084210816600adeb37e6c0cf395d252a463000021084211ed9ede57d51931a46300039490a0c0060c018b060c00842108c25c42059802f18cdf8c0679351352a82800ac934e49993d2664f428000000002510842108421084210842100079439269c933d36d33d36fc1f8300108429a6aa9e69be9aab24d394934d39262800000261600039540900a02448004c002c038001288421084210842108421080598000bca1c934e524d36d3f49bf07e0c0000c3c04210b2ac6cecacec6316140e58d9eb58d9e8d9cac6958d9d8c1662c482c6ceca67ec9d9f326b9ad95358d614000000001caa018300162c0000058b0060c0009442108421084210842108402cc0005e50cdeb376f19bf07e0ec60cd60c0000cf0084215cf3cf333799cf3cf330607341b3cccf3367999e6aa19e79e60b30059e79e607e2ac94a922800842101ed9ede5734d252a4a0160b15473468d060c68d016000108420598020ed6b36ddbde6c0fc55555739ce5555749ca729d27680015400014155544210842109544254100abe0fc1b9ce73ab736e739b0010842aab9aadacaa9aafaaaa80002a22aaaa83800680302aa828aa02a88421084212a244a02cc0004abe0fc1d83f5956df2800019e01084295ea95eaaaaaabe57aa4aa630002aa9ac6b2aa82a8000084aaaaa210842108481e3ef6efac36d57c1f83b18d60010842aafaaa9aaaaaadf99ac6b22aa2a800028aaaaa0aaaa0e001600c002884aaa25d54421084210805980009f2aadaaf83f07631ac000067804210b3ccd9e79d8d24d49a82d40e59ce0cc3f679979e66767ecf4693e9a9fd0587ecf3b49f329f90585b99059ce0cc3f4349465cd140154c18031600703160c18010842059802337631ac07e2e6aae658c183418d060c68b000b30046b5ac07e33b494172d48d1a76833ce4005e725582c50ad3b419d4814480548b2db3329252a4a8036b5aca0000008421084210076bc3f5f6b076f5b330e3ab3b19f7e41778df254957db296b1954257a957c9400450000000004a210842108421084210842000f287e0fc1d83f5af3c36fc7ded80084214b52346742b4ecf29252a482002108401e2cb6ced6b59402c163943468d061c68d016000108420598026db7bc06192d48d19e628569d9e524a54907d63c00021084165b67eb5ad6b2facd80582c72868d1a0c38f1e34680b0000842102cc015b2adf9dad64ecfbf64d51400000000b0b01caa000068b00600d1600000004a21084210842108421084201660002f287e0fc1d830fd60ede0db0fdef59b000033c0210858d29326463193200e51c3801c1c090a2c18010842059802f37e6c0cf33ccc684739e61a33cc2cc68d1b41987e9c93926e4d4d4dd290001b46d1a4cc9c800c600000000000108421084210842108421084200f07e0e49a724cf4db4cf4dbd18da00108429c939266534c9c934cc64d3ccc9c93326f80000000000e1102402803060013000b00600042108421084210842108421080598000bc1f839269c8c9a6da7e337e3183000030f010842cf3cf3318d634b3cf3ccb3943060d9e66799b3cccf3516033cf3cc16600b3cf3cc0cf294a519536b366400e51c380b1602428d160c38010842059802f3766c0fc55949dad6b262acfbacd97dc00a305a40000000000000210842108421084210842108401eb5834d4a4ec1facf9efb6f9efb60021085565276b5ac9a79a9fb27653654fa9f7ec9a600000000003e16008812014068b0060050a001f0000108421084210842108421084201660002f5ac1a6a52760fd653efb6ff94d800019e010842c99454a4c990001084203db3dba518ca9498c64c8001616387289214387000162c18300210842102cc01061f9bf3607e38d1a3679e618d191c8b59f346798e002d6798586346d00b5987ecdc8e60e00587efb9f5f5f7293526a500018c6300019426000000000021084210842108421084210840203c1f837cf7db7cf7db4d4a4fc630600210859f7d32fa93526a7df318c9a664d4fa69e600000000000384407c000c1800900a02c0060c0008421084210842109f12e210842108402cc0005e0fc1bfe33667df6d35293f18c1800019e010842cf3cf3cf3cf3cf3cf3cf3cf372868367999e66cf333cc05acf3cf3059802cf3cf3033ccf3cf3318d632b3cf3cdca18306cf333ccd9e6679c8b0023679e79d840b30059e79e60679294a4c935acd950039470e0070702428d06004210816600bd6f3766c0cf272b4ad6b5a564d34c4dd66ca6e918002ca000000000000010842108421084210842108420101eb5839269cac1fac99e9b699e9b60021085395a56b5ad24ec9a69e76936649c934ecfa60000000000088120140680301224002600002108421084210842109312e210842100b300017ad60e49a72b07eb4934db4fd26c0000c3c04210b9ce739374a428e4d4e739ce739ce70022208424421225c19ee4dbf371137481ce739ca526e739ce739ce739f51000104891084885e6df6dc1f9d10d2348d234910489adbadba92a46d1b4e766eb395ce739ca53ace529ce758110002c16084244884213833dd66fcdc451946328ca441226b6eb6ea4a91b46d3ace766e5739ce74a4eb3a52739d604400108489108427067bacdf9be57395253a4e5738ceb38ceb39c22020a0000021288421288424421084210801cae77830fde707e0fc1f9ce0c004210a5290c99484140751c730fa1cc3ea52948140000000004a210842108421084210842001d471dc38e38e3b7294a4e739c0021085d525487591a4694a56958d23023e6a9b4690000008421084210847b67b720fd20c3cdcf396a59cb394b523f3cf394b526fac8147ccda348794a4a53f294a52d6a4fca52500000108421084210a41fa41867b619e7b7294a529326520071e5294a4695a4694800000000000421084210842108421084210842003c71c394a5294a41cbd291e19e1800842152954294a500172b94a529c6769c676850000000004891084210842108421084210801cae5294a739cdb8f736e739c0021085ad295c651acab294a328ca52940eb374a651b40000021084210842179bf37e52830c3aa0eb35328da552e554a9552a748002088421084884f94a0d6fcd54a555549aaa9540abaccca368500004a21084210bcadf94a0f5946ce95c1a5d66651b5a56935294a5295ad2b49a94a5294000034160842108421085e52830f5ad361ebded5294a95294a500a3294a32aca52940000000000021084210842108421084210842100783f06af294a52835294af07e0c004210b5ac6b59565595ad5b56d593b5a4a35200000000001084210842108421084210802d6b59f319f4d4a4f56b68004210ad6b5ad6d5b56b6ad6d5ada6cead69695656a40000000000000842108421084210842108421084016b5ade0fc1ead6d6ad60eded58004210aa98c692280084211ed9edd3494c63580042307766aae554ca34954c98caad8ca64c64104001109108421096fc9e63074655328c64500108423db3dbaa32a8c6b008421183ab9576698caaa9954ca349319532a8c085aa000025108421085e56cf3183e5718ca60c6318c633a4e5394e928008a0000000009442108421084210842108400e57783f066318ce739cd86e71fe7360021085cae32a86318c6319ce739f718ce1400000001288421084210842108420072bbc1f83318c6306e739ce700084215594e318c631831a4e72aca718c6319300000000001084210842108421084210801d6b3935293318c653efa8004210b9c6319326318ca318d2318c6318c6318000000000000108421084210842108421084210801c1f9de0fc19bc6318c60cc6318004210a20000000008421084210842100b30001783f07e0fc1f83f06000067804210acb2cb2cb5d75d75d72cb5fc1f83f07e0fc1f83f17e0fc1f97 25 33554431 10 1023
def hc_87_1 : Nat → Nat := uH 0xf4548dfa1e033d09817e1dd9cec5127f5313dfa08243c9d99ae150e76e5694b6b09ebb3cc6ed96021eb804c35bb014000000d6da04eb50074000000000000d6700c699967f3bec3996cdcac75903e0c9b8ef8db5d731e54b96a095ca5042d71b8565f566ae532a553d7b29c0b7941bb13a09611ceec57e6783f92f491e976210cb8c0965878fb279d2893c20349c906000000126a42091a26c46fe74e28c3cd0c3e098236fa3f0d839f0c9e8f1b9ab749711b8f6555bcfaaed685fe65e158b2e4031968028c29e295b6f782b808dd456da69ec0fd4f400800000013cb8129e001700000000000013b183a9835564822fe239c1d51591d488a08a4200941f77624ea246674f80639cc2c1be4408de80286ea826372a0a9b83048da606e6cec11362c129b100180000006c280636080300000000000006bac1932b2c9171c8f4b8b00c5a3c872b0a850000000ab28405484442a060f14e2084a4e08c4b71c02282cd8ee39786da25e368c111b28078beb6a44e54422069b00e707106c91bc2f99ac116d9804751081e315c0771ea0000ee 0x14a52a4da369ca2709c2109c2108521284e10222600082c1084270b310842707e709bf0ace7acd5949bacd9708421294215ad6b26a5582da0000000000001084210842001080108401eb5834d4a4fc786df8f0dbb07eb000842155949dad6b26a5584244884290842508428c40026660000000082c01100b0d00600408001000008421084210971662108421080001020f5ac1a6a52760fd61084d8bc21000019e01084284a92a56b366ce0001333728e1c058b0099a2c187002109120841edd9b03f12932646d1b4e51384e10843887108521284e10220008421084e16621084eb383f384d9e2e95a46318c6318c270912210a4210942108c2000000000010842108420421084210801d6b3a49a72318c61084d88f108004210a72b493759b29ba521084210ad6b5a564e4164f400016000098000000210842108400210021084200f5ac1c934e499e9b699e9b760fd600108429cad2b5ad69593908489108521084a1084b882c00004ccc000000110130d1600c002040008000042108421084b8b310842108400008107ad60e49a72b07eb08426c47884000067804210b9642118c6318c006330b292242824480900180108421084204224dfa40679cae1006318c00021084211ed9edd48c631833cc42cf3a57018c6318ce51284210942508425084a1284610000000842109425cc2cc4210bca50626fc292aa52526097928402eb59ce759b2e7494a918c6318c63008400000000001800421084210800420046108400eb59de0fc1f8f0dbf1e1b66318c0021085d6b38c6318c63184e122442108427c421184000018cc000000b088098001804002108421084230b310842108400008103ad67783f066318c2109b17842000033c0210856b5ad6b5ac2122442108421084b88bb58b2ec5d8421022c408421084210971662108421084210bd6b07e0fc1d83f58421062f085e2fc18842148e8e39947328c3884aa3c842512212946318c3a8751c75287718ce1c71c1dc3825108421084210842108421084210ea38ea50ee319c38e3b63b871fc5f8310842e73953cd5ce544255138421084388421084a1284212842148cae319ce3194e328ce109ce5729ce1c5a84d4a4c4588108438c6709442108421084210842108421084e16621084e5729ce0dde539352931784210841b8c6778bf06210855554da349555442108429494c655559269cb4636932d3134d3154421084244212aa884212ac934e5a31b499e9b699e9b7e2fc18842154f3555572aaaaa21084a1085255512884aaaa6b1a4ad9328853aac934e4a896a22c408422c63595442109512251084210842b0b310842559269c950df288f10842107631ade2fc188421585e765e7554d54ca359555442528421094c655554d4a4ec6358b2c2cb154421084210915859884aaa21084aa9a949d8c6b78f0dbf1e1b7e2fc1884215555551084a1085255328d610a7550000000055108421084210842b0b300554d4a4c5e10842137631ac00210855572aaa79a884aaaaa255551084a108524caad954ca358429d4b2d554554d4a4c4588108458c6b225544aa210842108421085616621084f9550d55352931784210841d8c6b78bf0621085ca232e8da34842557284884212ca46318da9395d24d3968c6d38b70e73812884210842108421084210842109cae9269cb46369c7b9b739cdf8bf0621085ca210944e10842149cba968c884e72ba49a7211621085a73b42510842108421084210b42cc42109cae9269c8478842169ced78bf0621085ce554f3739ca884a2544e108425084290842109c2108421485232b8ce348c6739c6718d27084e72ba49a72939c38b9022c408421c63384a2108421084e12e21084210842108421385988421395d24d3949ce0dde9384788421083718cef17e0c4210a11914944dc9ac692a9913949aa4a99649a7255b18d6716e108425512212212a2108524d392ad8c6b383f3bc5f8310842a99c6918ce719c6ce527394e53b31084e50842109319d24d3949ce938c6739ce708421084270842cc4210842442108429269ca4e749c6339ce73bc5f8310842e13a4e12251084e718c64c884e739393a49b9498da4c2c716e1084891221261f937067ba621c9a9d31393538b9b8c61093509c98ce001084884e6fcdca6a2109c9b9ce738c63264424dd24d4e539ce4c67165858e7cb70842448910bc1f83707e767729059716a5495c63084e7dc98ce7016e1c0025130432e0b01084884225cdf9b03f1cae3194ce358d6108527294e9298c633972b8b2ec6359c58596e04251084210842108425108488421395de0fc1d8c6b3bc187ef383f17e0c4210a94a5295421094421265718ce918ce919465395ce738716e14a529c63384a2108421084210842108421084272b9ce736e3dcda94a538c673e5f9f10842a52946318ca3194a52a54a1084a918c632945be5bea5294598cfa94a145a810842108421084210842108421084210bc1f835294af18c1a94a0d5e529f2fcf884214a521326521221288465d18da518da51a4690ea38ee1c1c71c94a52d18da12884210842108421084210842108751c770e38e38edca52968c6d1e59e1884214a5291b46d18d231a5293265210852518c634a458e3ca52968c6d4a52245c8108421084210842108421084210842108f1c70e5294b4636a529072f4a479678621085366a632a8846318caa5ca952654a9552e5541623910842109109507e52e735532a98c632aaaba4e5695a92884aaaa5966318ce738716e15442108421223084aaa21084abe0fc198c6339ce6dc7b9bf17e0c4210aaaaaa88421085a5366aa6358c6308465572ae544a6554b2c4588108418c632a2e55510842108421084230b35448944210957c1f83178421084198c632ae5cbe2fc188421653666339542118c6318cad26a5294a55294a9495a4d4a5282cd0582108421084211b4a0fcad6830f5ef6b2994e5284ae1084a128421285a1284a1285a53264c6118b1416a2c102108421084211859f94a0fc21066b4eb398ca6118c63084aa634f29d5a56a424421096759cb2cc631a79e72774e094421084210842328842442108429d67f07e0cc631a79e76e774edf8bf0621085cae109544e1084210b4632a9b3318c6108c6319c9e9ced384272ae5716588b102108318c6d39c38bd02510842108421084211859884210842108421395de0fc18bc2108420cc6318d6d39ce0c373bded3bc5f8310842b0bbd18bab29c6318c6308c6339d66cb9c2118c21084210842118ceb59c9a94998c63165859608421084210842108c210842108421084eb59c9a94998c6378f0dbf1e1b7e2fc1884215594e1084891584212842148c6b18c6318d998c6b08467394d9538c63085631aceb59c9a94988b102108358c631956b162d40842108421084210842118598842108421084213ad6726a5262f08421083318c635956b076f2ade2fc18842174ad2318c6318c6309ceb365ce10842108c610842108c675ace9269c8c631938d3134d304210842108421084610842108421084275ace9269c8c631933d36d33d36fc5f8310842e95a42109122b084250842918c6318c6b18c6cc42339d26cc9c631842b18d675ace9269c84588108418c634ad62c5c81084210842108421084230b310842108421084275ace9269c84788421083318c695ac1dbd2b78bf0621085555554421284a1084a10e25094651b429c00000421084210ac2cfca507e109b9a4aa94525089282e715555358d655559295253195554000000015442108421221084aaa00abe0fc1d8c6b78f0dbf1e1b600210855555544213e2108755358d610a75335500000000554d5544aaa244aad9532a2aa210842108421085616600a8912aaf83f062f0842109bb18d6005437ca210858c3ac84028c652c811108423eb3ebc61d642128c690a67200072428d062448090028842108408449bf480cf319cae100a3194a0004270b3108423db3dba5729c0257084250942109421284a328da3184e5082a80cc004210842109c2cfca507e109be57195c6719c212ab9ce9394e53a4063000a0580000082894421084210210800001caef07e0dc6339c7b9b739d5800842172b842551384213e2108cae338ce109c0aa66160000000038130001000081000e00c0a8944210842108421084e166000025c042072bbc1f83178421084db8c67000019e01084292524a549319001224f6cf6e6998c21494a9263299980016163872885960c387000002109120841ed9ed81f8cdc68cf304239cf39cd13819e798582341987ecdc8e7380161fb9bb9e42c3f526a4cc6328c9b95c2129421084063000009800000000842108421084084200000f07e0d35293f18c1f8f0dbf1e1b6002108549a931084891084250842918c6519310a3001333000000001c2201602000102002c01800108421084210842108425c5980002041e0fc1a6a5262f0842109bf18c1800019e010842e252129252a498cb81370000842449ed9edca463085252a498cb804ccdc16003944cb160c1870e000004212241083db3db03f19b8d1b419e6583b408d191ce79e8da1c680332ccf3ccb3408d1b41987e9c9391b46d1b46926e4d4d4dc21084214a4063260000000000000210842108421081084200000f07e0e49a72d18da4cf4db4cf4db0010842b4ad2108489158421284214adab6a5a34842b0000000000084210842108421084084016b5ad24d3908f10842137ab5b40021085392721084891084250842918c64cd210970b000013330416000000384404c04000204005800c1800108421084210842108425c5980002041e0fc1c934e423c421084df8c60c0000cf00842152baca012d8421284a1084a1684a1284a168c6318c61180000004210842108c2cfca507e109bb5256952eb59c6318c6318ce759b2e7495a56a4021000000001800001084210842108408c21000003ad67783f066318de3c36fc786d800842175ace1084891584213e210b46318c6318c211800000000003198e1101300010180042108421084210842108c2cc000102075acef07e0c5e108421366318c000067804210a10912210842108c6318425cb2cb2c458810841663084210842108421084212e2cc4210bc1f83f07e0c5e10842107e3183f17e0c4210ad652acb232c94a007292146831a340387000210840b300566fcd81f8e572a4a918c028c00210847b67b79534cc8c6328c00e50c0060c0485060c00842102cc0178c66c0fc792a80a388280ea38e61f43987d0ea50e280000000025108421084210842108421000ea38e78e38e38ed8ea50fe0fc180084214d34d53cd534d5553efbea7d3529314000000001caa02850003800480501601c0009442108421084210842108402cc0005e50d4fbedbfe5369a949f83f06000067804210aac8c692280084211ed9edd949564a3494002c162ac851a341834680b0000842102cc01076b37e6c0cf2a9946929a4a000ab21418b0060c018b060c00842102cc0158c66cd6033c 25 33554431 10 1023
def hc_87_2 : Nat → Nat := uH 0x803d98df8c20d7ded10df5c47c7c24535f080047bf00c1e7fdf1783f701d3d74a73f0415c7edf570416e9b8e6086c1f869aa6187684c93194f70f64d31a98e613b623957d7ff23d5d0fbb573b0235bca4896b5cf3596c5ad60814c560088152895e54261f000000053fc0a94f5826534b22d4c882900000014b8042515961d434c8650c70314280274f734b5341a6d4cfe0213260664b964092cf05a4b100b12bc0204ae40312b4c114aa50b92910610000001287c254a1901927f81b48fe4011f15394678535195822000000118544144477390f307b41f575d07ac0a419814d044c85410204503e00a40ac13100b47f3e9f638fa540a3e43148f8b0173db11ecefc1c139a8920e1c936386a020e02c5f36c6514d44db332a49bcc8c473313f3c8bff1432eb152cb445a02a9b9d8a331cf26cb8049a7c2c26680dc8e16e321d96b07f66001cddbf06a9a3717d3b4c5f1c0c17b3050562a29129bbbc42fddc0ec57e832de0e0ac77c022de1008481bc1d210006de1a81a5848053b56c14c40a000000014a009050b074000000000000013b01f03725e804fe33005d38800005d 0xaa884aaaaa2555554aac954429d55575988c210842b1946d25aaa2a88b1021081d4a1f4636912aa2551084210842d0b310842108427caa86aa217bc21084210618ea50fa31b5e2fc18bc21085529da52b5a36b5a71b316b4a5295acf5a308421084254b529ce73b5ad6b5a35a042108488421084210b4210b3108421794a0dce73b5a76b5ad6b5ad6bc5f8310842bb3ccd3ba598bc19f7673e6eb68427494652959c62f0619f12a884230ac2108c231a4a30a75cd1288c610846b18b05820421084210b42ccd6b185ef08420c336bc2fce4a528da3c3a51095746d494a52b52d28b4a568421221296a5a95a2f46b5a35ad684a21084210842108421084210842f287e5283d68ff6b5ad6b4d87ad6b5e2fc18842142513a4b210a5a51084210b529292d445884214a5296b5ad09442108421084290b310842108423d431084210a5294b5ad68f2cf0c478842142512a27094a212fad2aeb3108c21084216ada52b5ad085a108421084210b56d4b4a5295a56a4a96a22c408420b52b5ad6b5ad1a2f409442108421085a16621084210b425c421084210842f286217bc2108421061f94a0f5a0f5ad6b5ad061eb5ef6b5e2fc18bc21085566aaaa328caa4c99533a555461094da4c64c162169ac2108488488460cf321f9c63295ca56a4a56a463298421288424c6319caed6b468bd05a946318c2510842108421084210842108421395dad6b4d87ad1fed6bca5066318de2fc18842152b84a6cd4c6318c6318da5294ad18da72b8b528c631b5a35a04a210842108421084210842109caef294198da318dad6b5ad78bf06210854a718c99318d2318ca318c6318c6328c630842716e2d4a318c18b306318c6108421084210842108421084210842109c1f9de5283318c19bc6318c6378bf06210855655ad6d5b56b294a56ad6d36756b194a52b5210856b5ac5a95ab5b56d5ac58bd0210842108421084210842108421084215ad6b794a0f56b6b56b076f6ade2fc1884216309128e2708421c43aa389cab354c95255094631932610ac583858215210e21c421084210942ccf1c70c47f84210619e2a52946d1b42528ca526e1d1d4dc210842128c2118c2108458e3bea5295a31b4996989a698210842108425084210842108421084211e38e1a94a568c6d1e7a6d9e7a6d9e59ef88f108428424489ca5494a5084a9199269085252a46d1b423084210aca52b332952329458e3be22c4084214a5295234a448b31a31b4210842108421084a14842108421084210842108f1c70c423fc2108421061aa4a529469483978d2d18da3cb3df11e210855552ba928ca328b0b04a9ed9edd284254a75a9294accda368793964c952749caba529494a1dce0b2416084244884213833dd20fd2948489471384210e21d51c4e52952612b5a54a8c2168b070b04084210842128599e39e38e188ff08420c33c54a52b5ad3a74e1084210946d6b5a5294a5084210842528b1c77d4a52b45e8d6b46b5ad08421084210942108421084210842108478e386a5295a3f5ad6b4deb5ad1e59ef88f1084284244894a5284256b5ad08c210842d2a4a5294ace5264ca421494a9294a2c71df116204210a5295ad6b529489172042108421084210942cc42108421084210842108f1c70c423fc2108421061a94a56b5ad4a520e5e948f2cf7c478842152bad0009a9475287739ce00000005552ae95511091095108420055123a943b83f3ace75801544210aac8ca32a8c21266a000b2549932a674a99d264c88842108488499bf190fcd5555555295554752877cd6d3e6b6955400000001544244212aa88421002a8ea50ef9efb6f9efb760fd60010842aa29d54463084210842358ca349446308423594650000010842d0b3108421085ef08426c3b18d635bc2aaaaa25510a7551084210ac3a943a99aa800000002a895544895592aa574aaa2aa210842108438b310842005448955442f7842108426c31d4a1ec1fac00a86f945e10842a94e7294e739ce1f00001c660000280004083400a88408488421084000002cc7d4a7dce739ce73800004210ae15846ccd6ccb1618d008d1b35c5e0e961a17179beccb166b8aecdd6109ca4b02c11ad0599ae25c5e0c3f6d68d99b45b99b4a2f4fe97107ea57c42557dc0a5002bea53ef99fd3e67f42800020a0025108408420001084200f286fa94fbe7bedbe7bf5f83f06002108594672b8ca318400000b4210847b67b7e1679dd99959f8395c27cca588c61084210846328d231842328c00022021085a166210842f784213619e6307e142512a27094af884fa89c210842b3ea53e0aa66082c00007c00002c0400020400480501a001512884210842109f16621084000025c0420f286217bc2108421361bea53fe0fc1800019e01784210a52aaa5368da54cc0048953db3dba5084a948e6b1ac380028cc0071ca22870e540340e1c008424482107b67b607e2b08ca9666b6662c68d9f83cf3167a76b3ccd1a3dbcf3a3356c2128cf3f07cec215a4acf5a0ce317830cfcf41a3367e79e66d6a9946518ca3084e01466000e51418300634018d060c00842108408419b3cc07e2a56b494a56765b1a4a5294a10ac028cc002c1659451a341834680b0000842108408459b3db03f12251c4e108438875471394a54a84a368da7085604400108421084210942ccf1cf1c70c47f84213619e2d6b1b336b336a4ad27a8c419f4a529370e8ea6e01080071d4a5293327a4cc9e82c0001400000008421084204a1080004210800f1c70d4a528f3d36cf3d36cf0cf0c0047884215284254a75ad6b5a0001084893db3db84244894a5284256b5ad0b4210842d2a4a52940000000000210842108421084a1662168421001e38e18847f842108426c35294ad6b5a0011e21085eddd99ac2139467a17830cfca3395c6518c2100000021084211ed9ede62cfdbb8c213a4ace317830cfd6519cae328c63580004210842b367b72b84a3288c61084210846328ca30e6118c210842108c65194000000021084a166210842108423fc2109b0cf31833cc60cf17b77666109d256718bc1867e798b3ca3395c6518c21000084210847b67b7084891394a528425187308c210842328ca000000000010842108421084250b310842003c71c3108ff08421084d86a5294798c18008f1084284244894a52952109438e21084212a4a5294160000000028cc00110040a0d000000842108421084212859884210000204078e386211fe10842109b0d4a528f0cf0c0000cf008f10842ab2ad6d5b4652b400000005800014160010842108108421000008b5ad67d4a7f56b6800004210a0a9252a464c8220842156dd6dc895c27084210842709ca92a427cc632644630842b5811000421084210b42ccf0cf0c5ef08426c3f0a9f53efb9f5f5f70294006d1b4651b46308421084000000006800421084204210000842100783f06fa94fbe7bedbe7bede8c6d00084214212244e53ea7c427cda368423184210842b1946d000000001a330004401000081001201401600210842108421085a166210840000810783f06217bc2108421361bea53fa31b4000067805e108429101529d68da368000d09127b67b74a109529d68da3680003466e450242870e01c01a00421224108737e6c0fc5594e318c6318c600000c66000e000050180042108420421084000021d6b39f529f318c600001084295c210ac2b0842709ca92a427f5a74e84670842d5811041600084210842168599f6b062f78421361f855653fad69d3a7029401ad6b5a52b421084216b400000000002108421021080004210803d6b06fa94fe8fd6b5ad37ad6b400210850848912aca7c427f5ad6842308421085ab694ad00020b0000000034660880200010200240280d0008421084210842168598842100002041eb58310bde10842109b0df529fd6b5a000033c02f084214212244a5084b88421084a516588b1021082d4a2cb1084210842108425c598842108421783f06217bc2108421061f94a0fc1f83f17e0c5e10842f2551084a3891094421d475187d0e61f43a9438ea38e58e0e38e0ea50f673ac25108421084210842108421084210ea38e78e38e38ed8ea50f673ade2fc18842166210e2549466a10e25058833eb26b6cd5c9aae5728ced38cad394ab09caa2109425084210871084210a421094210ac272b9458596a135293b39d6108408b1025108421084210842109c2cc4210842108421395caf061fbca0d35293b39d6108418bc2178bf0621085ca23299318c272884290842108c272ba49a72318c6108422c42510842108421084210842109cae9269c8c631842108f178bf0621085ca2729544251084212e574ace948d6d38d6d395d24d39269a6265a659ceb0944210842108421084213842108421395d24d39267a6da67a6dd9ceb78bf0621085c9aadb3759355cae959d2919d6d59c99a5a1395442148421284214852108421262108421584e574934e524d3132e459ceb08420458812884210842108421084e16621084210842109cae9269ca49a61a7e927673ac2108311e2178bf0621085ceb365ce74ad210a5210842318c61084231842118c6319d6b3934d3138d3249a72318c610842108421084210842108c210842109d6b3933d36d33d36e49a72318c6f17e0c4210ba5691ac64c98c6d18c6318d63666318c63184e122442148421284211842309d6b3a49a72318c18b306318c210811620421084210842108421084616621084210842109d6b3a49a72318c19bc6318c6308420c47885e2fc188421585d97a35594e73acd97384252842108c6318c6308c6318421084275ace4d4a4cb2c2cb0c63184210842108421084210842308421084275ace4d4a4fc786df8f0db318c6f17e0c4210b18c9935956538c6d18d6318c6318c6318d63662709122108c214842128421184eb59c62cc18c6135293358c6318421022c40842108421084210842108c2cc42108421084213ad671bc6318c60d35293318c6358421062f085e2fc188421421395ce55a5653a4e6cbace5d65759d6759cae71762d670597673ac21288421288424421084210842109cae77ad6b59c1f83f07673ade2fc1884214a52132652122128843a8e3987d0e61f5294a43a8e3b87071c7252949ce7384a210842108421084210842108421d471dc38e38e3b7294a4e739c79678621085294a52932652108561c7b4a5694a5234ad234a458e3ca5294a52245c8b176108421084210842108421084210842108f1c70e5294a529072f4a560cfb1e59e1884215295425294a2108425cae5294a719da719da72b94a529ce70e2dc39ce70912210842108421084210842108421395ca5294e739b71ee6dce739f2fcf884215294a95294a50842b5ad65194a519565294a558bb59f516a14a50a529567cbb084210842108421084210842108421085eb5835794a52941a94a5583f59f2fcf88421759080368da912105108423eb3ebeb210ad2358d214ce44890003922428244809006830a2108421021126fd2033ce57080328da0010842108f6cf6fc952568c651203310a95ca701946d394e51284210942508425084a1285612841540660020b0421084a12ee16621085e5283137e149552929344bc9560102e5739caa21494a9395ceb3ac16d000a000280800944210840021002708420072bbc1f83f1e1d7e3c36ece758004210b95ce573aceb09caa21084213e210ac2055330b0000000041605813000d00600408001000a894421084270b31084210840000810395de0fc1d9ceb08426c5e1080000cf0084214254952b59b36004ccc1ca3870162c016683002109120841edd9b03f1114a9368da4410842adbadb 26 67108863 10 1023
def hc_87_3 : Nat → Nat := uH 0x854f16e11dcd8846d028000000846302a1138150000000000000844402a0bc553829616e0718d08001715fb093f7cb1845e7c6c0782c715dbd936759b56dd0997571ed8e5bffdee6d23b71afed286a4e6b5a4194866c88f99465af62c295d86a11a60e43117f6d095f9c0fd7acce95d0f6917021075a0880167c81659db05c00000059ba08565ec3f591619564181058bf11d613c70000000160f013571a4895c101656961b957f898000000157ac1354b94c94796d450b94b1399a534b7fb9d28397147d18f51e2448448bbf909b61e407b7c8f99a153e0c168f498e63bbd5a4edd4483a35500e4192f37127d0db184c36ab06cd94c58363b06000000036070d0d1b59a33404b4000000332905cc7a1412fc987cbe303d2f6b084bc744e2dfe47cb798180000000b6c8342bf66f0aac5452a91080a5713527308b09c402026df0c49b281526aa080998848266000895590a254205094443123686a4846e4d20393887cb90b1d716f46cc640197e6cc6230f216b47605399ce1390558450e4d0f2787036a57e0ae0b2429e8660760c6817d96a045169407827101cc0500001cc 0x2aa29a469000084211ed9edd555368d200b1982ac85122404802c008421084084072937e9019e495254946524aaaaaaaa92a4aa632aa9ac6b2aaaa8000202a884000210842108400abe3c36fd586df83f07631ac00210855514d234800042108f6cf6eaa52aaaa5552a80cb6328d231850000112a2cc4210bcadf94a0eabeaaaaa6556caa6b1aca16aaa0aa0058cc014555550555507000b0028955459884210842100002040f9556d57c1f83b18d6000033c02108555555555555b592d55154b2ec5d944aaa2cc421084210842109f2aa1aaf83f0760fd6f17e0c4210aca4a210910944212a54a1cc3e8730fa1d475294a1cb1c1c71c1d475294a2df2df12212884251084a1084210842108439e38e38e3b63a8ea52947867867967be210855252ab35529510eaa21094212843a8ea528750ea5294a50842b09c210ea3a94a143a85294a548421028c416f96f89442108421084250b310842108421084210843a8ea528750ea5294a508428c518847867867967be2108555555552aa884aa3987d0e61f4a5294aa3c63838e38a529567cbb2a884aaa894210842108421095473c71c71c76d4a52ac19f63cb3df10842aa6528c611842118561084aaa12aa8c211ac2318462c088c1084250b310842108d6b1851c6235aaa84b252959885ad08d18954d25294a5084216b42d4621094446682c50b3108421084210851c620f5a0cfd55555551284aaa9294a50842b0a31095400000001544a1662108421084210801554a5284213628c42b067d8004210aaaa555566a255551284aaaaaa9294a50842b0a31094b2d554555294a10840a31167cbb225544aa250b310842108421084210849eaa86aaa5294210a3146215833ec7967be210850843b26521d94965272b9c61ec399d6946e9395ce2c7072dc4a38e45b9c21288421288424421084210842109cae77870c7f3839471cbce707e2fc18842158759195295946909caa2108c23084210ac2b0842109712e6b654d63484215846108b531762c5989172108408b11631ac2510842108421097166210842108421084210bca198fb0763cc1c83f48421062f08563066b07e2fc18842161185a12e79e79e62cf336799b3cc5999bd54c882ccf3cf3d0b310842cf3cf3107e1679e79d555555949555442d684210a5a1e4aa38e383b872438f2d39da5555109510842108421084aa38e3b63b871e438f2d39daf17e0c4210aae846573168c24d2d494ad2a421085ad0b51884251059a0b342cc421084210841f841eb5a0c3d1e7eaaaaaa8b425cd565a1e4210b423084ab2554a8912aa2555556438f2108408b11a2f4a896aaa21c59884210842108425448944210956438f2108418bc21683f6950d3d7c5f8310842aaaaaaaab292a98c21084211873495478c7071c72438f2b18d65510955510842108421084aa39e38e38e3b721c7958c6b78bf0621085554aac95544aaaaa212aaa88712aaadf998734842158461092d55156438f2108408b11631aca212aa8975510e2cc42108421084210842127aaa1aac871e42108317842b18d6f17e0c4210a23494655308c2108c2b0842d097344a2318462c082c108421c59884211ad63083f08d6c230b425cc463095d685ad09731059a1662108420fc236b5ae210852d69759e843e842d684210a5a5288bd17a10a42cc42108420f5ad07a3cfd6b39495216a31662e1685a5d67a15b5294842d6842109445e9f2f421084210841eb5a0f5ed52a84e51084a15944a54a10b42108b57d4a5284210a3169f2f4251084210842108421084210bca1a94a508421683f69f2fcf884216512a4a96975989136d084296a392de1668bd0842168421085787ebc3d6b41ebda8ccaa210eb2d2a528d5295944212884265a8e45ac65c6471c64a38e5a2f42510842108421085188421084210842f28719f1b719f1b728e39683f6bc5f8310842d162cef044666214627f37c5a105e810179f1084296b4211621485988420f598b85a168422c4210841e512a4a90913785821085a1085e158833e51685a5d662d1856d4b5ad484210b5a1684212882cd17ad0b31084210842106188375e3f59e62e1685a5d67a1785ed08b1084217b2895254b4bacc48917842f6af0b04210b4217ac419f28b42d2eb3168c217bc2f6ada968fd6a421085ad0b421097da0c41668bd6859884210bc21085d64272a8842d0acab7e72d48421684610ad294b4a54a421084216ac21084212a5ac8b9084204588d17ad16165e812884b8b310842108421084210842108421085e50e41fa42108317842d061fb41e8f0c30fc7fb41f8bf06210854a528ca91c4e5122709cad8561084a16b4c990b4611658111821084a166210847dac18a38c51b8747637294a50842128c215b43e842948421094a1294a2c71df8cb7c8e37c5294ad16f965e8421084210842108425084210842108423c71c33cf8db3cf8db5294ad067e8f2cf7c4210a94a50a312244212856d0fa52a59a94a50842d08c21294a95294a5084a549458e3bea529421081462345be597a529428b5021084250b31084210842108421084210842108478e386a5294210a3146216833f4a528351ea51e59ef8842152ab31c4e5122508c655294a5513b42b5842118c2b18464c8efaa42230b0b04250b310842108421c3147188f0cf0e94a51b46d194a1295a769d3ad084a30842108463084211638efa94a56b46317ad6b468bd0210842128421084210842108421084211e38e1a94a568c6d6b5a6f47eb47967be21085acf31e4a16a316619f94a4ca94a9294a5294270912210942128461cc6548ca5294a966210ac2308458e3bea2cc194a14a5295210840a3105966316f8842108421084210942cc4210842108421084211e38e1a8f328ca506a9294a508428c51884798c19e59ef884215a5695b56d4a5ab4a56b69b3ab4a5a558d290842b5ad69471cb56b58bd6ad62c5e810842108421084210842108421084210ad6b5a51c72d5adad5ac1dbdab78bf0621085d64631a52729ca948c65308c63184251084b95d28e3939ce1c5b8318c6122442108421084210842108421084272ba51c72739cdb8f7366318de2fc188421631932674a391946318c6918c630842318c6349c5b8c598318c4a38e462cc631842108421084210842108421084210842707e71bc6318c60e51c72318c6f17e0c4210aaaa4a909500108423db3dbaaa31a4211a499a80029954c99592a4ca64c888421084884f8c66d0cf6aaaaaaca4aaaa3987d0e61f521c792a800000002aaa884a88421084200551c71db1cf1c790e3cac1fac002108554636a52001084233757425d0e216b42309565a9295a5484210b5a16a31084a00001a16621084210842109bf083d6833f554712a99469084211ac231842128e6108d6118c25000001c59884210842108426fc2b18d635aaaaaa88712ac871e4210ac21094cd5400000001564aa951225544aaaaaa2aa21c59884210842108420054489556438f21084d8bc21583f580150d3d44210b0ac2cf32c62c082c6cf3bc8cd6727c4e121620d682ccc3f6b58d9e7a8f527c2c3f46e5510875904a400b19a3d4668f527df90a028092000012880042004f88421084200f28719f1d719f1b727df9783f060021085ca2d0adad3e216b42338565d494a9084216b42d38421000008e859884210842109bf0b419facdf767ca25c4652cca34842108d188c6108467cc211ac23184000220f8b310842108421185189bf08f3183eb2139544212e2593efc8421584e108154cc900000000058480500204000800000544a213e2cc421084210842100002041e50e4fbf21084d8bc21783f06000061e0210855230ac2cf33163390a38c59e7250ad18b30bd06619f4a52a471394489c272b18a31084a11b46d0ace102228001084250b3108423c33c313718b5ac6cf3d47a9282c33e370e8ec6e5294a01080071e3347a8cd1e94a528000000500000842100084009421084210800f1c70cf3e36cf3e36d4a528f0cf0c004210aca250a4a52b310b5a11a31597469294a5284210b5a16a31084000000a166210842108426e316833f5213a3167ca2508ca651942108468c46308425184234623184000000a1662108421084230a3137188f3183a5294a90a3122442128438ea9294a508428c518840028cc0000000011014020000010842128598842108421084200004080f1c70d4a5284213628c423c33c3000030f010842a37082f3cc4b90bcc419e6223274620bcf393e2d082f310661faa92a4e51384e108428c4212e2318c99158c204400108427c59884211e19e189bf0b312e7310a3149f0fd1ba3636373f27e41290018c210846308467cd2000000000001084200108010842108401e0fc1c67c6dc67c6dc9f7e5e31830010842fc9f909c24488425c46319f34842158461080000000105805998002204805002040008000b001084213e2cc421084210842100002041e0fc1c9f7e42109b17842f18c1800018780842142949932368da000719b9470e007070242870021091208439bf36067952549ca2709c210ac2b0842d0b5a74e85a3081100042109f166210847dac189bf0a3759b31b9f95a4129005b56d085ad084214b4fc800000000002ccc1084200108010842108401eb5838cf8db8cf8db93efcb41fb40021085f95a4212244216856d5b52d3f21085a1184200000000000b330440900a0040800100016002108427c598842108421084200004083d6b0727df908426c5e10b41fb4000061e02108529084891084b8a5210842108b2e45c8421022c416588421097166210842108421084210bc1f83907e908420c5e10bc1f83f17e0c4210a94212a539ce739ce700387000e122808a5c17a1c00842442112e6fcd81f8a52a9c210954a529cb95ce529c6759c6759cae2d4a716165b82dce10944210842109442122108421084e57794a0dde0c3f79c1f9ce0fc5f8310842a955555544255555294a4cd6d266b69554a52932d3134d32cf976551084894212aa88421084212aa94a51e7a6d9e7a6dd833ec7967be23c4210aa894aa2318421084211ac65194a23184211ac6529608b062c61084250b31084211fe1084187631ac6b1e2aaaaaacd544252a8954aa8842108565494a5295d2aaa22c4084214a529512d6cf97655108421084250b3544894421084210954423fc2108421061a94a52a1be5b067d8f2cf7c4788421529542109554a1221084b3acea529539a7d4e69f53acea52953cf393a7385be5be25108421094a2109108421084210a759d4a52a79e76e73e76cf0cf0cf2cf7c53884214ae5128caa118c210842108d65464c23184211ac6518c5821522c305984210942cc421084211fe1084186798c19e63c509544e5295559884a529421495513842108565294a94a5a94a45abe22c4084214a5295294a448b905be5be25108421084212859884210842108421084211ea18847f842108420c35294a94a41cbd291e19e19e59ef88f10842ac2367251a4a34f99ada367e0f5ad084aa27084210ac2b0842108c23294cab494a348425d759aeb4a88463084210856b1946d16a62ec58b3022c408420b52b463684a210842108421084210842d0b31084210842f2866f583b78c1885ef08421084187e5283d1833683f17e0c5e10842a974a56b46168da5552b9748ea50ee739dad6b4a2a212212a21084aa244210875287739ced6b5a55f17e0c4210aaaaaaaa94aaaaba52b421084216b4aa3a943e9da35ad1ad6b4aa212210955442108421095475287d3b5ad6b4deb5ad78bf0621085555544aa214ebacd54461084216b4a569544aaa244aac9552ba554458810840ea50fad6b4a896aaa2108421085a16621084a8912884212a885ef084210841863a943eb5ad2a1be5f17e0c5e10842ccbcbaaaaaaaa52aaaabaccca368c61084210954752872cbbcbcb3463695442122d084aaa2108421084aa3a943f8fbdbbcf0dbd18daf17e0c5e10842 26 67108863 10 1023
def hc_87_4 : Nat → Nat := uH 0x9b4f65e6974f299fe17e66e44598715225b4d9e95b24865035a591dc8c6440cd990ed05a43441c8f356723c90118f0208a3b28388ca788e3214228aa777a21ce3486b86ee122e2d830162a0541b17f8971df78da67c2e6d5ebd13a7805bbdd49adf7398639c721d0704e5e9b9c5dd6d63439b139156972b71a3d07e67cb4a59a413b65604c189eee5609f7717c5d885d4075d6d0dfd5860b8d597a025373bad45b2074e6cc01319a064983b8d244472482b3991c451a44ed891126454448006510786243393950cb40c42cd18107ccda405866cf912143ddf194f6b8313d431acf0e9093c34018f048223c0c018ee50783aa53bce49580377e69cd7e1863468640c9062731dd190c404dc2f6b658b97d0c2c4885caf8c652afe394a5859d292e0cca0392025f785c91d18322b470083e1bc1f3171c75adc61bbd6b868c98b17d19845b88ef16c90645a782b14d5724526c3a148505850f44811eb94843c4fa109a15c3e98f40f9703c3e200f0e245903734570d8f0f832e8d50b036dc2818fd09822102230f607205b0174150054921c13248003a04a40c887e01e64f00001e6 0x294aa14a528009972e71946518ce918ce90a00000000395ca5294e13a7709d3b8c6700395ca5294e739b71ee6dc63380230fd1d555381366a6318c632a972aa54aa972a549900004112853ae13e52835b7394ca00c9900014e29cf6cf6e9ca918c63006798854a95ca70194d998c6318c6329ca5294a52a525394a5294a000000250a714627794a0cd6739b0ddef374a52a54a5294018c63294632a46328c65000000000000471a84a5284a5d4a528c68c03c1f835794a52941a94a578c60c0230fd1e318c000016660008800005802ebaeb98cb8000b820f07e0fc1f83f18c1800019e0f07e5fc9540551c4140751d461f43987d0ea50e28000000003a8e38871c710f38ea50f673ac003a8e39e38e38e3b63a943d9ceb00783f2fd67d6d9ab9f55cae519da7195a7295614000000001c663954050a0007000900a02c00e57284faef894fbea53f673ac00046081cae53efb6ff94dbea53f673ac00006783c1f9792cb352882e92a019c6949ce90000038cc538a792f23c33c3907e96b35c576b312fcaa394aa0a002e574ace948d6d38d6d0a000000000e331cae93efc84bce25f5673ac00e5749f7e5e3c36fc786dd9ceb00783f2f99a0ccd06629f3d6608900a4b8b9f55b66eb3eab95d2b3a5233b4e34b4280000000038cc72a812014048900000160072ba4fbf290975c52d59ceb0000b82072ba4fbf297836fde937673ac000061e1e0fcbeb30d9e85d2b49ceb365ce948000c6318358d998c630006318000000000003198eb59d27f5212f3e85ad18c631ac00eb59d27df978f0dbf1e1b66318c01e0fcbf4ad2358c99318da318c631ac6ccc6318c63000000000006331c220480500603003ad6749fd48c232e6118c6318c6b0000b82075ace93efc8c63366f18c6318c000061e1e0fcbf3acd9739565394a000318c6318000c6306300000000001875ace7c4fcfa16b4fa95a318c60075ace7cf7db7cf7db7d4a7cc631803c1f97c63264d65594e31b46318c6318c6318d6366000000000018cc7088060900a00c1603ad67184631846d3ea568c63180008c103ad671bc6318c66df529f318c6000033c1e0fcbf2b9cab4aca749cd9759cbacaeb3aceb08808280000395ce15ad613975d7b39d60072b9deb5ad6707e0fc1d9ceb00783f2f29485966b290802a03a8e3987d0e61f5294a428000000003a8e38871c710f3ca52939ce7000ea38ee1c71c71db94a52739ce003d33d794a52b4a5264ca405871ed295a52948d2b48d29000000000002638ebca52948525e4294acba76003c71c394a5294a41cbd295833ec007a67af4a55566294a540005cae5294a719da719da14000000007365ce5294a709d3b84ed39ce700395ca5294e739b71ee6dce7380230fd1d294a952956529405ad6b28ca528cab294a52ac0000000000016b46a1294a12975294ab47600f5ac1abca5294a0d4a52ac1fac01187e8ed6b5ad6b580000002ccc1100000b00b5975d7b2f600017041eb583f07e0ec1fac00006783c1f97a25708421084a50843ae21084ae6ab84210a421294212aaa2109c27084a70ee1dca70ea50eb954421022c429c38396a075287739ce573544a88421c4b88421084210842108421084aa210831784253870c7f29c3a943b9ce778bf062108544b955cc4210a521094212b842108429484272e21084aaa8842709c2149ce949ce739d272a8842045889269ca4e70e2e439ce72b9aa25442108421384b884210842108421084aa2108311e214934e52738377a4e739cef17e0c4210ac95cf357390f25550e3aa52949cd735438ea94a52739ce5cd731091084894421084210955438ea94a52739ce3cb3c31084292ca525d56521084b294a5234ad234a45aca5294a52245c82cb128842108425108488421084210847a87294a52948397a523c33c33cb3c310842ae6e6e6a94e55294a52ac9ce9294a52ac9ce939ce72a25cd7310910842108421084a5294ab273a4e739cf97e7c4210aa94aa5c421294aa5194a5195655294a516a14a505abea52945be5be244251084a21084210842108421095e5294a507e50d4a52bc1f837cbf3e2108572aa4a92a9a4694a4e958d23084b9ae5368d2716241608421084895d6b3a41fa4eb5553aca3194a528c674212a94a51946d2e6e94b1438b0a884210842f2941b975ace75a895c210842118c213ac21084aa210842119ceb3ac672b9aae10842758423184254ce33954421022c419ce1d630596e319cae6a8951084e15842108421084210842108425caa2108317842339d6758cef07e0dc6719d6f17e0c4210aaa8942129952c2c10842108f6cf6dd6aaa21395ccda3497494a94a5296b5274a5259058e0b110848944210a41fa4eb39c186e3cf7551094ca36b4ae6ad26a5294a52b5a74a5294a58a34162a21085a14e21085e528376b5a0c3d7bda89544210953894a1084a21094a1084a50b46119553841616282d4b9a251084210841f85e5283a2551084210972ab9884216ac211842739ce5708421085ab084e5c42109c9b9ce739555108408b10596e739ce738716e15cd512a21084210842109c25c42108421084255108418bc21783f06e739ceb39ce7061b9def39de2fc18842172b9d65d59da76a7b2aeace9694e56a42109cae2cbd39dad59c38bd02510842108421084a210910842109caef07e0f4e76b56706ef6ade2fc18842157373734c631954c67299ce738c631954b2dce739512e6b988421084884210842318c6306abe0fc1b9ce739de2fc18842153194cb9946318c69395c2108c65318c6318b30631872b8b2cc63184884a210944210842108421084211bc6318c60dcaef07e0cc631bc5f8310842b3ceb3ce214a4210843ac842108c6108cba168d29dd393cf393acf24d3968c6d09109442128842108421084210a774edcf3cedceb3c934e5a31b5e2fc1884214e10eb210852128421dcaa670842108463084e10842959c6570842708c213937666749c6739cae108408b1124d3919ce1c598718ce5166a212a2108421084210842108421084e5708420c4788524d3919ce0dde339c633bc5f8310842b3ceb3ce21084a3084a59c429e4210853acee12ad397393cf393ace9a949d9ceb09109442128842108421084210a73e76e79e76e759d35293b39d6f17e0c4210ab094ae108521284272b84216846109c9bb353ad6739554e108421094a10ac21084a73ad6b395c21081162135293b59ce2ecab58b16a1459a884a8842108421084210842108421395c21083178424d4a4ece75956b076f2ade2fc18842152cf3ceab3e84252842108cb39942718c21084214eb3a6a5273cf393ba71c633848910842109442122108421084214eb3a6a5273cf3b73ba76dc633bc5f83108429c233955ce10842109c2118c21084a57084290942129d632b84213846108ce719ca7393766e5708420458871660ce709a949b8b319ce5166a212a21084210842709710842108421084272b8421062f084ef19c673834d4a4dc633bc5f8310842b3ceb3ce2148c210843ac8429d4210853acf2b3853a7393cf393acf24d3959ceb0910944212a8842108421084210a73e76e79e76e759e49a72b39d6f17e0c4210ab087590842909421395c210b423085275ace4dd98ee55938421084294842b0842149ceb5ace570842045889269cace75a56b162e428b351095108421084210842108421084272b84210623c429269cace75a56b076f4ade2fc1884215551006d1b4b2242aa210847d67d755442338d215ce448900092144890120070e151084894108937e9019e44aa21084a9c4a508425129420139c2328ce72840142aaa0335cd128842109bf0bca50744aa21084f884aa2109c27084e739c8aae6000082c02c000140408001058009800380702aae6a8951084210842000012e02102a88426c5e10bc1f83739ce000033c0210851ac2cec6cc44e18b19d854f38b3cec2b462cc2c44e38338c41fad6b2da4a548424ccc001ca166831a34038700021224408459b3db03f19e772e518c610000210847b67b7331a8c690846004ccc0c0060c03942c306011221081083cc66c0fc59e750108425284252cf39a7d4e69f53ace9a94980000a000008280a21084210842009cf9db9e79db9d674d4a4fc1f830010842a312953108521284251084210935293140000133300001caa008100020002c2c038005166a212a2108421084000081079431084d8bc2126a527e0fc1800019e0108428d61676366e444e18b1636761676453ce273cf3b0acb8b3722272ce7066b883f5ad65b494a9084e01333007058e513346830e3468070e000424488108b367b607e33cf33679bb3b9718c6908400180042108423db3db995d46348423003804cccc0060c03944c3160c1804488420420f319b03f1080010a4210879321084270e3ba4e74800010000150438b310842108421084200108423c4e1c774934e4e739c0021085679d4042948421087594e69f539a7d4eb3c934e400004ea0000020a02a8842108421080273e76e79e76e759e49a72f07e0c004210ab087590842909421596c210b42b0852b5a42800000000a2cd44254421084210802cb61084d88f10a49a72b5ad600108429c21d64210a4250846570842708c2119c690a0000000028b351095108421084213801cae1084d88f10a49a72718ce00108429710eb2108521284251084210a49a720b500000001333001c2a880204000800130b0038001459a884a884210842100002041e50c4213623c429269cbc1f83000033c021085cae100691a4000210847b67b7d272c842368d200719839490a2448090038010912204224dfa40679679d42754f29d53ca759c42108c6108cb399c6700000a000008280a21084210842009dd3b73cf3b73acfe0fc1b8c6700084217094ae1084254e2528421094a1009c611946918c0000008b344a2108426fc2f2941ce1395c21084f8846570842708c2119c670a0000000e33001caa008100020004c001c00a2cd442544210842108000102072b8421362f085e0fc1b8c67000019e010842d2e8401b469000084211ed9edf4b4b2108da348001c66e524485048901200b0021224408449bf480cf2cf3a84ea9e53aa794eb38853e84210a759dd6758000050000041405510842108421004e7cedcf3cedceb3f83f07673ac00210854e554b520010ac252b84210953894a1084a21284a50805a308ca35956000000459a2510842137e1794a0eb09cae108427c4272b84216846109d675850000000007198e5500408001000260016005166a212a21084210840000810395c2109b17842f07e0ece7580000cf0084214b8944210842510842108b5108408b10596596a2cd4425442108421084210bca188420c5e10bc1f83f07e0fc5f8310842aaaaaaaaaaa8cab28ca5294a52aa94a145a85294ab3e5d9544210842108421084210842108425552941abca5294a5283b07eb3e5f9f10842aaaaaaaaaaca52948d2b48d292aca5294a52245c8b17655108421084210842108421084210956520e5294a520e5e94ac19f63cb3c310842aaaaaa631a46518caaaa98c631acaa6318358c1659ac6318caa2108421084210842108421084212a98c6b1ac63783f066318c6b78bf062108555556dab6acaaab69695656a4aaa965ead6b17ad5ac58bd0aa2108421084210842108421084212af83f07ab076d5b56b076f6ade2fc18842155555555594954c655574692a8e58e0e38e4871e5a31b4aa2108421084210842108421084aa39e38e38e3b721c7968c6d78bf0621085555565ad2aba50ea90e3d956438f230e38e59b56b695442108421084210842108425590e3c8c3863987d5adaf17e0c4210aaa95592aa8eaaaaa632aaac871d4c6555b2a8e3db330f21cc3d92d55156438f230e3839662c635944aaa2cc42108421084210842108421093d550d56438f230e3863f8c3d8c6b78bf062108554ca55555298c398ca366654b318b0b2c65459884210842178c60cf0cf0ec2d3676597636718aaaaaaaa94aaaa61d48e398caaaaa3a94396585965ac6317655545988421084210842108421084212a8ea50fe3c36fc786dd8c6b78bf062108598598b56c6ce3154bccd9732c0c650bb1b38c55531955555555552ab25555ac9955b2a9871cc3aac38f6cd2d55154b2cc18b075287b58c62eca25551662108421084210842108421084f9550d57de3066f0618ea50f631ade2fc18842155349465530e00399802a9830062c01618b060c00842108408419bb18d603f1564a549140042108f6cf6e8e3aac94a928e660000aa59a341834680b00008421084084076b367b607e356368d6aaaaaaa52aaaa9ada35b43a943aaaaa803a0002a884000210842108400abe3c36fd586d8ea50f60fd60010842ab252a48a00210847b67b74d2528d600108c1d52c931955532a994692632a651805000112a2cc4210bcadf8c60eaa95592aaaaaa8ea50e8aa8aa0e660000a2aaaa82aaa85858000144aaa2cc421084210800010207caab6aa3a943d83f580000cf008421553494655349400073305530600c5801c3160c18010842108108337631ac07e2ca4ab252a4a2a800084210841d8f6cf6eca4ab252a4aa03998002a8e68d060d1a02c000210842102101dacd9ed81f8aaaaaaaab292a8e61f43987d4871e4aaaaa00200aa210000842108421002a8e78e38f58edc871e560fd60010842a3aab2564aa38e38f21c792aa2a00802884210810e2cc4210842108013d5471c71e438f2b39d60010842a692ac94a928aa000a21084211ac7b67b74d2559295230e0002108421183b367b754b24c65554caa651a498caaa9954c39a4085aa0000089516621084210847ab7e3183b18d6a692ac94a9280028842108460cf6cf6eaa95592aa655554c39a4a16aaa0aa0200a25551662108421084009eaab6ab21c7978c60c004210aaa95592aaaaaac871e4a16aaa0aaa000e6600a2aaaa828aaaa0e162c00002895545988421084210000097010813d556d56438f2b07eb000019e010842 26 67108863 10 1023
def hc_87_5 : Nat → Nat := uH 0x896403e257806892f0be24441e890503224080388dc09a1c7dbd84e98da0f950483db02a0f041a81fe70dff1e377f6418df935177d623adef598c7a296b5e72061797b135e258e5786c0a9db798e753d685d06d227252725c006516f093e1b84cf66c7a665aaf9bc68868e19e0904670020997ed05647d5f98a95d8618b46980357e5e257a17498ff5c144496ca0ec5a8828169dc115a3e0e5650cfb592c05d643c1d58f10795d45a057260ad5b5c4f00000015b0c14564b1e1586c3055313a954ac06551006d51f892544e0c14d74f1513c88540d5074e5278d301a4c4acc4e92ae0144a810dd298420488477518ea4a45074cd0dc197417a7d8ffa5913e2f6e8f1edb43b9c37cec54873a7f258e5412f37996dcd9b92b34cd684cbd1d9315a668c364812f94514b979362cb9694abf9bb294a6d0a1f4cd274e4bc96c99c23888a88ddc11236604488056520387247af17c1ce87506d5d91191e8e45e917a1600690542cf51373660457a150fa06f835c2300d450ac3478270b4376c243a3508253a41cccf2071208400000006ee090184cdb04945fc0bd99e01b74fc0001b7 0x67a0cf3cf30bd0067f720e19fc3baecc00b0cfa5294e1d1d728c00061cc294652800c6000140000000098e3c6a529498a39d31473a663460078e386a529479e1b679e1b6798c1801e99f1d294a9199269295230e652959994a9194a001466000000003844050482c018004c71e35494a528c2947211a4998d18000b8203c71c35294a34a4dcbc691e6306000061e07a67c729294a930f654a801466038e51071ca8e0e028d0600438a3171078e78e3b60679dcf0f21254a52ac38f65294a50e1d1d728c000a5000000a000000004c71e35294ab469d931473a628e7003c71c35294ab067d8f3c36cf3c36c00f4cf8e94a52a561c7b2a4a5294ace5264ca4a5494a5000a33000000000440506803012004c71e35294ab469da42947214a40002e080f1c70d4a52ac19f694a4dcbd29000018781e99f1d552a65194a8a0538a7adbadba529526d1b52529598f272c993a4e55d294a4a9294088a0005189c28c527067ba4dfa54013a752948952a73842739ce7022022609c2108421384e0f084db83f3a94aa7294aa53972b9c6759c6759ca50880828058000395ce12eb89cba94bb9cb80395cef061fbce0fca507e738300f07e5eacab5b56d594a52b56b69b3ab58ca5295a900000000000016b5aca56b56b6b42b2f616ac016b5ade5283d5adad5ac1dbdab00783f2f554c632914000538a73db3dbcf35328c635b3cc00c1d59aaa95553194652a9931955194c98c8020800318911853adf93cc60e94ca52ecf3a5738c65306318c6319d25294a74940045000000001cae5297318c6709d3b84e9c01caef294198c6339ce6dc7b9b00f07e5e94e318c99318c6518c6918c6318ca318c0000000000003977294b9846318465cc631801c1f9de5283378c6318c198c6300783f2f4a528002ccc00001100b000005d752975d700017041e0fc1f94a0fc1f83000033c1e0fcbca4aa02a54a10501d471cc3e8730fa5294a07501428028028001d471c438e38879d4a52938d38c00751c73c7ac71c76d4a528f0cf0c00f4cf8ea4a5566aa52a3a8ea528750ea5294a52a40ea02850000000a330007550140a0b0038000751d4250ea1294a9294a5271a71800118201d4752943a875294a529523c33c3000033c07a67c754ca519554600505199830062c02aa83160c180158463589c419bb18d603f1554a553294a550519802aa8d1a0c1a340580023b0a3158d080ed66cf6c0fc5555555055543987d0e61f4aaa5294aaaa02aa8029001c438e38879d554a52ad1a76001cf1c71eb1db555294ab067d800f4cf8eaaa555566aaaaaa5294a16aaa0aaa0028cc014555514162c0000225557555294ab469d80009c1027aaadaaa94a55833ec00006780f4cf8ec3ac8ca94aca349735b2a6b1a416a000000016660039540306002c58002c2c5803060015730acbd8465e4bcac63580005c10794331f66ec799b907e958c19ac1800019e0f07e5ee79e7999320399e79e79a9830386cf333ccd9e6679aa8679e799a119e79e607e2aac94a928aaa0399800b42d0763db3dbcae69a4a54954073300551cd1a0c18d1a02c00028c5634203b5acdb763cf6c0fc5555590e3c95556525551f4380002a8080282aaac871e4e739c38879c710fa005590e3c9ce7387ac76c770e380783f2f55735590e3c9564aa955554001ccc0154142d555541c34580300aaa0a2a80ab21c79597b2aba2500027040ab21c79583f5956d3d40000cf0783f2f5554ca329554519a0000aaa28000c1801554a52ac63580001554a52ac6358000230fd1d55555594954c3980001554c39a4aaa0aa020038871c710f3aac871e5631ac0039e38e3d63b6ab21c7958c6b00783f2f5552aaca4aaaaab998734942d5541554001ccc0145555505555070b1600c180044aaaeab21c7958c6b000138204f555b5590e3cac63580000cf0783f2f9e79e79e79e60399e79e79d870386cf333ccd9e66798679e799a119e79e607e2a6cf3cf36caa0399e79e79aa8e1b3cccf3367999e7a2c0679e799a119e79e76b01f886928cb9a2a8000e66aa60c018b003862c183002b08c4e20cdd8c6b01f8b9aab98166660c1618d060c68b006841ad6b01f8ce4067254945e9da0b2cb6ccca494a92a00dad2b17254070059980000b42d597b076f07e0ed60edeb715cf3b1acd716b32c12fd6565525691954252b28b54a4a800085a80005998000000abc979597b0979c4be803ca1c83f4ac187eb07e3c36fc786d80783f2f9868332c16b38f32cd3b408d00ada1517a75329252a4a00b802ccc005a169b43c6659a76811a1596d9dad2b495c0166600e50b346830e34680b000597b1a10db6f1e06199e6a2f4eb2db3329252a4a00fac781c0166601e05a16b32cd3b408d0acb6cfd6b5a5692facdb802ccfc003942cd1a0c38f1e34680b000597b1a11d65655ce5695a52b295292a16a0001666000000395402c3458030068b0000000abc979597b584bae2b2e0002e083ca1c83f4ac187eb0763c36c3f1feb3600006783c1f97a52946548f664c87000146638e511c395b1601468b061c00ac28c8c41edd9b03f14a52ac38f65285294fb87475f70028c1294800002c0001400000002638f1a94a55a34ec989f9d313fa003c71c35294ab067d8f3df6cf3df6c00f4cf8e94a52a561c7b2952cd4a5294a54a94a5295250580000a33000000004405068b006005002638f1a94a55a34eca12975094a0002304078e386a529560cfb294a6d47a9400006780f4cf8e94632a52632a464c8e000a33001c7288a1c395b1602c583060078e4a14628c8c40e19ed9ed81f8cc733cf31f3d1b4019f9838019ff70e8ebee5294a518000c398d230000194a14a0b000000005000098e3c6989f9d313fa5294a4cc68c00f1c70cf3df6cf3df6d4a528f3183003d33e3ca52654a5294a528c398ca9194a52952cc2c000000005198000e110140a0b0018300098e3c6a1194612975494a529331a30002304078e386a3cca3294da94a51e630600006780f4cf8e94a951b46d2a59a943a9caa543a9ca8ea1d4a52952502200038710e27097129c3b871dca6cf5764ca43b292ca4e5738c3d8733ad274844041400001cae70875c7139792f27397007797ce77870c7f383907e979ce0c03c1f97b4ad2b5b56b5b5694b56b4a56b69b3ab4a5a558d29000000000000016b5ad25f52d5acbdb56d0acbd85ab005ad6b483f4b56b076f6adab583b7b5600f07e5ea4a5566aa52a3a8ea52b4a1d4a5294a14000000001d4750943a84a5294a55ad6b000ea3a94a1d43a94a52956b5ac007a67c794a4caaca5294a52ada1f4a5494a5294a90000000000005871eca1194612b4a9294a56ad6d005871eca3cca3294da94a56ad6d001e99f1da5690842448ac21094210a56d5b52d5a42158000000000042108424c42108421084216859805ad6b4934e423c421084dead6d00084214ad2b5ad695a40000016b2f25e565ec01eb583907e9583f5803c1f97aaa32a9946328aa0006b0b42d1ac7b67b79e6aa32a99463187cf300368518ac60ecd9edd54aab34c65554caa6519498caaa9954ca32810b540000004ab88c29ec6358f56cf3183b18d6eb231954d986318c631a52729ca94950001140000000072ba4bc8c6319c274ee13b400e57483f48c6318c1b9ce7361b9c7f9cd80783f2f55554c6319564aa9532aa0200a88aab21c7918c632ae44a00ab21c7918c632adae500f07e5fac8caa18c6318c6949ca72a523187140000000072ba4bc8c6319c272ee139c00e57483f48c6318c1b9ce7361b9c7f9cd80783f2fd2918c64c98c6328c6348c6318c6318c631a40000000000000397749791846318465cc6318c65c01c1f9d20fd2378c6318c19bc6318c60c03c1f97a929559aa94a99473194398ca5194a32a428000000003a8ea12875094a5294a718ce001d4752943a875294a529c633800f4cf8eaa8caa6518ca00068c518a33067b67b75552aaab34caaaa99465285aaa82a80080225557555294a4cc68c013d556d554a528f3183003d33e3aaa6cd54c6319564aa9532aa0200a88aab21c7918c632ae44a00ab21c7918c632adae500f07e5fac8c6553666318c631a52729ca9495140000000072ba4bc8c6319c272ee139c00e57483f48c6318c1b9ce7361b9c7f9cd80783f2f4a52952318c6318c63194a72952a518c63194000000000000e1c77294a518c63284a5d4252801c38ee5294a318c65294da8f52800f4cf8fa49c8c6318c63184e12244214842128421184000000000021084270842108c2cc4210842100383f3a49a72318c61084d88f108004210a52318c690000002ebc97918cb80783f0720fd2f18c180783f2f294a4160000166600088058000002ebc9792eb8000b820f07e0e41fa5e0fc1800019e0f07e5fc954051c4140ca398c3a8c6528ca30e28000000003a8e38871c710f38ea50ee319c003a8e3b871c71c76c75287718ce00f07e5f9ce57f35739532b8c6738c6538ca33850000000719800e5501428001c00240280700395ca13977094e7d4a7dc63380008c10395ca739b7794dbea53ee319c00006783c1f979d714e25eaaaaaca4000aa6b1a4aa632aa80282a8202ac9f7e425e712f3d8c6b002ac9f7e5eac36fc786dd8c6b00783f2f5fcd5555caa9ac692b64caaa00a88a58cc015554900a055505154b002ac9f7e4aae896c63580009c102ac9f7e4ab6f96c63580000c3c3c1f97aaaaa50002a98caaaaa651acaaaa02a8016407c4fcef89f9d55f529fb18d6007cf7db7eb7db557d4a7ec635803c1f97aab9555fcd32ab655328d650b555055002c6600a2aaaa82aaa920140580112aabaabea53f631ac0004e081f2aadaabea53f631ac00006783c1f97e51ca550500132b8ce348c6748c694850000000001cae93efc9c274ee13a7718ce0072ba4fbf2739cdb8f736e319c01e0fcbf3955fcdce72a65719c6918ce718d270a000000e0b01c660039540900a024480070003801cae93efca4272ee149ce319c0002e081cae93efca4e736ef49b718ce000030f0f07e5eaa655318c65555749ca729d2550555000c80a0aaaabeb46318ce13a7709d3802af83f066318ceadcdb9ce6c03c1f97aaa6cd54c631955cab9532aa0018cc01511555541c000c2802aafad18c632ae44a0004e08157c1f83318c655b5ca00006783c1f97e9194d2918c64c80018cc1ca4890a0912024006025a12e290b88937e9019e72b8c65306318c632a83a4e5394e928008a000600050172b97d68c6319c274ee13a70072bbc1f83318c6739d5b8f73601e0fcbf2b8c6553666318c6319da739fd39514000c6600000039540000303801cae5f5a318c6d09cbb85a70000b82072bbc1f83318c635b4e739b0dcef7b4d800019e0f07e5eaca718c6318c18c673acd973800c60318000000030000003ad673ea568c6319f13f3be27e70075ace7d4a7cc6319f3df6df3df6c03c1f97ab29c6318c631b3318d67394d9538c6318d600000c6600000058440900a00c165801d6b39f52b46318ca1597b095600023040eb59cfa94f98c632ad66ede53600006783c1f97ce44f9925c599b53e625fa56918c6318c6b18c6cc73acd9738c600031ac000000006330000001d6b3a4fea46318c6b0979c4bce00eb59d27df918c6378f0dbf1e1b601e0fcbf4ad2318c6318d6318d9b9d26cc9c6318c6b000006330000002c22048050060b003ad6749fd48c6318d690acbd852b0000b82075ace93efc8c631a56b376f49b000030f0f07e5f9ce739f74a428e7d4e718c64c39932008088e5d3709712ee0cf779bf3711f7481ce739ca53ee738c99318c99cfa880008027c4bba3779b7db707e749caa4bca50975225e80274ef884e4dc63191264ce044041384210842709c1e109b707e772b9ca929d23194ce3194c6726b1ac22020a00000e57384bae272ebaf631ac00e573bc187ef383f07e0ec635803c1f9794a4326521050328e630ea318751a4690a000000000ea38e21c71c43cf294a4e319c003a8e3b871c71c76e52949c633800f4cf5fac80ca6ccc6318c631a529294e7e529494a549cfca525000001685212e27483f48d6739b0dc79edca5294a4c9948030e631a46348c6928c69480000000000131c75e5294a4292f214a4998cb801e38e1ca5294a520e5e948f3183003d33d7 26 67108863 10 1023
def hc_87_6 : Nat → Nat := uH 0x83db3fa0b590581af49e00519b7e1f7d5f0b5f27a357e1e0ca037630809d1f5b37273829c2d1bf6e50991b41d4969e0c9da0f5a366c45e592c61364800c591981a633c4a98731705fa589d78c9735ccb59d6e014b59fe60961fd7f577343154f23752fa909433a2c505e1c13d98f84d2f8dd2e5d98495a8f51f019a45709410ff1744276619004a643ff4078ff4c213e2c69cefe2343aa155ce6091f384a4e0dbad5f3552664cf6579329d4f0c9185731fe120c255692f4254cb6a9982c4a580aad19629505909ff952267063895910c24683f08de4ef236a03c000000235a040876581203668c7ca10e1dfc4b077c80a000000077a00a1dd105c000000000000076e4181c2664c68221e19f006066a048178e8685a3501163017454b90213be5c04801be10ff40443b81110dd0443dcd6a0daa72436042900000003538330cfd1442ff5000af1430285cda097d268255827091111420ccde082d018203021080601820140107e90701f601106675c419341a063805417dc410000000179013059214800000005780681250e40438170000000041e0680ccceb0119868000119 0x19e79e79e79e65998679e79b942c367999e66cf333cc33cf3cc8c4679e79819e679e79e79e79816679e79e6e50b0d9e66799b3cccf30cf3cf32c34233cf3cc0cf3945a1679e79e79e79e62cf336799b3cc59882ccf3cf3d0b310842cf3cf312e20cf1679e79f5ace3666ccd99b33666ccd99b375ace2cb3666ccd99b375ace5f5a3666ccd99b32cb5dd6b3bc1f833666ccd99b3f17e0fc1f97c6318d99b33666ccc633a56918d63194eb59c6318c6ccd99b33672b5a4eb59c6318c6ccd99b33672b5a4596bbad6718c631b33666ccd9cad6978bf07e0fcbca521d93290eca4b2339b2eb391ecae54ace9395ce2c707b389172b39d672b9c21ec389cbc97959ceb165aeef2d9cef0f61ece0e41fa5673ade2fc1f83f2f2593975294a52b4a5294ad272ba5294b4e76a529482522cb90e574a52969ced485292ebca4214a49969aee574a52969ced4a529061ca5ef4a47967867a67af8c653265253292ca463298c63298c64c6318751c770e0e38e494a918c630ea38e21c71c43cf252a46318c9969ae3a8e3b871c71c76e4a548c6318f2cf0cf4cf5ea4a918c99318d2318c631946ccc6318c633871dd252a4631831660c6319c38ee92952308cb9846318c63265a6bb871dd252a463183378c6318c63cb3c33d33d7c6318c6318c6367294a4634931a59b871dc6318c6318d294a4e1c7718c6318c634a529265a6bb871dc6318c6318d294a47967867a67af4a528da368ca36663294ab2952a518c654956b5aca5295ab18c5e94a50a2d45ad6b294a568c6d284a5d42529f8cb7ed6b594a52b463694a506af294f97e7e30fd1d294a5294a52959ca5292952cd4a9361c7b294a5294a54a529172b0e3d94a5294a52a5294938d37ec38f65294a5294a94a523cb3df3d33e394a52b687d4a5294a56ce5694a5694a5294ad2001c240068009120002c220480501a00c0482c0b0e3da5294b56b6a5292f29480b0005c105871ed294a5ab5b52949b97a52003c0030f03d33d79584b6128521185a0791a04160059490a341810580204000e21485a108100025c1083c426c3c0cf0f14a5295b43ea5294a52b662109122b0842508429084230842d4ad294ad294a5295a421497b0e3da5294b56b68458810844a52917290843884210842148421085a108421084210a42908421097b0e3da5294b56b68478842108394a41cbd291e59e188f1084295a56b5ad2b676936652b176b48b958bb48b0b2e45acbc979597b484bae292e596bfad60e41fa560fd697830fde907e2fc1f83f2f5555565255555471cc3c954c6555000000005590e3c8710f38e21c7b18d6005590e3c871c76c73c71ec635803c1f97aaaaab21c7551c7b6661e43987b299aa800000002ac9552a64caa8eaab654ca8aac871e4610f38e230f631ac00aae89556438f230e3b63f8c3d8c6b002a1a7af83f2f4a99008e30c3b23738ea53291cca80000002aa95553288ea50ee5dd631ac00b1aa3a943b83f3ac6358014357c1f97aaaaaaa52aaaa98caaa6523aaa800000002abe27e77c4fe875287b18d600557cf7db7cf7db1d4a1ec635803c1f97aaaaafaaaad65530e398755871ed9a99aa8000000002abeaaa64caac9552b65532654555f11a7309f9c75287b18d60056344aaaff8cd99f7db1d4a1ec63580150df2f83f2f555555555594a5291a5691a525550000000005594a5290a4bc85295974ec00ab294a52948397a52b067d800f4cf5eaaaaaaaaaaa3294a32aca5294aa000000000aaa1294a12975294ab47600555794a52941a94a5583f580230fd1d555556b4aa38e38f253a92a800000002abe69cdad0ea56b56b680155f33667db1d4a1f56b6803c1f97aaaab6d5ada5555b4b4ab2b525554000000001557d6b565edab68565ec2d580157c1f83d583b6adab583b7b5600f07e5eaaaaa98c6518c692aa98d6318caaa8000000002aaeb984631846b18c631ac00abe0fc19ac6318c6b18c631ac01e0fcbd555b594cd5400015555555455575ecbd80155d12aaf83f0760fd6005437cbe0fcbd72b9aae55554e1dc3b94e1d4a1d155cc0001c2c01c000141428001c2c0090028500e01c0aaaa843ae3894e1d4a1dce7380008c102aa9c3b63f94d8ea50ee739c00006783c1f97b955cd5caaaae939d2939ce73a4e455732400000382c001424480500489000e0b001c03815555d27df9484e5dc2939ce7380005c102e5593efca4e736ef49b739ce000030f0f07e5eb954ce759d63395cd572a6719c8aae600038b005800028183000e2c0000038b0060c0aaa984eb384672ebb8c670000b8205caa6739b758cdf83f06e338ceb000019e0f07e5eaac80368da91215514e29cfacfaeaaca4e929915ce448244800491214122404803418590a71485c449bf480cf2aae5caae6e739cae739ce7dce5515542c000000070582800068b00600d16001c1600aaaaebb9ce7384e5dc27380005c102af83f06e739ceb39ce7361b9def39b000033c1e0fcbf5939caae74a40006570e7cce90018c0284800140401cae93efc9c274ee13a7718ce0072ba4fbf2739d5b8f736e319c01e0fcbf590ee5533a567195ce7dd999d2719ce0553324000000003824480500183000e0007006055cae93efc8c272ee119ce319c0002e081cae93efc8ce736ef19b718ce000030f0f07e5e95ce5739c29d673955ce005182d2000140000050172b9f529fb39d67c4fcef89f9c01cae7d4a7ece759f3dfadf3df6c03c1f97a57395ce7dd9a9d6b39caaa729ceb5ac0aa663e00000000582c0b0480501a2c0180142800b000ab95cfa94fd9ceb28565ec25580008c10395cfa94fd9ceb2ad66ede53600006783c1f97a94e3287193387c00007198000028cc000c18000c1855f529f739ce718ce0008c07d4a7dce739c6338000303c1f97e72ab9ca5729400065718c000650e140105000072b9c274ee13b4fa94fb8c6700395ce3dcdb9ceadf529f718ce00f07e5f395cab9ce52b94eb195c6738ce539cfbb3055331c1600003e00000381c00060c004801428070018302ae5738467184e5df529f718ce00023040e573bc66cce736fa94fb8c67000019e0f07e5f39c92e2cdd69c4bf59395d275ace7dd98e72ab9d230005940002a84800001405cae93efcace7584bce25e70072ba4fbf2b39d6f1e1d7e3c36c03c1f97eb272ba4eb59cfbb31dcab2749ceb5ac0aa664800000000b0480501a00c04890016001572ba4fbf2b39d690acbd852b0000b82072ba4fbf2b39d695acddbd26c0000c3c3c1f97b2573cd5ce43c9554e1c71d5294a4e6b9a020a200aaa1c754a52939ce7002aa871d5294a4e739c007a67af72994e928d292a9a4694a4e958d2302e6b94c6368d2000511584e14e2939bb3720fd275aaa8395ce4e368d25d29494a73f294a52d6a4e7e5292828800b42909713a41fa4eb39cd86e3cf6f395ce92ca4e9195c6948d296894a598a00000800395ce319d294a4e319c00e5738c674a52938c67001e99ebc9652916ab2900b294a5291a5691a52140000105004d5794a5290a4bc852926ba6b801ea1ca5294a520e5e948f0cf0c00f4cf5f9aae79aaa529cb9ae6a52952739ce939ae68a55010005cd735294a939d2739ce00735cd5294a939d2739ce008c3f4772a994672aca528ca32994a528ca702e6b94ca368c60050aaa80cc561384a14ee5cdd9bf2941bad555402990014e29cf6cf6eaaa4ad2650b203310aaaa72aacc1cae6651b4e52e5394a5294a56b4a7294a529542aaa033007058250a714627794a0dd6739b0ddef374aa1dca67294e32b8528cad194a14148000000e57294a519ce338c6700395ca52946738ce319c01187e8e94aaa2d4a5500aa3294a32aca5294a141428028a000cc01635094a5094ba94a54718079435794a52941a94a5783f0601187e8f395ce52b95ad3974e739d2568d4b598a00000000b95ce31b4fa95ad39da0072b9c6339f529fd39da00f07e5f95ceb2eaced59da759575674b4a72b520050000000415cae5f5ad39dad09cbb85ab00395de0fc1e9ced6ace0dded5803c1f97aab9cd573cd318c65339ce73ee319ce6b9a002a020aabae6318ce739c00abe0fc198c63183739ce73803c1f97a57194c6306349ce5538c6318d6140004000072b9f529f318c655aca0072b9f529f318c655aca00f07e5f95c632a98b318ca318d23194c6318c60050001404001cae5d7308c6308cb98c6300395de0fc19bc6318c60cc631803c1f97aa0aa66160000160000002aabaebaeb8000b820f287e0fc1f83f0600006783c1f97aaa52aa94652a8cc0002c162aa8d1a0c1a34058000518ac4e203b59b3db033caa65194a652a8cc000155418b0060c018b060c008c2b1388b18cd9ac0679ab1ba35aa5555555505555294a35b46b6954520282a802aa94a52628e74c51cf68d3b002aa94a51f586d9e786dd833ec007a67c7559aaaaa9555294a55555146600a88a00aaaa2850b00002aa94a52b1a25b469d80009c102aa94a52adbe5b067d80000c3c0f4cf8ed65294aa546652519800039451a341871a34038700164c518ac2e22c7d9b3db033ccaa5463264c6328d998ca330000728a0c58030600c58306024a11851a661710798cd9e6033cd1b46a94e8da906254a550a52a82800aa94a51b46d0a0a000501004d635294a4c51ce98a39d38d38c00f50d4a528f3c3acf3c36cf0cf0c00f4cf8e94aaacd4a52aaa5294a94a5294a42828cc0000000072a80a09058070009ac6a9294a548528e4294938d38c0005c101ea1a94a52a52949b97a523c33c3000030f03d33e3d651b3ce4a34946cec6ccc58b294cab494a349735b2a651ac2800001666000039540306002c58002c2c0180055cc2b47611a35297b18d600017041e50cdeb376f19bf2941d8c19ac1800019e0f07e5ee79e7999323998679e799830586cf333ccd9e6679aa8679e799388cf3cf303f1564a54914000538a73db3dbcae69a4a5494733000b058aa59a0c68d0160001462b13880ed6b36dd8ff3607e2aaa8ea50eaaaaaaa52bb4000aa0e8000a0aaaa3a943b9ce7384e9dc274e00aa3a943b9ce73ab736e739b00f07e5eaae6aa3a943aac9552aaa839980002a22aaaa858680302aa828aa02a8ea50f65ecac68940009c102a8ea50f60fd655b7ca00006783c1f97aaaa651a4aa08000aaa48003002aca52958c6b00002aca52958c6b00001e99ebceb8a712f55554a5555531800154ca30eaaa0aa0e800025e712f3aa8ea50f631ac01e3c36fd586daa8ea50f631ac01e0fcbd554a55592aaaaae665187455455073300005155554155542c2c0180044aac6aa3a943d8c6b000138207caab6aa3a943d8c6b000019e0f07e5f3ccbcf371f9c94a5282c33f9da4a3294acc2d1c019f9e79e79e79e63998679e79d870586cf333ccd9e66798679e799388cf3cf303f153679e79b651ccc33cf3ccb2a9618d19e660c679e8b019e79e64e233cf3ced603f10d25197345001ccc154c18031600b0c18015846271066ec63580fc5cd55ccb3302c60c161831a2c00b8835ad603f17660a00b3f354959c80b2f4161f65b666524a54906d62d4ab2800000029c53d97b076f07e0ed60edeb67b123294acf3ae20fd3897a5b28a558caa05c94a52ad250011400000000055d4a5ecbd84bce25e700f287e5283b07eb78f0dbf1e1b601e0fcbe64e017380a7ce3cc2c11a0159716720bca494a9208000a714e1e33042e2b2db3b594ab2966600160b1ca166831a34058002cbd85c436dbde030cca494a920fac780000538a7cc10b8acb6cfd6b58f52acbeb36599800582c72859a0c78f1a34058002cbd85c452d957352ad69294a55a4a8a05998000000058580e5500b0d0060345800000055d4a5ecbdac25e315a300017041e50fca50760c3f583b7836c3f7bd66c0000cf0783f2f8ca52a54631932a9000e0e28cc071ca20e3951c1c05160c0087147250b883c71db033c 26 67108863 10 1023
def hc_87_7 : Nat → Nat := uH 0xd500583480300cf21b7f34d1edcb4a7ab26c599c80b69b193dbcc4956eb0b4dc2c19f4d2ff81bfbe1f706f36945bb45656e0ff06b66e746cdc2feb1d3676c055beae70696b37992ac8e142a6c2dea8106829875f3a509452938029a49213a90f854a16db467ecdba9dc57ba72991f9b555466d40059b260aa67d53197c68be59f14a94f561e53cc0294dd05a4efd1e90e2b7643141d8ec48063a80248e8207a3235f58c151e22ee45c8a5359a27687987e17e618cdae841487e0f9c2d83c309206fe0481441edff49727f50209f536037ba8695e89d81776baf1d7d57673a4945c32ed96ee37a1b28a416aeb6dda3022b65f6b29937d176407361871a41606c5697d411c5e3c4516cdb0659b360d5bc2c35384db145b6174f787d53669de4bcc73927220447c181d155a6b44204d9045b0a3f686b8f6d5b33bf0714e64a5e36a2bc0d698fc35760c0d1093432507c8c1edd52e29948adb2bd29b56dc9db64825638288a86c220e36f87cb9b51e1b44c7311571a5f99464913b179663859214e1326c8846658d0f83858330ac10985cf4186f6a04f848c0f4d2502166f4000216 0xab9aab294a45ac8b948b0b2e4165aaf25e5212eb8a4baeb965afe50e41fa52f061fbd20fc1f83f17e0fc1f97ae5718d2329ca50ee1ec6328cae6ab8ca1dd2b29ca51a4aab9aae54c61c7758c398ca719461d54ce70eb185387072d40ea50ee319caa613ace119ca10eb8e253875287718ce2cb5d72a99ceb3ac6729c3863f94e1d4a1dc6719d6f17e0fc1f97ae5caae66549d2939cab1a4ae3194693a52739d631a46555cd572a671a46339ceb19c6349caa6738758c48b949ce1c5c8718ce55309d6708ce92f2909cbb852738c67165aeaa673aceb19d20fd2939c1bbd2738ce33ade2fc1f83f2f2b2ca52b2aca46318cb631a4634964a3329596d294a5294891722c635acb694a5290a4bc852958c6b265a6bd96d294a52948397a52b18d63cb3c33d33d7aa52aac63194a5558ca94aa9196c6328c6528b50a528b2d94a52ac6359425294252f65b294a558c6b3f196fabca5294a0ecb65294ab18d67cbf3f187e8eca6b58cb9ad95358d62d4c5d8b1660b2ec63595730acbd8465d75ec6358b2d7f2866f583b78c1f83f0763066b07e2fc1f83f2f8c632a6ccd99b336699554c98c631659b33666ccd9aa98c632fad1b33666ccd9aa965ae6318de0fc19b33666ccd9aaf8bf07e0fcbd555555555652b4a5291a5691a525594a5294a448b91673acab294a52149790a52b39d64cb4d75594a5294a41cbd2959ceb1e59e19e99ebd555555555546529465594a5295655516a14a50a5295673acaaa1294a12975294ab39d67e32df555794a52941a94a559ceb3e5f9f8c3f475532ab99b46d29ad2d2acad495552cbd18dad5ac58bd0aabeb5a31b5a1597b0b562cb5d57c1f83d18336adab5ac1876b7bdab78bf07e0fcbd55cd56d655555554b2ec5d9512d55575ecbd955d12965aeabe0fc1d83f5950df2f8bf07e0fcbd5555555554c6548c6528c6518ca55529428b50a5294ab18d6555094ba84a5294a558c6b3f196faaa94a0d5e5294a52ac6359f2fcfc61fa3aaaaaaaaaa98d231a463494634a4ab294a5294a448b91631acab294a52149790a52b18d64cb4d75594a5294a41cbd2958c6b1e59e19e99ebd55555555573358d64b554552cbb18d644aaaeaabaf631ac596bbe554355f07e0ec635bc5f83f07e5f9aae79ab9ae6a994c63395294a1d54c631875287739ce55318c61d4a1dce738b2d755318c63063a943b9ce739de2fc1f83f2f5cae6ab955caae6a30e3eac38e65687528757294630f2d4871dca56943c9ca5294e50f255554e1c1cb503a943b9ce739ce1c5b85550875c7129c3a943b9ce7384e8dc2738b2d75553870c7f29c3a943b9ce73ace739c186e77bce778bf07e0fcbf35cd7355cf3532a9a52732918c3ae6b9c8b918c6339ce716e5cd7392f2318c6709ce138b2d75cd73907e918c63183739ce738ff3bc5f83f07e5ee5573572ab955ce4e74a4673b56738d2d2ba52749ca729d294a463395a539ce94b525555748b949ce1c5c8739ce739c38b70aaba4bca4272ee14b4e739ce1397709ce2cb5d557483f4a4e706ef49ce739ceb39ce7061b9c7f9cef17e0fc1f97b39d6737373733666ccd99b3b39d62cb3666ccd99b3b39d6bd7d68d99b33666cef2ef5ece75bc1f833666ccd99b3f17e0fd7debd5531b33666ccd9adadab695552cb3666ccd99b3d5ada55bd7d68d99b33666cf56b6af2ef5d57c1f833666ccd99b3d5ad6b6bc5f83f5f7af4caa631a46518cae6a995318c655318c1ac60b2cc631954c2358c231975cc6318b2d755318d6358c6f07e0cc6318d6f17e0fc1f97c63195ccc631956dab695ccc6318b2cc631b56b68c63197d68c631b56b68b2d7318c6f07e0cc6318d6d5ad6b6bc5f83f07e5f3b49f9480b9165e82c3fb964e1dcab234b5a75956d9cb5a74b523697195d6b6adab5a52d4ad652ae5748b2cb948b0b2e469ced6ad6b17ab395d25f5a9484bafa14b5a73b5ab597b27ab165aee57483f4a5e0c3f7a41e9c1bb56d5ad60ed63f56f17e0fc1f97b2573cd5ce43c9cd73543e956954aaa9c38e3aa52949ce73955421c712a52949ce73932d35d55438ea94a52739ce3cb3c33d33d792ca525591a529596d295a52948d264652d652948b94a52245c8b1764d5794a52948525e4294acba764cb4d73d4394a5294a41cbd295833ec7967867a67af964a9295a5299554b5651f33265523264b1449520b04a16a4a146291ea50720fd20ed4172548d12cd5614a0b2cb569da0b34216698b51895a508518a8caae729cae72b5a75956d9b8caa36972b4ad69d6b5ad2b295a56adab2ae57165a8516165a945e9ced6ad67ec5eace57094ba85ad295ad69ced6ad68edab165aee577bca0d5e0c3f2941e9c1bb56d5ad60ed6f6ade2fc1f83f2fcd573cd55294e735cd52b2769969735cd4a52a4e738b939ce72e6b9a94a5484e70a4e739cfc65beb9ae6a5295273a4e739cf97e7e30fd1d19554a52a94a5596ca32a8ca54a529562d5f516a14a50a2d4a52acf97658d425294252ea5294ab4767e32dff286af294a52835294ab07eb3e5f9f8c3f47ce729b5ad68c997005858016166872922428244802c2c04321a12e2d058b88f37e6c0cf3ac82ca3e66d1a43da5294a567e5294a4a54acfca5251c0ce400480005a14acba76907e9076b59bb1e7b72a7295a0010a952b94e0b2db3328dab59562d4a5294a54a4ab294a5294000004a14f68ede52830ed6b376f37cae75956d9bb4ed3ad6b6ad67f565472800161a00345800072a8000080652c160395cbeb5a73b5ab597b6ac005802e081caef07e0f4e0ddab6ad6b376b7b4d800019e0f07e5f4baceda56935294a52b9542168c6549525295a526a52b4f97a505821084210842107ad683d7b4a0fcacae73b5a532675a12b8421284a1085a1684a128521693092c2c2cb2c1027084210b42d09421085a108b1783f061dbc21074a12852b84f8b4984b80bd020b001ca2608644160081000272e2168420042012e08478426c0fc72b9d655b66ed3b4212a89c2108421694461084bad6b27ab5b565442b2ee57165e9ced08b102108d5ad62f5610944e10971084210842d0842108421085a158422c421395de0fc1e9c1bb561784210841ead6b076b7b56f17e0c4210a5224597dcb270ee5591a5ad39752d69d2d48da5c6572ba45965ca458597234e769cae92fad4a425d7d0a5ad39da2cb5dcae9061861ca5e0db0c3937a7390cb2c35c30d7a5165ab4ed084a10a8caae729cae72b5a72e9c6551b4b95a56b4e57165a8516165a945e9ced395c252ea16b4a56b5a73b4596bb95c186a6d5e0db0c352830f4e72196586b861afd6406d1a43819c800900b42949b6e54ae0328da00012853b6a537cae728ed3b4394000b0d000e550000100ca0395cbeb5a73b4005802e081b56db6db6f4db6803600d8d836db6df2a842d18ca5058210842129b0d4b8b95ce513b4ed084aa2708421085a51184212e57165e9ced08b10210810944e10971084210842d0842108b1084e57061861e9ce44b8842109b0cb2c312e21085cae75956d9bb4ed3ad6b6ad6d59572b8b2f4e76b56b58bd59cae5f5ad39dad5acbdb562cb5dcae0c30c3d38372dadef065961ae186bf72c9c3b9564696b4e5d4b5a74b523697195cae91e79f23e479e79e7c8f5c7bb5672ba479e797291e78797234e768f3cf3dcae91e7eb52908f5f4296b4e768f3cf3cb2d7cc528b2d5a76842cd42151955ce5395ce56b4eb2adb3d38caa36972b4ad69caef1eaf28ff7bcaf2bde5de76ace57165a8516165a945e9ced7bdef395c252ea16b4a56b5a73b5ef7bc596bd2a57282d6328da3d4af7ac000250a7e573acb61da769caef7bde5de76ac394000b0d001e001caa01e00080653c01e00395cbeb5a73b5ef7bc005802e0835af69caa10b4632bca3d4a0b04210842e573acb613b4ed084aa2708421085a51184212e577bdef2ef3b5611e210842f395c597a73b422c408423def78425138425c421084210b42108421085e108b1085cae75956d9bb4ed395def7bcbbced59d6b5b56b6acadbd60dcae2cbd39daf7bded5ad62f5672b97d6b4e76bdef7b56b2f6d58b2d7b655ced6b5aca96a59762ed62c2cbb0abaebd97b584bae2b2e596bf943f07e0ec187eb076f06187ef7ac1f8bf07e0fcbd494aacd54a5643aa9a4a54aca548ca398ca1cc65294a566652a46528751d4a50a1d4294a51a5224598718ce1d4750943a84a5294a518528e42349c633938d37c751d4a50ea1d4a5294a34a41cbc6938c671e59ef9e99f1d5555552a4aaa52b3329523294aa000000000aaa9294a518529e4234ac635801554a528d29372f1a5631ac007a67c75552aaab3592aaaa9524caad9554a566652a465294b2d554555494a528d29122cc58c6b225557555494a528c294f211a5631ac9c69be9eaa86aaa529469483978d2b18d63cb3df3d33e3c63499329495292ca4a63298c632a9a463194c63194c6318d23666318c6318751c770e0e38e4a52918c63166318c630ea38e21c71c43ba52948c632e6318c631932d35c751c770e38e38ee94a52318c19bc6318c631e59e19e99ebe318764ca43b292ca463299c63298ce4d6349cae71638396e245cac6359cae70875c7139792f2b18d62cb5dcae77870c7f383907e958c6b78bf07e0fcbd552ab25564a65555318d2326554c9954d23666318c631972aa2aca52918c63166318c6322555cab294a4631a7318c6318c9969aeb95572aca52918c60cde318c6318f2cf0cf4cf5e4b2318d23194c6318c6319cae94a52318c18b306318ce574a52918465cc2318c631932d35dcae94a52318c19bc6318c631e59e19e99ebd55555368ca6cd54c39b3318c6318cab2554a994caac871e4631831660c63195172aac87d48c234e6118c6318cab912965aeab21c7918c60cde318c6319572e5f17e0fc1f97eb233954c6368c632a9b3358d998c6318c6318d29694e54a46339572ba45c8c63062cc18c6369ce1c5e872ba4bea461197308c6318c635b4272ee169c596bb95d20fd2318c19bc6318c631ada739c186e71fed3bc5f83f07e5f1a52549918c64c63180070724061c728838e5470702428306004389c2e21c38ed819e552c99194c651ca8480c8e555411caac85060c0095c4e21cad81d64a52918c6318c6918c6318d23666318c631800900060c00000607088120140182c3006001c38ee94a52318cb98c6318c600017040e1c774a52918c66cde318c63180000c3c0f4cf5f1a52549909128e2708421c43aa38a712852318c98c6108ce070b0408710e2108429084613871dc788419e2aa593244255544e5551384a148ca63323184233942c10884a89c2908461395c788419e295c250a46108d204160006729214082c010200c1801484230804b82107884d819e1e294a521084891384212842148c6318c6348c21197318c6348d998c6308c210842318c670e3ba529484588108418c63166318c6308421084210a42108421084211846108c210842109c38ee94a5211e2108420cc63066f18c6318c79678623c4210a52329a463666918b2e45c8c5859660b31975e4bc8c25d7119731972cb5fc1f83907e91bc187ef183f18c1f8bf07e0fcbd295559a94a55cae52a59a94a548d2d48d2929caaa5294a5494a929cae5294a54a529122e45ace7176529428b50e57294a548528e4294ace7594252ea12949c69bee57294a54a520e5e94ace7594a506a3d4a3cb3df3d33e3a52a4a52a46b1932631946318c398c6b18c631946918c65394a9528c6318ca3194e1c772a4a5294a918c60c598358c6318d6529428b50e1c772a4a5294a918468cc2318d6318c63594252ea12949c69bee1c772a4a5294a918c60cde318d6318c63594a506a3d4a3cb3df3d33e3acd59ab35672348ca5494a528c632a4a2c71df566acd59ab334a522cca529498e3c6acd59ab35666948ca52949c69be78e386acd59ab35666948ca52947967be7a67c78c631b33666ccd998c672aca31ac6349d6b38c6318d99b33666cd56b29d6b38c6318d99b33666cd56b28b2d775ace318c63666ccd99b355acaf17e0fc1f97a5294a5539465529cb9b2eb397595d27295672b9c5d8b59c16a559ceb395ce15ad613975297b39d62cb5dcae77ad6b59c1f94a0ece75bc5f83f07e5e954e5d294a52aca5294ab29cae5294ad39da529428b50e57294a569ced284a5d42529f8cb7dcae5294ad39da5294a0c352bde529f2fcfc61fa3c63264ca52946328c6318c6318c631946cdd6b38c598318c294a518b318c675ace308c6308cba94a518c633f196fbad671bc6318c60d4a528c6319f2fcfc61fa3a92a46d1b463294651b395a4c9948c63294ab0e3da4a54b4636a529122e45871ed252a5a31b52149790a524cb4d7b0e3da4a54b4636a529072f4a47967867a67af4a52adab694ab66a5294ab294ab294a5295651600005068b00028500016110140280d1600c160282c0b5ad65294ad5ada5294ba94a002c0230416b5aca5295ab5b4a529b5794a000033c1187e8eca12d84a1284616ac0ad198088c00b28a1468b06011180204002842d0840805182111884d81f8a52956d5b4a55b35294a1084891584212842128421184216956529565294a52aca1094bdad6b294a56ad6b17a146204210a52945a94210842128421084210b4210842108421284a10842b5ad65294ad5ada1462108428d4a506af294f97e7c4210aacab5ad6cd56b29b2a558bb58b52ac5965d9458596a2d65d4a5ecbd9425d712972cb5fd6b07e5283b07eb2bc187ef283f17e0fc1f97c652a8c65194c6318c6319cae318c18b30a52946318ce5718465cc23194a528c6319f8cb7dcae318c19bc63294a518c633e5f9f8c3f4752aa9954a554caa6326319555557294a539ce1c5b8318c6555ca5294e13a7709da318c67e32df555ca5294e739b71ee6cc6319f2fcfc61fa3a632aaaa553194aa6552aa54caa6318c6318ca366a9932aaae3166318c65294a545ca6b18c632aae318c631a75294a55c894c6319f8cb7d5571bc6318c60d4a529572e5318c67cbf3f187e8f18c6553194a5528c6518c65555294a528c65318c6318c631946ccc65318c672fae718b318c63294a539ce1c5b83166318ce635ce318c631975294a709d1b84e718c633f196fb90d738de318c6306a5294e7383779ce318c67cbf3f187e8e94632a538c632673801c3800c8a0229705a1905dce5dc1646203739bf3607e3164608cc518a94244a6119509319529c274e63191264ce71608716e109c2708421084e138b106ef0841b83f3a94aa718c655294a7263299c651ac63298ce5cae2d4a716165b8b18d672bae5d4a5dc25d71397b18d62cb5dc86b83f2941bbc187ef383b18d6f17e0fc1f97a955555554655553294a94632aaaaa94a5165be165be5ac63176555294a4c51ce98a3d58c6b271a6faaa94a51e786d9e786dd8c6b1e59ef9e99f1d5555566aaa529554aa554ca9194a52952cd5b2655551660ca50a9294a52a25adac6317655508ca30953aa4a5294ac6896c635938d37d5547994652835294a5437cb631ac7967be7a67c794aaa7294aaacd4a5294a52a5654cae32a465294a54b331a4e31a5272b945983294294a54a52245c87166339ce5728465184a5d4a52a42947214a4e319c9c69bee5728f328ca506a52952948397a52718ce3cb3df3d33e3aaaaaaa52aaa655319554c632632ab9ce1c5b81d4a1cc631955c274fa16b43a95a318c62cb5d55ce736e3dcd8ea50e6318de2fc1f83f2f555554c6d29b355318c6318c61cd9aa9964aa9532aa62cc18c6075287358c63195172aa984631846d0ea568d6318c655c894b2d755378c6318c18ea50e6b18c632ae5cbe2fc1f83f2f8caa6329475d4948f23194c6318c98ca6318c630ea38e38e0ee1c1d4a1cc6318751c710f3e85ad0ea568c6318b2d71d471c71db1dc38e3a94398c6378bf07e0fcbe32a99ca5718da31954d998c6318c6358d998c6319ce9294a56a4ab95c62cc18c60b528d6318c6d39c38bd0e57184631846d295a318c6d09d1b85a7165aee571bc6318c60fca5066318c6b69ce7061b9def69de2fc1f83f2f8c63294a518caccc6318c632651b370e3b8c63194a528c6318b33871dc6318ca52946318c9c69bee1c7718c63294a518c631e59ef9e99f1e318c6318c631b35294a319498cacdd6b38c6318d6318c65294a75ace318c6318c65294a7e32df75ace318c6318c65294a7cbf3f187e8e9552a4ca632a80a504720633472aaa142a823953018300b97098c2710b96dc9601d6528c654a518c6319319c002801c16018cdc394450a1c39571600c060c046e146274611880dce6fcd9601f8c6318c65294a31946318c6318c6318ca36638000003060050001830384403058a0140182c0306001d1b8c6318c65d4a528c6318230008c10383f38de318c6336a52946318c058000678230fd1c4e5554894a128912a25caa95264463093195c22311caa27084a1289c88498427d70a38c4b9c8a3e13944894a12942319513b427584212a528c6118c232633ee1118e0b042709c21284270a3108423084f86e147189c1f9c28f9442528423184e0004460a0319b94102004460285060306004e10942308100028c108137188b00fc0a3c6318c61384891084612ea52946328421284a108c6318c630842308c2118c631946cdcf96e3166318c610840a310a529462cc6318421084e1184610842108421084a108421184210842109f707e71bc6318c60c4214628c425294a318c67cbf3e2108428f2654a518c632b32cb2cb3062c2d4a2cb318b5d7119730975d4a5cc65cb2d7f07e0fde3066f061f94a0fc6307e2fc1f83f2f232ac8ca54a94a5465518751d4655194a94a52943a8e3963838e38a5295673ac3a8e38871c710f3a94a559ceb271a6f8ea38e78e38e38eda94a559ceb1e59ef9e99f1d494aacd54a54751d4656946529525294a56721d565252a4a5494a50ea3a94a143a85294a54ace75a529122e40ea3a84a1d425294a52ace75a42947214a49c69be3a8ea528750ea5294a559ceb4a520e5e948f2cf7cf4cf8f9c3a3ae7294a9294a918c6318c6318c6318c61cc6358c631946318c6518c6366651b3318d99946cdc38ee2cb7c2cb7c5494a52952358c6318d670e3b931473e85ad2a4a5294a91ac6318c6b271a6fb871dc79e1b679e1b6a9294a52a46b18c631ac7967be7a67c78c64c9aca52a4a52a46328c630e631ac6318c6318ca32a4e93265231a46318c653871dc62cc18c61525294a548d6318c635a529122e43871dc6118c611b4a9294a52a46b18c631ad214a390a524e34df70e3b8c798c631835494a52952358c6318d694a41cbd291e59ef9e99f1f723e6b973cf3cf33679ab3ccd9e6acf3cf3cdc16679e798a313b3cf3cdc19ee0c3cf3cf3e51f3cf3cf3cf3cf31dca6cf35679ab3ccd9e79e79e6e0b33cf3cc518b41879e79e6e0cf771d59ab3566acd59ab33666ccb1c77cb7cb7d59ab3566acd31c78d38d38d59ab3566acd38d37cf1c70cf0cf0d59ab3566accf2cf7cf4cf8f28ca566acd59ab35295294a4a548c631638efa8c652b3566acd59ca5291724c71e3518ca566acd59ab394a524e34df3c71c3518ca566acd59ab394a523cb3df3d33e3 26 67108863 10 1023
def hc_87_8 : Nat → Nat := uH 0xef92efe7e5ebdc42e9d4c9decc2629c0ced6bb4d60b449c1ad71b6a659c69f69bc9a69409379bc8c79c089a0b684794a7ffd1f7935b27221c567fa8a6129b45ac5994f3ae34751fa3baaea33fdeb2f2d342a4939218e2f1c8941166d871021930b51340002d4 0x50ea5566aa52a38ea38ea5294a1d4a5294a5294a1c7551e4a50e652954a94a528751d4a50ea1d4a5294a739ce1c71c1dc383a8ea528750ea5294a539ce70e21dc38871df8cb7c751d4a50ea1d4a5294a739ce1c71dc3b871df2fcfc61fa3a51dd65d5875294ad0f655d48732a9d494a5395c3a943e9ced6ace1c5e872b8752b5a73b5a139770b562cb5dcae1d4a1f4e76b56706ef6ade2fc1f83f2fa4aa38ea1d4a1d565566aa52932954a54c3a8e3994a328c650ea52946528ca50ea38e59830e38a528750ea5294a538c670ea38e230e610f1a94a1d43a94a5294e319cfc65be3a8e3f8c39871c352943a875294a529c6339f2fcfc61fa3c65532947326329a463298c6318ca318ce5718b3063181d4a1cc6319cae308c6308cb8ea50e6318c596bb95c6f18c631831d4a1cc631bc5f83f07e5e8752ab3552951d4752943a875294a5281d4050a0000050000eaa0282c52881601c000ea3a94a1d43a94a5294e74600046080751d4a50ea1d4a5294af39c1800019e08c3f47095443a875084a5d559aa942442512951d47138421085652943a875294a528751c51881084294a1d43a94a52945b9cf884a21c4210842108425094212842108421084210ea38a310842146a528750ea5294a579ce0df2fcf884215cd5555294a2d5458596a0b528b2d5750975c4a5d4a5d75cb2d7f286af061fbca0fca507e0fc1f8bf07e0fcbd552a95294a566acd59ab3555294a566acd59ab355b3e5d94a52959ab3566acd56d1a764e34df5294a566acd59ab355b067d8f2cf7cf4cf8ea5573552aab252a5234ad234a4ab252a5294891722ce759564a54a4292f214a5673ac9969aeab252a52948397a52b39d63cb3c33d33d7aaaab296ad292aaaca5a558d292aab22e5ab5ac5eb56b162f42ac97d4b56b6b42b2f616ac596baac83f4b560edab6ad60eded5bc5f83f07e5eaaaaa98c6518c692aa98c631a4aaac8b91ac60c6306b18c632ac979184631846b18c63165aeab20fd2358c6318d6318c635bc5f83f07e5ee6aaaaaacad2555559172544b5b1765592f255744b65ec596baac83f4950df2d83f5bc5f83f07e5eaaa98c69194632aaaaaa6328c6318c60d630aa5a946318c611ac6118caaa52e6318c6b165ae631ac6b18cabe5283318c635bc5f83f07e5eaaaad94a52b4aaab63294a56a4aaa96a56ad6d6ad62c5e85552b5ab2f6d5b42b2f616ac596baaf94a0f560edab6ad60eded5bc5f83f07e5eaaaa956550000555297b2f60055f2941d83f5803c1f97aaaaae6aaaaaa5594b2d554552d4ab17644aaaeaaa52f65ec596bbe554355f2941d83f5bc5f83f07e5fbb3cf3cf373cdcf35679b98e3e63b871f3cf3cdc16679e798a714f9e79e6e0cf7679e79f37373731c7b2b3566acd599638efab3566acd59d9f2ec98e3c6acd59ab356768d3b271a6f9e38e1ab3566acd59d833ec7967be7a67c754b2555559ab3566ace5294955559ab3566ace5294acf97655566acd59ab394a52b469d938d37d5559ab3566ace5294ac19f63cb3df3d33e3aaaaaaaab9557294a1d43a94a52952949d274a4b9557294a143a85294a94a4fc8b949ce73972aae50943a84a5294a54a528e52939ce7271a6fae555ca528750ea5294a54a520e5e949ce738f2cf7cf4cf8ea95cd552aaaa32aca3294a5294aaa528516a14a52ace759554252ea1294a5295673acfc65beaaa52835794a5294ab39d67cbf3f187e8eb9aaab9a94a5294a54a529294a5294a54a52916e73ea5294a5295294a49b9d1a71a6fa94a5294a54a5291ee7067967be7a67c7292acb393a4ab9cae74a5294a5294a5274a52939caae54992a4a5949c694a4e574a5294a52917293ace739ceb38739c395d294a52949794a4eb39ce7384e7384eb265a6bb95d294a52948397a52759ce739d6739ce758f2cf0cf4cf5f964eb2ead2969d293acaba549d29c6594a4e5748b96ace717ad59c38bd0e57497d4b5673b5a139770b562cb5dcae907e96ace77b5ab38377b56f17e0fc1f979495659994aae72c94654993a4ac9d2b19cae71a5234a46948d231a4e94a5272ba52949c598339c4a529172938b319ce72ba52949c2338c272f2949794a4e4cc673932d35dcae94a5271e6719ce0e529072f4a4e3cc6738f2cf0cf4cf5f964632a994ca318c98ca6318c6348c63395d22e462cc18c60c598c63395d25e46118c61197318c63165aee57483f48de318c63066f18c6378bf07e0fcbf3a5272a9529949c48070e0070e1ca229d1a0c38d1a01c3800b384e1584c5c459d66dcd87819e52b952973a52949c48705800061ce5114b8b0060c038b060c009c25d37098b883db7367b83c0cf2525596727e4ab95d294a5294a5290e50240048900000381caa0202949059601c00395d294a52949794a49b9cb802600b82072ba5294a529372f4a47b9c1801e0018781e99ebc4b9a255544a555554252a550e3a9c2139ca81c2c10a8b35421c421084a109c28c4a1c751e210678a5d2a12e74a423384216b4e552a522738421084216b5291608b3ac38138521084e10842709c21084588f1083b3ace758f1552b952912b950910846118421385673a529484630842758b1c16082dc270a42108427097108461084588f73833c420cf71e295ca84b842b389020b000739445220b004080b0e004e14842708010804b82107884d87819e1e29495659884aa2728942109949510a4bb95d294a427084210ad294a529395d294a422c40842252948b948b7384251384210852108421084210a429084e108421162109cae94a5211e2108420e529072f4a47b9c19e59e188f10842 24 16777215 10 1023
def nh_87 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_87_8 (Nat.sub p 1024)) (hc_87_7 (Nat.sub p 896)) (Nat.blt p 1024)) (hc_87_6 (Nat.sub p 768)) (Nat.blt p 896)) (hc_87_5 (Nat.sub p 640)) (Nat.blt p 768)) (hc_87_4 (Nat.sub p 512)) (Nat.blt p 640)) (hc_87_3 (Nat.sub p 384)) (Nat.blt p 512)) (hc_87_2 (Nat.sub p 256)) (Nat.blt p 384)) (hc_87_1 (Nat.sub p 128)) (Nat.blt p 256)) (hc_87_0 p) (Nat.blt p 128)
def f_87 := uF 0x20db5b836d660db57836d560da5b83655c00c5f82d5b60b45e82cd260b34500316e0936d824d860926000315e0835f81f1b1ffd657ff1bdffc6e7ff1b5ffb4b7fed25ffb477fed1602c5980b155ffa4b8011fa00349800d16002497fe51c00c537f51bdfd4637f5165fd455002d7dfac6d7ead79fab567ead3800b5b7e51b5f9461002d5df846477d5bdf745477d58df636c77d195df36e77cdb5f425b77cd7df356e77cd79f0b5e7c71f1f0a637c25bddf3577bf189df3567b31b9eca6e7b7175ed35c7b2999df23b7a71a9e9b667aad81ea2667a68e5df1377a292de435e79c94de715f790d59e5a5e796959e4239792d69e413577c0e9dfa5e78854de205f77e959e115677e4a5e035a77e095df036002d4dd6d6f7769c1d6d6775b1bdd6c6e75b19dd6c6275adadd6b637655f9d957675a92dd747e75d1d9d724975a51c00b4f74358dd0c5f743179d0c5d742db9d0b62742d59d0b4e7428edd12397424dc00b4b7115b9cf46c7115adc456373292dcd24973251dc456272f1b1c446b71118dca36c710dadc936c710d8dc434e710d25c6e7a71b9c9c42537139e9c4e72712985c415f002d1dc33646e15bdc236c6e115dc0c5f70314dc035c6e1159be24b6f890dbe14f6f6d71b84556e0db9b83626ef1b9b835e6e0d75b834e6e0d35b823b6e28e5b8137002d0db72546c717db5a566d655db4e706d29b1b1c576c6979b1a566cb159b1a4e6c691800a5b6815bda05636811bdaf2546bb1b9a04636b6951a045f6b2911a045b6ad9c1ab26c68115da993f6a64dda924468114da6d6e69adbda6b6369ad55a025e68d189a336f690db1a435c68cd8da334d680959a2456680939a0b62682d69a024600294d9cc596731559d34f6775c19d3476729517356b65d1659745565ed3d9a45c65ed2d97b47662d319845465ed0d972545cd58d962546575cd7346f64d5f59424464d179932445cd1ad90d706445bd911676429f17346763b5918f35c63a99180e736371f180d756031f980c7d62e99180c6f6029198a45461f58d8946461edbd8793f61e4dd80a446189718624460251d8525460d1b98324460e931831456021298113460653181035602119734635ef5f97ec645fa9117bc735f11bd7c4635f2d517c3635ee9517345f5e51f979b6f5e6d8d792445cd14d783645dcd0d771575cc9b97324e5d5161753585cf5ad745695cf1897324600292d7226453f5bd7047d5c11c57027c53f59d4fc6f5b55f56e2445b51796d24453f1ad6bd7c5ae9f14fc675ab1f15fd7557f1f95fc7d5a29f15fc6757e9196636f5984fd6613757e9116524457e51d6426c58b19962a4458a5155f84a5865b1603665804d16003557e1194fc635791f95e24453f16d5b6725729115b47356ed8d5b26c53f15d5a34b53e9b94fa4e55f17d57b4755e4dd4fa4c5591c15637055159d54462550da95436253e9195045f54ad8550457540d6d50353540d2d5013f53e91000a4353a9913cd6f53453d4d1475329513cd6b52e9f13cd6752a9513cd635269113cc6b5211b9482444f318d472444f316d4593f5164dd452444f314d41c5b50715d4246150b1414245550655d3ca6e5011b9403634f29793d5624f4dad3db6c4f6d713d3634f295800a3b4ee9913256f4de9593994f4e651d37a544e09b1382544de55d325634da53d362544c917d3526c4c915d3226e4cf1b93225e4cb589322560028cd1246f44918d3056e4491652f4524491552dc694b71951236f4b2d512b5694ad5952b356448d8d123594a6d49123554a31911234f49ed911234b49b5a112347496d911234349295123d6948e9591226347d1fd2224447d1cd1f4694811892027c47d1951f26444892d1847f476911184734611a51c24446b1891b35246a9f1184654609f1182644609311824444890d172544575a515a644569591223b45295112d6944a9911346844a9591223300257cf946d3e5184f936d3e4d850ec7c43adc0f934f42b5c50ca4b43290d0ad7042da010b28c42a94cf93474171f5092444171c507b5f41ed5d05a7c4191c106370416918f924b4011f5042444011c50027c4009b101c70406dc100246402d85002443e490cff2543e75c4fb45f3f75b0fb45b3ed15cfc46c3ef590fb4533e69f0fa5703e6958f923b00255cf846431f5bcf5c7c3d6df4f5b713d69c0c7d6731f1b8c7b6f3cb1f4f2b543cad38c7b6b3c71f0c7b67390df8e437d390db4e4367390d94e4364390d54e43543ad1f0eb4643aed70eb2643908ece7b6c39ed98e7b6439ed50e825439e8e4e403a392998e4a64392950e51543924a4e403631ed8ce2b7e38ad50c7b5b3839c8e0c6c382dccc7b5731ed24df56231ed14de26c36f154dba54373150dba4e36e918c7a6b3571fcda4643571ccd836f362db0d8363356950d5a4e35ad50d6372356918c7a6333f1fcd424433f1cccfa7e346dbcd236c346d8ccfa5433e938d047233e918c7a5b33a910ca47b335190cd2443291cccc4663289f8cab6b32ad8cca25431e8ecc857e3209f8c825431e8cc0094f31a92c915623151b0c53452451acc3c6c30ed149146330b1cc9136f3059c0c136c244dacc02432ff5c0913672ed9c0be4542ed5ccbb37e2f2d10bc5632ecdb0bb35c244d8cb956b2e51b8b9362244d74913512dd1f8b746c244d3cb63542d39c8b4b7e2d2db0913432ce958b1e702c71b4b1a6c2c69189126b2a99c0aa47f2be970aec7c2bb1b0aa4732b2dbcad36c2b2d8caa26c2ab180ab4602aadc8aa24624498ca8a562a295097e7225f1fca57802951f0a5e70296d80a524425f1cca426428b5f8a324428b1c897c6d25f18497a7e27edbca035c27ed8c97a6c27b58897a4c276db09ac7226b1809bc6026edb09ab7226ad8097a46266db0983632631889835125e9109124325318095d6a2575a094a7e2529b09123b24e95091e722471b091a7e2469b09123300251c8f36423e9108f26b1d15bc8dc54236d5074563232d507445f22c92c8b24322adb0744571d0db88946e1d0d78885621d0d58872542051b885b6c216d708126620717c8456c20716c81c5720ad708256420714c812441d098c7dc7e1fed907da7e1f91bc7e4631f69107425b1ed1f87b27e1ec9507b2441d094c74c6e1e4db07935c1d29987545f1df5b07545b1d515c7635c1d7590754531d29107424b0024fc734681115bc724581115ac70a3b1c28cc6fc701be9c0445671b91606e35811158c6d35519d5a46756119cd7c6a26e1a89886a26019cd5c67e7919f1b86835c19e9986723b1111886636e1111686536e11114863d6a18ed704436b1875a861b66186d70443631808ec6023317ed704435b17ad70443531669985a35f1731b05a35b168d5c5b35c16b1905a3531669704426b16291056d6215f18056a6615a97044263154918552441355c85446c1351ec52c6c14a9104d4731371ac4dc63136dbc5047c136dac4db6713adb04e474136d8c4d25c11096c4ba4612e9104757212a9104a46c11d1ec48c6c1229104747311c9704724c11094c44a66114d7c4535b112970442330024dc41c6910a9b041c651069900156f1029103f4590fd1543f2540055ac3cc7d0f69103cc710f29f0015670e91643b25c0e91543a25400558c3857f0e2950385730051bc35d7d0da91035c5e0d69100146b0d11bc344630ce9f0014670ca9b03257408d9fc3125c0c15903026408d9cc2347e08d1f42346f0b69f0234670b0db82c36608c91828d6f0ab15028d630a2dbc28b5f0a2d5c232440991b82726c0991982624408c12823b6e0925b023b6608e4d02304600518c2057e0811ec212440811cc2025400517c1e56d0791f81e24400516c1ca560729501867206f1f01847b0691f01a2440611cc18b6b062d8c1826c00515c1725e05b1b0155650551f81524400514c11c5b04715c13364046d2c12364046d0c0126e02d1b80b36f02edf40bb6502ed540db64036d500b83a0309900c25402e0d80b36300497807d6201edbc07b6b01ed9c0837e01ed8c0125601b1580124e015160053580075ac03c7000edc001d6700718801b62006d68012460024bc0003f 11 11
def ch_87 := dN fullMask g_87 ep_87 4 15 bds_87 1057 (dT fullMask rootStock 11 f_87) cur_87 nh_87
set_option maxHeartbeats 0 in
theorem rc_87 : dR fullMask g_87 ep_87 4 15 1057 bds_87 (dT fullMask rootStock 11 f_87) (cur_87 0) (nh_87 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_0 : tB 0 32 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_1 : tB 32 64 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_2 : tB 64 96 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_3 : tB 96 128 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_4 : tB 128 160 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_5 : tB 160 192 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_6 : tB 192 224 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_7 : tB 224 256 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_8 : tB 256 288 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_9 : tB 288 320 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_10 : tB 320 352 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_11 : tB 352 384 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_12 : tB 384 416 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_13 : tB 416 448 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_14 : tB 448 480 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_15 : tB 480 512 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_16 : tB 512 544 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_17 : tB 544 576 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_18 : tB 576 608 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_19 : tB 608 640 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_20 : tB 640 672 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_21 : tB 672 704 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_22 : tB 704 736 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_23 : tB 736 768 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_24 : tB 768 800 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_25 : tB 800 832 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_26 : tB 832 864 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_27 : tB 864 896 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_28 : tB 896 928 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_29 : tB 928 960 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_30 : tB 960 992 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_31 : tB 992 1024 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_32 : tB 1024 1056 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_33 : tB 1056 1057 ch_87 = true := by decide +kernel
theorem nj_87_1 : ∀ i, 0 ≤ i → i < 64 → ch_87 i = true := bJ (fun _ h1 h2 => tA nb_87_0 h1 h2) (fun _ h1 h2 => tA nb_87_1 h1 h2)
theorem nj_87_2 : ∀ i, 0 ≤ i → i < 96 → ch_87 i = true := bJ nj_87_1 (fun _ h1 h2 => tA nb_87_2 h1 h2)
theorem nj_87_3 : ∀ i, 0 ≤ i → i < 128 → ch_87 i = true := bJ nj_87_2 (fun _ h1 h2 => tA nb_87_3 h1 h2)
theorem nj_87_4 : ∀ i, 0 ≤ i → i < 160 → ch_87 i = true := bJ nj_87_3 (fun _ h1 h2 => tA nb_87_4 h1 h2)
theorem nj_87_5 : ∀ i, 0 ≤ i → i < 192 → ch_87 i = true := bJ nj_87_4 (fun _ h1 h2 => tA nb_87_5 h1 h2)
theorem nj_87_6 : ∀ i, 0 ≤ i → i < 224 → ch_87 i = true := bJ nj_87_5 (fun _ h1 h2 => tA nb_87_6 h1 h2)
theorem nj_87_7 : ∀ i, 0 ≤ i → i < 256 → ch_87 i = true := bJ nj_87_6 (fun _ h1 h2 => tA nb_87_7 h1 h2)
theorem nj_87_8 : ∀ i, 0 ≤ i → i < 288 → ch_87 i = true := bJ nj_87_7 (fun _ h1 h2 => tA nb_87_8 h1 h2)
theorem nj_87_9 : ∀ i, 0 ≤ i → i < 320 → ch_87 i = true := bJ nj_87_8 (fun _ h1 h2 => tA nb_87_9 h1 h2)
theorem nj_87_10 : ∀ i, 0 ≤ i → i < 352 → ch_87 i = true := bJ nj_87_9 (fun _ h1 h2 => tA nb_87_10 h1 h2)
theorem nj_87_11 : ∀ i, 0 ≤ i → i < 384 → ch_87 i = true := bJ nj_87_10 (fun _ h1 h2 => tA nb_87_11 h1 h2)
theorem nj_87_12 : ∀ i, 0 ≤ i → i < 416 → ch_87 i = true := bJ nj_87_11 (fun _ h1 h2 => tA nb_87_12 h1 h2)
theorem nj_87_13 : ∀ i, 0 ≤ i → i < 448 → ch_87 i = true := bJ nj_87_12 (fun _ h1 h2 => tA nb_87_13 h1 h2)
theorem nj_87_14 : ∀ i, 0 ≤ i → i < 480 → ch_87 i = true := bJ nj_87_13 (fun _ h1 h2 => tA nb_87_14 h1 h2)
theorem nj_87_15 : ∀ i, 0 ≤ i → i < 512 → ch_87 i = true := bJ nj_87_14 (fun _ h1 h2 => tA nb_87_15 h1 h2)
theorem nj_87_16 : ∀ i, 0 ≤ i → i < 544 → ch_87 i = true := bJ nj_87_15 (fun _ h1 h2 => tA nb_87_16 h1 h2)
theorem nj_87_17 : ∀ i, 0 ≤ i → i < 576 → ch_87 i = true := bJ nj_87_16 (fun _ h1 h2 => tA nb_87_17 h1 h2)
theorem nj_87_18 : ∀ i, 0 ≤ i → i < 608 → ch_87 i = true := bJ nj_87_17 (fun _ h1 h2 => tA nb_87_18 h1 h2)
theorem nj_87_19 : ∀ i, 0 ≤ i → i < 640 → ch_87 i = true := bJ nj_87_18 (fun _ h1 h2 => tA nb_87_19 h1 h2)
theorem nj_87_20 : ∀ i, 0 ≤ i → i < 672 → ch_87 i = true := bJ nj_87_19 (fun _ h1 h2 => tA nb_87_20 h1 h2)
theorem nj_87_21 : ∀ i, 0 ≤ i → i < 704 → ch_87 i = true := bJ nj_87_20 (fun _ h1 h2 => tA nb_87_21 h1 h2)
theorem nj_87_22 : ∀ i, 0 ≤ i → i < 736 → ch_87 i = true := bJ nj_87_21 (fun _ h1 h2 => tA nb_87_22 h1 h2)
theorem nj_87_23 : ∀ i, 0 ≤ i → i < 768 → ch_87 i = true := bJ nj_87_22 (fun _ h1 h2 => tA nb_87_23 h1 h2)
theorem nj_87_24 : ∀ i, 0 ≤ i → i < 800 → ch_87 i = true := bJ nj_87_23 (fun _ h1 h2 => tA nb_87_24 h1 h2)
theorem nj_87_25 : ∀ i, 0 ≤ i → i < 832 → ch_87 i = true := bJ nj_87_24 (fun _ h1 h2 => tA nb_87_25 h1 h2)
theorem nj_87_26 : ∀ i, 0 ≤ i → i < 864 → ch_87 i = true := bJ nj_87_25 (fun _ h1 h2 => tA nb_87_26 h1 h2)
theorem nj_87_27 : ∀ i, 0 ≤ i → i < 896 → ch_87 i = true := bJ nj_87_26 (fun _ h1 h2 => tA nb_87_27 h1 h2)
theorem nj_87_28 : ∀ i, 0 ≤ i → i < 928 → ch_87 i = true := bJ nj_87_27 (fun _ h1 h2 => tA nb_87_28 h1 h2)
theorem nj_87_29 : ∀ i, 0 ≤ i → i < 960 → ch_87 i = true := bJ nj_87_28 (fun _ h1 h2 => tA nb_87_29 h1 h2)
theorem nj_87_30 : ∀ i, 0 ≤ i → i < 992 → ch_87 i = true := bJ nj_87_29 (fun _ h1 h2 => tA nb_87_30 h1 h2)
theorem nj_87_31 : ∀ i, 0 ≤ i → i < 1024 → ch_87 i = true := bJ nj_87_30 (fun _ h1 h2 => tA nb_87_31 h1 h2)
theorem nj_87_32 : ∀ i, 0 ≤ i → i < 1056 → ch_87 i = true := bJ nj_87_31 (fun _ h1 h2 => tA nb_87_32 h1 h2)
theorem nj_87_33 : ∀ i, 0 ≤ i → i < 1057 → ch_87 i = true := bJ nj_87_32 (fun _ h1 h2 => tA nb_87_33 h1 h2)
theorem nc_87 : ∀ i, 0 ≤ i → i < 1057 → ch_87 i = true := nj_87_33
theorem lb_87 : LowerBin fullMask rootStock g_87 12 :=
  lowerDagV5 (kn_cons lb_82 (kn_cons lb_77 (kn_cons lb_83 (kn_cons lb_80 (kn_cons lb_78 (kn_cons lb_11 (kn_cons lb_79 (kn_cons lb_12 (kn_cons lb_46 (kn_cons lb_85 (kn_cons lb_86 (kn_cons lb_10 (kn_cons lb_81 (kn_cons lb_23 (kn_cons lb_21 (kn_cons lb_84 (kn_cons lb_35 (kn_cons lb_20 (kn_cons lb_22 (kn_cons lb_15 (kn_cons lb_42 (kn_cons lb_59 (kn_nil))))))))))))))))))))))) rc_87 nc_87 (by decide +kernel)
def wg : List Gate := [⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [6, 1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [9, 5]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.and, [11, 4]⟩, ⟨GateOp.and, [12, 7]⟩, ⟨GateOp.or, [12, 7]⟩, ⟨GateOp.and, [2, 14]⟩, ⟨GateOp.or, [15, 10]⟩, ⟨GateOp.and, [8, 16]⟩, ⟨GateOp.or, [17, 13]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 3972587648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276808392 * 2 ^ 32 + 3972587648)) (13 - 1) := by
  rw [show canon fullMask (4276808392 * 2 ^ 32 + 3972587648) = g_87 by decide]
  exact lb_87
end PEqualNP.Outside.L_meta_48420
theorem PEqualNP.Outside.L_meta_48420 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 3972587648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 3972587648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_48420.table2_from_lowerBin (4276808392 * 2 ^ 32 + 3972587648) 13 PEqualNP.Outside.L_meta_48420.root_lb PEqualNP.Outside.L_meta_48420.wg 18 rfl PEqualNP.Outside.L_meta_48420.wfits PEqualNP.Outside.L_meta_48420.weval

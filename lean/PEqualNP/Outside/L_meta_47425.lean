import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47425

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
        (Bool.rec none
          (forceWP (Nat.shiftRight h 2) (fun h' => some (cur, h')))
          (checkHintBoundV5 goal negGoal fuel1 ws1 hist1 bounds tag))
        (forceWP (Nat.shiftRight h 2) (fun h1 =>
          forceWP (Nat.add 3 (Nat.land h1 cutMask)) (fun cid =>
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

def m_0 : Nat := 0xcccc00000000
def s_0 : List Nat := [0x444400000000, 0xc0c00000000, 0xcc00000000]
def g_0 : Nat := 0x44c00000000
def ep_0 : Nat := 0x4800000000000004080000000000000000000000000000044000000000
def bds_0 : List (Nat × List Nat × Nat × Nat) := []
def cur_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_0 : Nat → Nat := fun _ => 0
def f_0 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_0 : Nat → Bool := dagCheckNodeV5 m_0 g_0 ep_0 1 1 bds_0 1 (dagTraceF m_0 s_0 3 f_0) cur_0 nh_0
set_option maxHeartbeats 0 in
theorem rc_0 : dagCheckRootsV5 m_0 g_0 ep_0 1 1 1 bds_0 (dagTraceF m_0 s_0 3 f_0) (cur_0 0) (nh_0 0) s_0 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_0 : treeBlockF 0 1 ch_0 = true := by decide +kernel
theorem nc_0 : ∀ i, 0 ≤ i → i < 1 → ch_0 i = true := fun _ h1 h2 => treeBlockF_at nb_0 h1 h2
theorem lb_0 : LowerBin m_0 s_0 g_0 4 :=
  lowerDagV5 (kn_nil) rc_0 nc_0 (by decide +kernel)

def m_1 : Nat := 0xf0f000000000000
def s_1 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_1 : Nat := 0x107000000000000
def ep_1 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
def bds_1 : List (Nat × List Nat × Nat × Nat) := []
def cur_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_1 : Nat → Nat := fun _ => 0
def f_1 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_1 : Nat → Bool := dagCheckNodeV5 m_1 g_1 ep_1 1 1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) cur_1 nh_1
set_option maxHeartbeats 0 in
theorem rc_1 : dagCheckRootsV5 m_1 g_1 ep_1 1 1 1 bds_1 (dagTraceF m_1 s_1 3 f_1) (cur_1 0) (nh_1 0) s_1 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_1 : treeBlockF 0 1 ch_1 = true := by decide +kernel
theorem nc_1 : ∀ i, 0 ≤ i → i < 1 → ch_1 i = true := fun _ h1 h2 => treeBlockF_at nb_1 h1 h2
theorem lb_1 : LowerBin m_1 s_1 g_1 4 :=
  lowerDagV5 (kn_nil) rc_1 nc_1 (by decide +kernel)

def m_2 : Nat := 0xaa00aa00000000
def s_2 : List Nat := [0x22002200000000, 0xa000a00000000, 0xaa00000000]
def g_2 : Nat := 0x2002a00000000
def ep_2 : Nat := 0x28000000000000000000000000000200080000000000020020000000000000000000000000
def bds_2 : List (Nat × List Nat × Nat × Nat) := []
def cur_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_2 : Nat → Nat := fun _ => 0
def f_2 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_2 : Nat → Bool := dagCheckNodeV5 m_2 g_2 ep_2 1 1 bds_2 1 (dagTraceF m_2 s_2 3 f_2) cur_2 nh_2
set_option maxHeartbeats 0 in
theorem rc_2 : dagCheckRootsV5 m_2 g_2 ep_2 1 1 1 bds_2 (dagTraceF m_2 s_2 3 f_2) (cur_2 0) (nh_2 0) s_2 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_2 : treeBlockF 0 1 ch_2 = true := by decide +kernel
theorem nc_2 : ∀ i, 0 ≤ i → i < 1 → ch_2 i = true := fun _ h1 h2 => treeBlockF_at nb_2 h1 h2
theorem lb_2 : LowerBin m_2 s_2 g_2 4 :=
  lowerDagV5 (kn_nil) rc_2 nc_2 (by decide +kernel)

def m_3 : Nat := 0xcc00cc00000000
def s_3 : List Nat := [0x44004400000000, 0xc000c00000000, 0xcc00000000]
def g_3 : Nat := 0x4004c00000000
def ep_3 : Nat := 0x48000000000000000000000000000400080000000000000000000000000004004000000000
def bds_3 : List (Nat × List Nat × Nat × Nat) := []
def cur_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_3 : Nat → Nat := fun _ => 0
def f_3 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_3 : Nat → Bool := dagCheckNodeV5 m_3 g_3 ep_3 1 1 bds_3 1 (dagTraceF m_3 s_3 3 f_3) cur_3 nh_3
set_option maxHeartbeats 0 in
theorem rc_3 : dagCheckRootsV5 m_3 g_3 ep_3 1 1 1 bds_3 (dagTraceF m_3 s_3 3 f_3) (cur_3 0) (nh_3 0) s_3 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_3 : treeBlockF 0 1 ch_3 = true := by decide +kernel
theorem nc_3 : ∀ i, 0 ≤ i → i < 1 → ch_3 i = true := fun _ h1 h2 => treeBlockF_at nb_3 h1 h2
theorem lb_3 : LowerBin m_3 s_3 g_3 4 :=
  lowerDagV5 (kn_nil) rc_3 nc_3 (by decide +kernel)

def m_4 : Nat := 0xf000f000000000
def s_4 : List Nat := [0x50005000000000, 0x30003000000000, 0xf000000000]
def g_4 : Nat := 0x10007000000000
def ep_4 : Nat := 0x60000000000000000000000000000000000000000000100020000000000010004000000000
def bds_4 : List (Nat × List Nat × Nat × Nat) := []
def cur_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_4 : Nat → Nat := fun _ => 0
def f_4 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_4 : Nat → Bool := dagCheckNodeV5 m_4 g_4 ep_4 1 1 bds_4 1 (dagTraceF m_4 s_4 3 f_4) cur_4 nh_4
set_option maxHeartbeats 0 in
theorem rc_4 : dagCheckRootsV5 m_4 g_4 ep_4 1 1 1 bds_4 (dagTraceF m_4 s_4 3 f_4) (cur_4 0) (nh_4 0) s_4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_4 : treeBlockF 0 1 ch_4 = true := by decide +kernel
theorem nc_4 : ∀ i, 0 ≤ i → i < 1 → ch_4 i = true := fun _ h1 h2 => treeBlockF_at nb_4 h1 h2
theorem lb_4 : LowerBin m_4 s_4 g_4 4 :=
  lowerDagV5 (kn_nil) rc_4 nc_4 (by decide +kernel)

def m_5 : Nat := 0xf000f0000000000
def s_5 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_5 : Nat := 0x100070000000000
def ep_5 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
def bds_5 : List (Nat × List Nat × Nat × Nat) := []
def cur_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_5 : Nat → Nat := fun _ => 0
def f_5 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_5 : Nat → Bool := dagCheckNodeV5 m_5 g_5 ep_5 1 1 bds_5 1 (dagTraceF m_5 s_5 3 f_5) cur_5 nh_5
set_option maxHeartbeats 0 in
theorem rc_5 : dagCheckRootsV5 m_5 g_5 ep_5 1 1 1 bds_5 (dagTraceF m_5 s_5 3 f_5) (cur_5 0) (nh_5 0) s_5 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_5 : treeBlockF 0 1 ch_5 = true := by decide +kernel
theorem nc_5 : ∀ i, 0 ≤ i → i < 1 → ch_5 i = true := fun _ h1 h2 => treeBlockF_at nb_5 h1 h2
theorem lb_5 : LowerBin m_5 s_5 g_5 4 :=
  lowerDagV5 (kn_nil) rc_5 nc_5 (by decide +kernel)

def m_6 : Nat := 0x4444444400000000
def s_6 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_6 : Nat := 0x4044400000000
def ep_6 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
def bds_6 : List (Nat × List Nat × Nat × Nat) := []
def cur_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_6 : Nat → Nat := fun _ => 0
def f_6 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_6 : Nat → Bool := dagCheckNodeV5 m_6 g_6 ep_6 1 1 bds_6 1 (dagTraceF m_6 s_6 3 f_6) cur_6 nh_6
set_option maxHeartbeats 0 in
theorem rc_6 : dagCheckRootsV5 m_6 g_6 ep_6 1 1 1 bds_6 (dagTraceF m_6 s_6 3 f_6) (cur_6 0) (nh_6 0) s_6 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_6 : treeBlockF 0 1 ch_6 = true := by decide +kernel
theorem nc_6 : ∀ i, 0 ≤ i → i < 1 → ch_6 i = true := fun _ h1 h2 => treeBlockF_at nb_6 h1 h2
theorem lb_6 : LowerBin m_6 s_6 g_6 4 :=
  lowerDagV5 (kn_nil) rc_6 nc_6 (by decide +kernel)

def m_7 : Nat := 0xff000000000000
def s_7 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_7 : Nat := 0x17000000000000
def ep_7 : Nat := 0x600000000000000120000000000000014000000000000
def bds_7 : List (Nat × List Nat × Nat × Nat) := []
def cur_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_7 : Nat → Nat := fun _ => 0
def f_7 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_7 : Nat → Bool := dagCheckNodeV5 m_7 g_7 ep_7 1 1 bds_7 1 (dagTraceF m_7 s_7 3 f_7) cur_7 nh_7
set_option maxHeartbeats 0 in
theorem rc_7 : dagCheckRootsV5 m_7 g_7 ep_7 1 1 1 bds_7 (dagTraceF m_7 s_7 3 f_7) (cur_7 0) (nh_7 0) s_7 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_7 : treeBlockF 0 1 ch_7 = true := by decide +kernel
theorem nc_7 : ∀ i, 0 ≤ i → i < 1 → ch_7 i = true := fun _ h1 h2 => treeBlockF_at nb_7 h1 h2
theorem lb_7 : LowerBin m_7 s_7 g_7 4 :=
  lowerDagV5 (kn_nil) rc_7 nc_7 (by decide +kernel)

def m_8 : Nat := 0xaaaa00000000
def s_8 : List Nat := [0x222200000000, 0xa0a00000000, 0xaa00000000]
def g_8 : Nat := 0x22a00000000
def ep_8 : Nat := 0x2800000000000002080000000000000220000000000000000000000000
def bds_8 : List (Nat × List Nat × Nat × Nat) := []
def cur_8 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_8 : Nat → Nat := fun _ => 0
def f_8 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_8 : Nat → Bool := dagCheckNodeV5 m_8 g_8 ep_8 1 1 bds_8 1 (dagTraceF m_8 s_8 3 f_8) cur_8 nh_8
set_option maxHeartbeats 0 in
theorem rc_8 : dagCheckRootsV5 m_8 g_8 ep_8 1 1 1 bds_8 (dagTraceF m_8 s_8 3 f_8) (cur_8 0) (nh_8 0) s_8 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_8 : treeBlockF 0 1 ch_8 = true := by decide +kernel
theorem nc_8 : ∀ i, 0 ≤ i → i < 1 → ch_8 i = true := fun _ h1 h2 => treeBlockF_at nb_8 h1 h2
theorem lb_8 : LowerBin m_8 s_8 g_8 4 :=
  lowerDagV5 (kn_nil) rc_8 nc_8 (by decide +kernel)

def m_9 : Nat := 0x2222222200000000
def s_9 : List Nat := [0x202020200000000, 0x22002200000000, 0x222200000000]
def g_9 : Nat := 0x2022200000000
def ep_9 : Nat := 0x220000000000002002000000000000202000000000000000000000000000000000000000000
def bds_9 : List (Nat × List Nat × Nat × Nat) := []
def cur_9 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_9 : Nat → Nat := fun _ => 0
def f_9 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_9 : Nat → Bool := dagCheckNodeV5 m_9 g_9 ep_9 1 1 bds_9 1 (dagTraceF m_9 s_9 3 f_9) cur_9 nh_9
set_option maxHeartbeats 0 in
theorem rc_9 : dagCheckRootsV5 m_9 g_9 ep_9 1 1 1 bds_9 (dagTraceF m_9 s_9 3 f_9) (cur_9 0) (nh_9 0) s_9 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_9 : treeBlockF 0 1 ch_9 = true := by decide +kernel
theorem nc_9 : ∀ i, 0 ≤ i → i < 1 → ch_9 i = true := fun _ h1 h2 => treeBlockF_at nb_9 h1 h2
theorem lb_9 : LowerBin m_9 s_9 g_9 4 :=
  lowerDagV5 (kn_nil) rc_9 nc_9 (by decide +kernel)

def m_10 : Nat := 0xa0a0a0a00000000
def s_10 : List Nat := [0x202020200000000, 0xa000a00000000, 0xa0a00000000]
def g_10 : Nat := 0x2020a00000000
def ep_10 : Nat := 0x208000000000002000800000000000000000000000000020200000000000000000000000000
def bds_10 : List (Nat × List Nat × Nat × Nat) := []
def cur_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_10 : Nat → Nat := fun _ => 0
def f_10 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_10 : Nat → Bool := dagCheckNodeV5 m_10 g_10 ep_10 1 1 bds_10 1 (dagTraceF m_10 s_10 3 f_10) cur_10 nh_10
set_option maxHeartbeats 0 in
theorem rc_10 : dagCheckRootsV5 m_10 g_10 ep_10 1 1 1 bds_10 (dagTraceF m_10 s_10 3 f_10) (cur_10 0) (nh_10 0) s_10 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_10 : treeBlockF 0 1 ch_10 = true := by decide +kernel
theorem nc_10 : ∀ i, 0 ≤ i → i < 1 → ch_10 i = true := fun _ h1 h2 => treeBlockF_at nb_10 h1 h2
theorem lb_10 : LowerBin m_10 s_10 g_10 4 :=
  lowerDagV5 (kn_nil) rc_10 nc_10 (by decide +kernel)

def m_11 : Nat := 0xc0c0c0c00000000
def s_11 : List Nat := [0x404040400000000, 0xc000c00000000, 0xc0c00000000]
def g_11 : Nat := 0x4040c00000000
def ep_11 : Nat := 0x408000000000004000800000000000000000000000000000000000000000004040000000000
def bds_11 : List (Nat × List Nat × Nat × Nat) := []
def cur_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_11 : Nat → Nat := fun _ => 0
def f_11 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_11 : Nat → Bool := dagCheckNodeV5 m_11 g_11 ep_11 1 1 bds_11 1 (dagTraceF m_11 s_11 3 f_11) cur_11 nh_11
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsV5 m_11 g_11 ep_11 1 1 1 bds_11 (dagTraceF m_11 s_11 3 f_11) (cur_11 0) (nh_11 0) s_11 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_11 : treeBlockF 0 1 ch_11 = true := by decide +kernel
theorem nc_11 : ∀ i, 0 ≤ i → i < 1 → ch_11 i = true := fun _ h1 h2 => treeBlockF_at nb_11 h1 h2
theorem lb_11 : LowerBin m_11 s_11 g_11 4 :=
  lowerDagV5 (kn_nil) rc_11 nc_11 (by decide +kernel)

def m_12 : Nat := 0xaa000000aa00
def s_12 : List Nat := [0x220000002200, 0xa0000000a00, 0xaa00]
def g_12 : Nat := 0x20000002a00
def ep_12 : Nat := 0x280000000000000000000000000000000000000002000000080000000200000020000000000000000000
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
def cur_12 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_12 : Nat → Nat := fun _ => 0
def f_12 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_12 : Nat → Bool := dagCheckNodeV5 m_12 g_12 ep_12 1 1 bds_12 1 (dagTraceF m_12 s_12 3 f_12) cur_12 nh_12
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsV5 m_12 g_12 ep_12 1 1 1 bds_12 (dagTraceF m_12 s_12 3 f_12) (cur_12 0) (nh_12 0) s_12 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12 : treeBlockF 0 1 ch_12 = true := by decide +kernel
theorem nc_12 : ∀ i, 0 ≤ i → i < 1 → ch_12 i = true := fun _ h1 h2 => treeBlockF_at nb_12 h1 h2
theorem lb_12 : LowerBin m_12 s_12 g_12 4 :=
  lowerDagV5 (kn_nil) rc_12 nc_12 (by decide +kernel)

def m_13 : Nat := 0xf0f000000000
def s_13 : List Nat := [0x505000000000, 0x303000000000, 0xf000000000]
def g_13 : Nat := 0x107000000000
def ep_13 : Nat := 0x6000000000000000000000000000001020000000000000104000000000
def bds_13 : List (Nat × List Nat × Nat × Nat) := []
def cur_13 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_13 : Nat → Nat := fun _ => 0
def f_13 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_13 : Nat → Bool := dagCheckNodeV5 m_13 g_13 ep_13 1 1 bds_13 1 (dagTraceF m_13 s_13 3 f_13) cur_13 nh_13
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsV5 m_13 g_13 ep_13 1 1 1 bds_13 (dagTraceF m_13 s_13 3 f_13) (cur_13 0) (nh_13 0) s_13 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_13 : treeBlockF 0 1 ch_13 = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 1 → ch_13 i = true := fun _ h1 h2 => treeBlockF_at nb_13 h1 h2
theorem lb_13 : LowerBin m_13 s_13 g_13 4 :=
  lowerDagV5 (kn_nil) rc_13 nc_13 (by decide +kernel)

def m_14 : Nat := 0xff0000000000
def s_14 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_14 : Nat := 0x170000000000
def ep_14 : Nat := 0x6000000000000001200000000000000140000000000
def bds_14 : List (Nat × List Nat × Nat × Nat) := []
def cur_14 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_14 : Nat → Nat := fun _ => 0
def f_14 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_14 : Nat → Bool := dagCheckNodeV5 m_14 g_14 ep_14 1 1 bds_14 1 (dagTraceF m_14 s_14 3 f_14) cur_14 nh_14
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsV5 m_14 g_14 ep_14 1 1 1 bds_14 (dagTraceF m_14 s_14 3 f_14) (cur_14 0) (nh_14 0) s_14 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14 : treeBlockF 0 1 ch_14 = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 1 → ch_14 i = true := fun _ h1 h2 => treeBlockF_at nb_14 h1 h2
theorem lb_14 : LowerBin m_14 s_14 g_14 4 :=
  lowerDagV5 (kn_nil) rc_14 nc_14 (by decide +kernel)

def m_15 : Nat := 0x4444000044440000
def s_15 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_15 : Nat := 0x4000004440000
def ep_15 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
def cur_15 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_15 : Nat → Nat := fun _ => 0
def f_15 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_15 : Nat → Bool := dagCheckNodeV5 m_15 g_15 ep_15 1 1 bds_15 1 (dagTraceF m_15 s_15 3 f_15) cur_15 nh_15
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV5 m_15 g_15 ep_15 1 1 1 bds_15 (dagTraceF m_15 s_15 3 f_15) (cur_15 0) (nh_15 0) s_15 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15 : treeBlockF 0 1 ch_15 = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 1 → ch_15 i = true := fun _ h1 h2 => treeBlockF_at nb_15 h1 h2
theorem lb_15 : LowerBin m_15 s_15 g_15 4 :=
  lowerDagV5 (kn_nil) rc_15 nc_15 (by decide +kernel)

def m_16 : Nat := 0xc000c000c000c00
def s_16 : List Nat := [0x400040004000400, 0xc0000000c00, 0xc000c00]
def g_16 : Nat := 0x40004000c00
def ep_16 : Nat := 0x400080000000400000008000000000000000000000000000000000000000000000000000000040004000000
def bds_16 : List (Nat × List Nat × Nat × Nat) := []
def cur_16 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_16 : Nat → Nat := fun _ => 0
def f_16 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_16 : Nat → Bool := dagCheckNodeV5 m_16 g_16 ep_16 1 1 bds_16 1 (dagTraceF m_16 s_16 3 f_16) cur_16 nh_16
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV5 m_16 g_16 ep_16 1 1 1 bds_16 (dagTraceF m_16 s_16 3 f_16) (cur_16 0) (nh_16 0) s_16 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16 : treeBlockF 0 1 ch_16 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 1 → ch_16 i = true := fun _ h1 h2 => treeBlockF_at nb_16 h1 h2
theorem lb_16 : LowerBin m_16 s_16 g_16 4 :=
  lowerDagV5 (kn_nil) rc_16 nc_16 (by decide +kernel)

def m_17 : Nat := 0xaa00aa
def s_17 : List Nat := [0x220022, 0xa000a, 0xaa]
def g_17 : Nat := 0x2002a
def ep_17 : Nat := 0x280000000000000000000000000002000800000000000200200000000000000000
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
def cur_17 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_17 : Nat → Nat := fun _ => 0
def f_17 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_17 : Nat → Bool := dagCheckNodeV5 m_17 g_17 ep_17 1 1 bds_17 1 (dagTraceF m_17 s_17 3 f_17) cur_17 nh_17
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV5 m_17 g_17 ep_17 1 1 1 bds_17 (dagTraceF m_17 s_17 3 f_17) (cur_17 0) (nh_17 0) s_17 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17 : treeBlockF 0 1 ch_17 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 1 → ch_17 i = true := fun _ h1 h2 => treeBlockF_at nb_17 h1 h2
theorem lb_17 : LowerBin m_17 s_17 g_17 4 :=
  lowerDagV5 (kn_nil) rc_17 nc_17 (by decide +kernel)

def m_18 : Nat := 0x30c030c030c030c0
def s_18 : List Nat := [0x1040104010401040, 0xc000c000c000c0, 0x30c0000030c0, 0x30c030c0]
def g_18 : Nat := 0x1000104010403040
def ep_18 : Nat := 0x40200000000040000020000000000000000000000000000000000000000000000000001000104010400040
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
def cc_18_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a490320230c608c108a104207c4f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c50244438453c3d3c3930302c2c24253c2134183c143408100924ee3fda3bd637d233cd3fc93bb537a1339d2f952b89277d23783f743b60374c33482f402b342728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_18_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b09490909090747070707070707070545050505034292821202012101002 0xfd38f934f438f034e928e524e028dc24c64cc240bc4cb840b13cad34a818a41499389a3c903c8c3084188014 8 255 3 7 10 1023 16 65535
def cur_18 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_18_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_18_0 p) (Nat.blt p 32)
def hc_18_0 : Nat → Nat := unpackHintV5 0xb47533a905480a4050125952829404a024090ca8224009f08f807823919c80dc46833309904ace541290911c6902a50d400b0002 0x0 13 8191 5 31
def hc_18_1 : Nat → Nat := unpackHintV5 0xe41c83906c6d81b03606c0ccd81ad34ce7dcf09e03c0708ba9612c0580a10f51a4304510a010414c28032006 0x0 11 2047 4 15
def nh_18 : Nat → Nat := fun p => Bool.rec (Bool.rec (0) (hc_18_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_18_0 p) (Nat.blt p 32)
def f_18 : Nat → Nat × Nat := unpackForestF 0xf138f134f038f034063fdd28dd24dc28dc24063b06370633053f053bba4cba40b84cb8400537a53ca534a418a4140533052f9a3c052b8c3c8c300527801880140523043f043b664c6640654c65400437503c5034502c50240433042f453c042b393c393004272c2c2c240423213c2134041f143c1434041b041709240413000f 6 10
def ch_18 : Nat → Bool := dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 64 (dagTraceF m_18 s_18 5 f_18) cur_18 nh_18
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 64 bds_18 (dagTraceF m_18 s_18 5 f_18) (cur_18 0) (nh_18 0) s_18 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18_0 : treeBlockF 0 32 ch_18 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18_1 : treeBlockF 32 64 ch_18 = true := by decide +kernel
theorem nj_18_1 : ∀ i, 0 ≤ i → i < 64 → ch_18 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_18_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_18_1 h1 h2)
theorem nc_18 : ∀ i, 0 ≤ i → i < 64 → ch_18 i = true := nj_18_1
theorem lb_18 : LowerBin m_18 s_18 g_18 6 :=
  lowerDagV5 (kn_nil) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0xc3c30000c3c30000
def s_19 : List Nat := [0x4141000041410000, 0x303000003030000, 0xc3000000c30000, 0xc3c30000]
def g_19 : Nat := 0x103000001430000
def ep_19 : Nat := 0x40000000000000000000000002000000420000000000000000000000000000000000000100000001400000
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
def cur_19 : Nat → List (Nat × Nat) := unpackCursorV5 0xb146850a14214072e0701 0x282868c142030f243e80c9c2a409881e104800f 7 127 3 7 10 1023 14 16383
def nh_19 : Nat → Nat := unpackHintV5 0xe81b12e4582b01602a1540988f202e002 0x0 11 2047 5 31
def f_19 : Nat → Nat × Nat := unpackForestF 0x282810f843210a9630508042630f041e104800f 4 10
def ch_19 : Nat → Bool := dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 11 (dagTraceF m_19 s_19 4 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 11 bds_19 (dagTraceF m_19 s_19 4 f_19) (cur_19 0) (nh_19 0) s_19 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19 : treeBlockF 0 11 ch_19 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 11 → ch_19 i = true := fun _ h1 h2 => treeBlockF_at nb_19 h1 h2
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagV5 (kn_nil) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0x33330000cccc0000
def s_20 : List Nat := [0x1111000044440000, 0xcccc0000, 0x30300000c0c0000, 0x33000000cc0000]
def g_20 : Nat := 0x1113000004440000
def ep_20 : Nat := 0x2000000400000000200000400000000000000000000001110000004440000
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
def cc_20_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0a4948290520a41292504a090320230c608c108a104207c4f05e03a1740e81b13606c0c881c001 0x7a38763471386d34643c60345c2c58244438453c3d3c3930302c2c242028212c1a3816300c3c0834fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23683f543b50374c33482f402b34272823241f1c1b10170413000f 11 2047 5 31 10 1023 16 65535
def cc_20_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_20 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_20_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_20_0 p) (Nat.blt p 32)
def hc_20_0 : Nat → Nat := unpackHintV5 0xdc0dc0dc0dc0d06d00d00d00d00c46b86ac6a44a029849809048468407c47066846425c45c0544486480404346058002 0x0 12 4095 5 31
def hc_20_1 : Nat → Nat := unpackHintV5 0xaa75502989482a404d2a6812c49414a02294f8e6e73701a88d026802f29780b445812c013949824a11e38e847022a70d40414010 0x0 13 8191 5 31
def hc_20_2 : Nat → Nat := unpackHintV5 0xe 0x0 8 255 4 15
def nh_20 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_20_2 (Nat.sub p 64)) (hc_20_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_20_0 p) (Nat.blt p 32)
def f_20 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b0527823405236e386e346d386d34043f583c5834582c5824043b04370433042f453c042b393c393004272c2c2c240423041f212c041b163816300417083c08340413000f 6 10
def ch_20 : Nat → Bool := dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 64 (dagTraceF m_20 s_20 5 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 64 bds_20 (dagTraceF m_20 s_20 5 f_20) (cur_20 0) (nh_20 0) s_20 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20_0 : treeBlockF 0 32 ch_20 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20_1 : treeBlockF 32 64 ch_20 = true := by decide +kernel
theorem nj_20_1 : ∀ i, 0 ≤ i → i < 64 → ch_20 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_20_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_20_1 h1 h2)
theorem nc_20 : ∀ i, 0 ≤ i → i < 64 → ch_20 i = true := nj_20_1
theorem lb_20 : LowerBin m_20 s_20 g_20 6 :=
  lowerDagV5 (kn_nil) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xc0c03030c0c03030
def s_21 : List Nat := [0x4040101040401010, 0x303000003030, 0xc0003000c00030, 0xc0c03030]
def g_21 : Nat := 0x103000403030
def ep_21 : Nat := 0x40200000000000000000000000002000400000000000000000000000000000000000000000100000400000
def bds_21 : List (Nat × List Nat × Nat × Nat) := []
def cc_21_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682b1560ac148a80d009c3382704a2941282314418810861042084108210420748e81d03a0740c901c001 0x7a3876346c3c68345c305d44564c5244484c4444382039342a48264022381e30144c10440c3c0834f63fea3be637de33d93fd53bc137ad33a92fa52b91277d23703f643b603758334c2f402b3c273423301f2c1b18170413000f 11 2047 5 31 10 1023 16 65535
def cc_21_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0a2a0a092898881808080808080646060606044404040404040242020202004 0xfc38f834f028ec24e230e344d24cce40c84cc440bd3cb934b418b014a3489f40983c94308d4c894484188014 8 255 3 7 10 1023 16 65535
def cur_21 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_21_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_21_0 p) (Nat.blt p 32)
def hc_21_0 : Nat → Nat := unpackHintV5 0xfa27b13925c04dc2654aea160aa084e126090d28223f11b24b905252140f0c6c63601910c805c428314009084802020d180b0002 0x0 13 8191 5 31
def hc_21_1 : Nat → Nat := unpackHintV5 0xa624a4a4091847a93541814a104a322191008044001e10d8c6c03221900b885062230e187003041800a1038c1c00a20500188006 0x0 13 8191 5 31
def hc_21_2 : Nat → Nat := unpackHintV5 0x4 0x0 6 63 3 7
def nh_21 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_21_2 (Nat.sub p 64)) (hc_21_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_21_0 p) (Nat.blt p 32)
def f_21 : Nat → Nat × Nat := unpackForestF 0xf838f834063fec28ec24063b0637e3440633053f053bc64cc640c44cc4400537b13cb134b018b0140533052f052b97489740943c94300527814c814480188014052376387634043f683c6834043b04375d440433524c5244042f444c4444042b042739340423041f041b1e481e401e381e300417084c0844083c08340413000f 6 10
def ch_21 : Nat → Bool := dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 64 (dagTraceF m_21 s_21 5 f_21) cur_21 nh_21
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 64 bds_21 (dagTraceF m_21 s_21 5 f_21) (cur_21 0) (nh_21 0) s_21 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_0 : treeBlockF 0 32 ch_21 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_1 : treeBlockF 32 64 ch_21 = true := by decide +kernel
theorem nj_21_1 : ∀ i, 0 ≤ i → i < 64 → ch_21 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_21_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_21_1 h1 h2)
theorem nc_21 : ∀ i, 0 ≤ i → i < 64 → ch_21 i = true := nj_21_1
theorem lb_21 : LowerBin m_21 s_21 g_21 6 :=
  lowerDagV5 (kn_nil) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xcc003300cc003300
def s_22 : List Nat := [0x4400110044001100, 0x330000003300, 0xc0003000c000300, 0xcc003300]
def g_22 : Nat := 0x130004003300
def ep_22 : Nat := 0x400200000000000000000000000000000000000000002000400000000000000000000000000100004000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := []
def cc_22_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682b1560ac148a80d009c3382704a2941282314418810861042084108210420748e81d03a0740c901c001 0x7a3876346c3c68345c305d44564c5244484c4444382039342a48264022381e30144c10440c3c0834f63fea3be637de33d93fd53bc137ad33a92fa52b91277d23703f643b603758334c2f402b3c273423301f2c1b18170413000f 11 2047 5 31 10 1023 16 65535
def cc_22_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0a2a0a092898881808080808080646060606044404040404040242020202004 0xfc38f834f028ec24e230e344d24cce40c84cc440bd3cb934b418b014a3489f40983c94308d4c894484188014 8 255 3 7 10 1023 16 65535
def cur_22 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_22_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_22_0 p) (Nat.blt p 32)
def hc_22_0 : Nat → Nat := unpackHintV5 0xfa27b13925c04dc2654aea160aa084e126090d28223f11b24b905252140f0c6c63601910c805c428314009084802020d180b0002 0x0 13 8191 5 31
def hc_22_1 : Nat → Nat := unpackHintV5 0xa624a4a4091847a93541814a104a322191008044001e10d8c6c03221900b885062230e187003041800a1038c1c00a20500188006 0x0 13 8191 5 31
def hc_22_2 : Nat → Nat := unpackHintV5 0x4 0x0 6 63 3 7
def nh_22 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_22_2 (Nat.sub p 64)) (hc_22_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_22_0 p) (Nat.blt p 32)
def f_22 : Nat → Nat × Nat := unpackForestF 0xf838f834063fec28ec24063b0637e3440633053f053bc64cc640c44cc4400537b13cb134b018b0140533052f052b97489740943c94300527814c814480188014052376387634043f683c6834043b04375d440433524c5244042f444c4444042b042739340423041f041b1e481e401e381e300417084c0844083c08340413000f 6 10
def ch_22 : Nat → Bool := dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 64 (dagTraceF m_22 s_22 5 f_22) cur_22 nh_22
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 64 bds_22 (dagTraceF m_22 s_22 5 f_22) (cur_22 0) (nh_22 0) s_22 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22_0 : treeBlockF 0 32 ch_22 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22_1 : treeBlockF 32 64 ch_22 = true := by decide +kernel
theorem nj_22_1 : ∀ i, 0 ≤ i → i < 64 → ch_22 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_22_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_22_1 h1 h2)
theorem nc_22 : ∀ i, 0 ≤ i → i < 64 → ch_22 i = true := nj_22_1
theorem lb_22 : LowerBin m_22 s_22 g_22 6 :=
  lowerDagV5 (kn_nil) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0x3300330000330033
def s_23 : List Nat := [0x1100110000110011, 0x300030000030003, 0x330033, 0x330000000033]
def g_23 : Nat := 0x1100130000130033
def ep_23 : Nat := 0x200000000200000000000000000000002000002000000000000000000001100100000100000
def bds_23 : List (Nat × List Nat × Nat × Nat) := []
def cur_23 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44890e8701 0x192430919242090d24209263a88d9d3a54d903a10d800f 7 127 3 7 10 1023 14 16383
def nh_23 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_23 : Nat → Nat × Nat := unpackForestF 0xc7463629d6490a6c43a492209086c00f 3 10
def ch_23 : Nat → Bool := dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 10 (dagTraceF m_23 s_23 4 f_23) cur_23 nh_23
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 10 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) (nh_23 0) s_23 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23 : treeBlockF 0 10 ch_23 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 10 → ch_23 i = true := fun _ h1 h2 => treeBlockF_at nb_23 h1 h2
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV5 (kn_nil) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0xf0f00000f0f000
def s_24 : List Nat := [0x50500000505000, 0x30300000303000, 0xf0000000f000, 0xf0f000]
def g_24 : Nat := 0x10100000503000
def ep_24 : Nat := 0x40200000000000000000000000000000000000000000000000000000101000000030000010100000500000
def bds_24 : List (Nat × List Nat × Nat × Nat) := []
def cur_24 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x16588f 4 15 2 3 5 31 7 127
def nh_24 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_24 : Nat → Nat × Nat := unpackForestF 0x39c4f 1 5
def ch_24 : Nat → Bool := dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 3 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 3 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24 : treeBlockF 0 3 ch_24 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 3 → ch_24 i = true := fun _ h1 h2 => treeBlockF_at nb_24 h1 h2
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_nil) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0xf0f000000000f0f
def s_25 : List Nat := [0x505000000000505, 0x303000000000303, 0xf00000000000f, 0xf0f]
def g_25 : Nat := 0x107000000000f0f
def ep_25 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def nh_25 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) (nh_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 nh_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0xf00f0000f00f000
def s_26 : List Nat := [0x500500005005000, 0x300300003003000, 0xf0000000f000, 0xf00f000]
def g_26 : Nat := 0x100100005003000
def ep_26 : Nat := 0x400200000000000000000000000000000000000000000000000000001001000000030000100100005000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := []
def cur_26 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x16588f 4 15 2 3 5 31 7 127
def nh_26 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_26 : Nat → Nat × Nat := unpackForestF 0x39c4f 1 5
def ch_26 : Nat → Bool := dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 3 (dagTraceF m_26 s_26 4 f_26) cur_26 nh_26
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 3 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) (nh_26 0) s_26 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26 : treeBlockF 0 3 ch_26 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 3 → ch_26 i = true := fun _ h1 h2 => treeBlockF_at nb_26 h1 h2
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV5 (kn_nil) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0xf000f00f000f000
def s_27 : List Nat := [0x500050050005000, 0x300030030003000, 0xf000f000, 0xf000000f000]
def g_27 : Nat := 0x100070010003000
def ep_27 : Nat := 0x600000020000000000000000000000000000000000001000200100030000100040010000000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def nh_27 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) (nh_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 nh_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0xffff00000000
def s_28 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_28 : Nat := 0x177f00000000
def ep_28 : Nat := 0x6800000000000006080000000000001220000000000000144000000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13), (m_14, s_14, 4, g_14), (m_0, s_0, 4, g_0), (m_8, s_8, 4, g_8)]
def cc_28_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_28_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_28 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_28_1 (Nat.sub p 32)) (cc_28_0 p) (Nat.blt p 32)
def hc_28_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_28_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_28 : Nat → Nat := fun p => Bool.rec (hc_28_1 (Nat.sub p 32)) (hc_28_0 p) (Nat.blt p 32)
def f_28 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_28 : Nat → Bool := dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 43 (dagTraceF m_28 s_28 6 f_28) cur_28 nh_28
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 43 bds_28 (dagTraceF m_28 s_28 6 f_28) (cur_28 0) (nh_28 0) s_28 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_0 : treeBlockF 0 32 ch_28 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_1 : treeBlockF 32 43 ch_28 = true := by decide +kernel
theorem nj_28_1 : ∀ i, 0 ≤ i → i < 43 → ch_28 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_28_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_28_1 h1 h2)
theorem nc_28 : ∀ i, 0 ≤ i → i < 43 → ch_28 i = true := nj_28_1
theorem lb_28 : LowerBin m_28 s_28 g_28 7 :=
  lowerDagV5 (kn_cons lb_13 (kn_cons lb_14 (kn_cons lb_0 (kn_cons lb_8 (kn_nil))))) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0x6060606060606060
def s_29 : List Nat := [0x2020202020202020, 0x60006000600060, 0x606000006060, 0x60606060]
def g_29 : Nat := 0x6000402060
def ep_29 : Nat := 0x40200000000060000020200000006000400040000000000000000000000000000000000000000000000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := []
def cur_29 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xb9710f 4 15 2 3 6 63 8 255
def nh_29 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_29 : Nat → Nat × Nat := unpackForestF 0x1e788f 1 6
def ch_29 : Nat → Bool := dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 3 (dagTraceF m_29 s_29 4 f_29) cur_29 nh_29
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 3 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) (nh_29 0) s_29 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29 : treeBlockF 0 3 ch_29 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 3 → ch_29 i = true := fun _ h1 h2 => treeBlockF_at nb_29 h1 h2
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV5 (kn_nil) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0xffff000000000000
def s_30 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_30 : Nat := 0x1117000000000000
def ep_30 : Nat := 0x6000000000000000600000000000011120000000000001114000000000000
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_30 : Nat → List (Nat × Nat) := fun _ => []
def nh_30 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 0 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) (nh_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 0 (dagTraceF m_30 s_30 4 f_30) cur_30 nh_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0xff00ff0000000000
def s_31 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_31 : Nat := 0x1100170000000000
def ep_31 : Nat := 0x600000000000000000000000000000006000000000011001200000000001100140000000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def nh_31 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) (nh_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 nh_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0xff00ff00000000
def s_32 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_32 : Nat := 0x17007f00000000
def ep_32 : Nat := 0x68000000000000000000000000000600080000000000120020000000000014004000000000
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_7, s_7, 4, g_7), (m_3, s_3, 4, g_3), (m_2, s_2, 4, g_2)]
def cc_32_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_32_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_32 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_32_1 (Nat.sub p 32)) (cc_32_0 p) (Nat.blt p 32)
def hc_32_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_32_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_32 : Nat → Nat := fun p => Bool.rec (hc_32_1 (Nat.sub p 32)) (hc_32_0 p) (Nat.blt p 32)
def f_32 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_32 : Nat → Bool := dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 43 (dagTraceF m_32 s_32 6 f_32) cur_32 nh_32
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 43 bds_32 (dagTraceF m_32 s_32 6 f_32) (cur_32 0) (nh_32 0) s_32 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_0 : treeBlockF 0 32 ch_32 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_1 : treeBlockF 32 43 ch_32 = true := by decide +kernel
theorem nj_32_1 : ∀ i, 0 ≤ i → i < 43 → ch_32 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_32_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_32_1 h1 h2)
theorem nc_32 : ∀ i, 0 ≤ i → i < 43 → ch_32 i = true := nj_32_1
theorem lb_32 : LowerBin m_32 s_32 g_32 7 :=
  lowerDagV5 (kn_cons lb_4 (kn_cons lb_7 (kn_cons lb_3 (kn_cons lb_2 (kn_nil))))) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0xf0f0f0f000000000
def s_33 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_33 : Nat := 0x1010107000000000
def ep_33 : Nat := 0x60000000000000006000000000000000000000000010101020000000001010104000000000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def nh_33 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) (nh_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 nh_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0xf0f0f0f00000000
def s_34 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_34 : Nat := 0x107070f00000000
def ep_34 : Nat := 0x608000000000006000800000000000000000000000001020200000000000104040000000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_5, s_5, 4, g_5), (m_11, s_11, 4, g_11), (m_10, s_10, 4, g_10)]
def cc_34_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_34_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_34 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_34_1 (Nat.sub p 32)) (cc_34_0 p) (Nat.blt p 32)
def hc_34_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_34_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_34 : Nat → Nat := fun p => Bool.rec (hc_34_1 (Nat.sub p 32)) (hc_34_0 p) (Nat.blt p 32)
def f_34 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_34 : Nat → Bool := dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 43 (dagTraceF m_34 s_34 6 f_34) cur_34 nh_34
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 43 bds_34 (dagTraceF m_34 s_34 6 f_34) (cur_34 0) (nh_34 0) s_34 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_0 : treeBlockF 0 32 ch_34 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_1 : treeBlockF 32 43 ch_34 = true := by decide +kernel
theorem nj_34_1 : ∀ i, 0 ≤ i → i < 43 → ch_34 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_34_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_34_1 h1 h2)
theorem nc_34 : ∀ i, 0 ≤ i → i < 43 → ch_34 i = true := nj_34_1
theorem lb_34 : LowerBin m_34 s_34 g_34 7 :=
  lowerDagV5 (kn_cons lb_1 (kn_cons lb_5 (kn_cons lb_11 (kn_cons lb_10 (kn_nil))))) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0xcccccccc00000000
def s_35 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_35 : Nat := 0x4044c00000000
def ep_35 : Nat := 0x448000000000004004800000000000404080000000000000000000000000004044000000000
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_0, s_0, 4, g_0), (m_6, s_6, 4, g_6), (m_11, s_11, 4, g_11)]
def cc_35_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_35_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_35 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_35_1 (Nat.sub p 32)) (cc_35_0 p) (Nat.blt p 32)
def hc_35_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_35_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_35 : Nat → Nat := fun p => Bool.rec (hc_35_1 (Nat.sub p 32)) (hc_35_0 p) (Nat.blt p 32)
def f_35 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_35 : Nat → Bool := dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 43 (dagTraceF m_35 s_35 6 f_35) cur_35 nh_35
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 43 bds_35 (dagTraceF m_35 s_35 6 f_35) (cur_35 0) (nh_35 0) s_35 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_0 : treeBlockF 0 32 ch_35 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_1 : treeBlockF 32 43 ch_35 = true := by decide +kernel
theorem nj_35_1 : ∀ i, 0 ≤ i → i < 43 → ch_35 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_35_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_35_1 h1 h2)
theorem nc_35 : ∀ i, 0 ≤ i → i < 43 → ch_35 i = true := nj_35_1
theorem lb_35 : LowerBin m_35 s_35 g_35 7 :=
  lowerDagV5 (kn_cons lb_3 (kn_cons lb_0 (kn_cons lb_6 (kn_cons lb_11 (kn_nil))))) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0xcc00cc00cc00cc
def s_36 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_36 : Nat := 0x4004c0044004c
def ep_36 : Nat := 0x40000000000048000000080000000000000000000400080000000800000000000000000004004000440040
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def nh_36 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) (nh_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 nh_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0x3333333300000000
def s_37 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_37 : Nat := 0x1113133300000000
def ep_37 : Nat := 0x220000000000002002000000000000202000000000000000000000000001110100000000000
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def nh_37 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) (nh_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 nh_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0x4848484848484848
def s_38 : List Nat := [0x808080808080808, 0x48004800480048, 0x484800004848, 0x48484848]
def g_38 : Nat := 0x4800400848
def ep_38 : Nat := 0x40080000000048000008080000004800400040000000000000000000000000000000000000000000000000
def bds_38 : List (Nat × List Nat × Nat × Nat) := []
def cur_38 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xb9710f 4 15 2 3 6 63 8 255
def nh_38 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_38 : Nat → Nat × Nat := unpackForestF 0x1e788f 1 6
def ch_38 : Nat → Bool := dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 3 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 3 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38 : treeBlockF 0 3 ch_38 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 3 → ch_38 i = true := fun _ h1 h2 => treeBlockF_at nb_38 h1 h2
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_nil) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0x66666666
def s_39 : List Nat := [0x22222222, 0x6060606, 0x660066, 0x6666]
def g_39 : Nat := 0x4462666
def ep_39 : Nat := 0x22200000000000420040000000000402040000000000000000000000000000000000
def bds_39 : List (Nat × List Nat × Nat × Nat) := []
def cc_39_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xd43a8340de5bc168ad05a0ac5582b0560a4519a304608c1182304608c0f91f03e07c0f81f03e07c0d901d001 0xb878503c32a61f0f0f068742c381217090a0285c3c260a140f09848683e321e980b4b04a541d240a8d13060882c2c14120513020880c3c041a4b8fe34770e378519bf4fdd276dd376c99b54bda256cd275691aa0fd187c843b401b9b0cc8864402f1e158e09c4846201f0e0d8605c0826000f 11 2047 5 31 10 1023 17 131071
def cc_39_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xe0e0e0e0c4c0c0aba8a8a8a1929089888888815d515049484841401610090100 0xf93cf534f018ec14e44ce040903cc920c53cb414c524b524ca34c14cbd44b818b0146440a42499248a3e663da13d9d35943d9035881c684c 8 255 3 7 10 1023 16 65535
def cc_39_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x1e38dbb162c5878e1c234080c83 0x290f26a71313450264a4a24a4920288e124513220809c3c4c16418e20468944c 7 127 3 7 10 1023 17 131071
def cur_39 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_39_2 (Nat.sub p 64)) (cc_39_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_39_0 p) (Nat.blt p 32)
def hc_39_0 : Nat → Nat := unpackHintV5 0xde16d13605a46d016613285940ca0640b201900c805b4a9252ce8494109f88f44743352962494e3891b08c885c42830f280b8002 0x0 13 8191 5 31
def hc_39_1 : Nat → Nat := unpackHintV5 0xe226d23589a44c856213009708ae54c5a0acdd46262f11590a444e22320e9855024312008844022000f0870424a101051810c004 0x0 13 8191 5 31
def hc_39_2 : Nat → Nat := unpackHintV5 0x1522914a88c8fa1d2364594a11221c82542a041008 0x0 11 2047 4 15
def nh_39 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_39_2 (Nat.sub p 64)) (hc_39_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_39_0 p) (Nat.blt p 32)
def f_39 : Nat → Nat × Nat := unpackForestF 0x262713134031fc74a23a491c288e12018ee20991040031b818ce04710234029fbb4f1da68ec18760a014edc098e040029b814cc0a5e052b0293ac8d18a48b14c58a22c0616a48b0140291810fd4848913d489aa6491207a9035021f2207008760437381e1c0d0e05870240219920f8907a482d2e1e12094903a4c3c2612120540864042f02158109c5098284414160a0900846041f020d8105c10980844041e020d00826000f 7 10
def ch_39 : Nat → Bool := dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 78 (dagTraceF m_39 s_39 5 f_39) cur_39 nh_39
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 78 bds_39 (dagTraceF m_39 s_39 5 f_39) (cur_39 0) (nh_39 0) s_39 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_0 : treeBlockF 0 32 ch_39 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_1 : treeBlockF 32 64 ch_39 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_2 : treeBlockF 64 78 ch_39 = true := by decide +kernel
theorem nj_39_1 : ∀ i, 0 ≤ i → i < 64 → ch_39 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_39_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_39_1 h1 h2)
theorem nj_39_2 : ∀ i, 0 ≤ i → i < 78 → ch_39 i = true := block_join nj_39_1 (fun _ h1 h2 => treeBlockF_at nb_39_2 h1 h2)
theorem nc_39 : ∀ i, 0 ≤ i → i < 78 → ch_39 i = true := nj_39_2
theorem lb_39 : LowerBin m_39 s_39 g_39 6 :=
  lowerDagV5 (kn_nil) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xaaaaaaaa00000000
def s_40 : List Nat := [0x2222222200000000, 0xa0a0a0a00000000, 0xaa00aa00000000, 0xaaaa00000000]
def g_40 : Nat := 0x2022a00000000
def ep_40 : Nat := 0x228000000000002002800000000000202080000000000020220000000000000000000000000
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_8, s_8, 4, g_8), (m_9, s_9, 4, g_9), (m_10, s_10, 4, g_10)]
def cc_40_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_40_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_40 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_40_1 (Nat.sub p 32)) (cc_40_0 p) (Nat.blt p 32)
def hc_40_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_40_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_40 : Nat → Nat := fun p => Bool.rec (hc_40_1 (Nat.sub p 32)) (hc_40_0 p) (Nat.blt p 32)
def f_40 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_40 : Nat → Bool := dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 43 (dagTraceF m_40 s_40 6 f_40) cur_40 nh_40
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 43 bds_40 (dagTraceF m_40 s_40 6 f_40) (cur_40 0) (nh_40 0) s_40 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_0 : treeBlockF 0 32 ch_40 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_1 : treeBlockF 32 43 ch_40 = true := by decide +kernel
theorem nj_40_1 : ∀ i, 0 ≤ i → i < 43 → ch_40 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_40_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_40_1 h1 h2)
theorem nc_40 : ∀ i, 0 ≤ i → i < 43 → ch_40 i = true := nj_40_1
theorem lb_40 : LowerBin m_40 s_40 g_40 7 :=
  lowerDagV5 (kn_cons lb_2 (kn_cons lb_8 (kn_cons lb_9 (kn_cons lb_10 (kn_nil))))) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0x6666000066660000
def s_41 : List Nat := [0x2222000022220000, 0x606000006060000, 0x66000000660000, 0x66660000]
def g_41 : Nat := 0x6000004460000
def ep_41 : Nat := 0x440000000000000000000000006000000420000000600000402000000000000000000000000000000000000
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0x6600660066006600
def s_42 : List Nat := [0x2200220022002200, 0x600060006000600, 0x660000006600, 0x66006600]
def g_42 : Nat := 0x60004002600
def ep_42 : Nat := 0x400200000000600000022000000000000000000000006000400040000000000000000000000000000000000
def bds_42 : List (Nat × List Nat × Nat × Nat) := []
def cur_42 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xb9710f 4 15 2 3 6 63 8 255
def nh_42 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_42 : Nat → Nat × Nat := unpackForestF 0x1e788f 1 6
def ch_42 : Nat → Bool := dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 3 (dagTraceF m_42 s_42 4 f_42) cur_42 nh_42
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 3 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) (nh_42 0) s_42 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42 : treeBlockF 0 3 ch_42 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 3 → ch_42 i = true := fun _ h1 h2 => treeBlockF_at nb_42 h1 h2
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV5 (kn_nil) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0x5555000055550000
def s_43 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_43 : Nat := 0x1115000015550000
def ep_43 : Nat := 0x440000000000000000000000004000000400000000400000400000011100000100000000000000000000000
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def nh_43 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) (nh_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 nh_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xaa00aa00aa00aa00
def s_44 : List Nat := [0x2200220022002200, 0xa000a000a000a00, 0xaa000000aa00, 0xaa00aa00]
def g_44 : Nat := 0x20000002a00
def ep_44 : Nat := 0x28000000020000002a000000000000000000000002000000080000000200000020000000000000000000
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def nh_44 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) (nh_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 nh_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0xff000000ff00
def s_45 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_45 : Nat := 0x170000003f00
def ep_45 : Nat := 0x2800000000000000000000000000000000000000060000000c0000001200000030000000140000000000
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def nh_45 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) (nh_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 nh_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xf0f00000f0f0
def s_46 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_46 : Nat := 0x107000003070
def ep_46 : Nat := 0x200000000000000000000000006000000040000000000000000000001020000030200000104000000040
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def nh_46 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) (nh_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 nh_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0xf0f00000f0f0000
def s_47 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_47 : Nat := 0x107000005070000
def ep_47 : Nat := 0x400000000000000000000000006000000020000000000000000000001020000000200000104000005040000
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def nh_47 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) (nh_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 nh_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0xcccc0000cccc
def s_48 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_48 : Nat := 0x44c00000c4c
def ep_48 : Nat := 0x800000000000000000000000048000000400000040800000c0800000000000000000000044000000040
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def nh_48 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xaaaa0000aaaa
def s_49 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_49 : Nat := 0x22a00002a2a
def ep_49 : Nat := 0x280000000000000000000000002800000000000002080000080800000220000020200000000000000000
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def nh_49 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) (nh_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 nh_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0xcc00cc00cc00cc00
def s_50 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_50 : Nat := 0x40004000c00
def ep_50 : Nat := 0x4000800000004000000080000000000000000000000040004000c0000000000000000000000040004000000
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def nh_50 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) (nh_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 nh_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV5 (kn_cons lb_16 (kn_nil)) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0xf000f000f000f00
def s_51 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_51 : Nat := 0x100070005000f00
def ep_51 : Nat := 0x40008000000060000000a000000000000000000000000000000000001000200000000000100040005000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def nh_51 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 0 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) (nh_51 0) s_51 4 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 0 (dagTraceF m_51 s_51 4 f_51) cur_51 nh_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0xcccccccc
def s_52 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_52 : Nat := 0x4440c4c
def ep_52 : Nat := 0x80800000000004000400000000004000c0800000000000000000000000004440040
def bds_52 : List (Nat × List Nat × Nat × Nat) := []
def cur_52 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_52 : Nat → Nat := fun _ => 0
def f_52 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_52 : Nat → Bool := dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 1 (dagTraceF m_52 s_52 3 f_52) cur_52 nh_52
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 1 bds_52 (dagTraceF m_52 s_52 3 f_52) (cur_52 0) (nh_52 0) s_52 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52 : treeBlockF 0 1 ch_52 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 1 → ch_52 i = true := fun _ h1 h2 => treeBlockF_at nb_52 h1 h2
theorem lb_52 : LowerBin m_52 s_52 g_52 4 :=
  lowerDagV5 (kn_nil) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0x5555555500000000
def s_53 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_53 : Nat := 0x1115155500000000
def ep_53 : Nat := 0x440000000000004004000000000000404000000000011101000000000000000000000000000
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def nh_53 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 0 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) (nh_53 0) s_53 4 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 0 (dagTraceF m_53 s_53 4 f_53) cur_53 nh_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0xffff0000
def s_54 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_54 : Nat := 0x15570000
def ep_54 : Nat := 0x420000000000000402000000000000100200000000000015540000
def bds_54 : List (Nat × List Nat × Nat × Nat) := []
def cc_54_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_54_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_54 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_54_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_54_0 p) (Nat.blt p 32)
def hc_54_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_54_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_54_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_54 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_54_2 (Nat.sub p 64)) (hc_54_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_54_0 p) (Nat.blt p 32)
def f_54 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_54 : Nat → Bool := dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 64 (dagTraceF m_54 s_54 5 f_54) cur_54 nh_54
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 64 bds_54 (dagTraceF m_54 s_54 5 f_54) (cur_54 0) (nh_54 0) s_54 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_0 : treeBlockF 0 32 ch_54 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_1 : treeBlockF 32 64 ch_54 = true := by decide +kernel
theorem nj_54_1 : ∀ i, 0 ≤ i → i < 64 → ch_54 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_54_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_54_1 h1 h2)
theorem nc_54 : ∀ i, 0 ≤ i → i < 64 → ch_54 i = true := nj_54_1
theorem lb_54 : LowerBin m_54 s_54 g_54 6 :=
  lowerDagV5 (kn_nil) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0xf0f0f0f0
def s_55 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_55 : Nat := 0x10503070
def ep_55 : Nat := 0x20200000000000400040000000000000000000000000100030200000000010500040
def bds_55 : List (Nat × List Nat × Nat × Nat) := []
def cur_55 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_55 : Nat → Nat := fun _ => 0
def f_55 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_55 : Nat → Bool := dagCheckNodeV5 m_55 g_55 ep_55 1 1 bds_55 1 (dagTraceF m_55 s_55 3 f_55) cur_55 nh_55
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 1 1 1 bds_55 (dagTraceF m_55 s_55 3 f_55) (cur_55 0) (nh_55 0) s_55 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55 : treeBlockF 0 1 ch_55 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 1 → ch_55 i = true := fun _ h1 h2 => treeBlockF_at nb_55 h1 h2
theorem lb_55 : LowerBin m_55 s_55 g_55 4 :=
  lowerDagV5 (kn_nil) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0xaaaaaaaa
def s_56 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_56 : Nat := 0x22a2a
def ep_56 : Nat := 0x2a280000000000020000000000000002080800000000000220200000000000000000
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
def cur_56 : Nat → List (Nat × Nat) := fun _ => []
def nh_56 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_56 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 1 1 0 bds_56 (dagTraceF m_56 s_56 4 f_56) (cur_56 0) (nh_56 0) s_56 4 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_56 g_56 ep_56 1 1 bds_56 0 (dagTraceF m_56 s_56 4 f_56) cur_56 nh_56 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_56 : LowerBin m_56 s_56 g_56 5 :=
  lowerDagV5 (kn_cons lb_17 (kn_nil)) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0xf000f000f000f0
def s_57 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_57 : Nat := 0x10007000500070
def ep_57 : Nat := 0x40000000000060000000200000000000000000000000000000000000100020000000200010004000500040
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_57 : Nat → List (Nat × Nat) := fun _ => []
def nh_57 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_57 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 1 1 0 bds_57 (dagTraceF m_57 s_57 4 f_57) (cur_57 0) (nh_57 0) s_57 4 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_57 g_57 ep_57 1 1 bds_57 0 (dagTraceF m_57 s_57 4 f_57) cur_57 nh_57 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_57 : LowerBin m_57 s_57 g_57 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0xff000000ff0000
def s_58 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_58 : Nat := 0x17000000570000
def ep_58 : Nat := 0x40000000000000000000000000000000000000000600000002000000120000000200000014000000540000
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_58 : Nat → List (Nat × Nat) := fun _ => []
def nh_58 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_58 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 1 1 0 bds_58 (dagTraceF m_58 s_58 4 f_58) (cur_58 0) (nh_58 0) s_58 4 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_58 g_58 ep_58 1 1 bds_58 0 (dagTraceF m_58 s_58 4 f_58) cur_58 nh_58 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_58 : LowerBin m_58 s_58 g_58 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0x5050a0a05050a0a0
def s_59 : List Nat := [0xa0a00000a0a0, 0x1010202010102020, 0x5000a0005000a0, 0x5050a0a0]
def g_59 : Nat := 0x1010002010502020
def ep_59 : Nat := 0x40200000000000000000000000002000400000000000000000000010100020100020200000000000000000
def bds_59 : List (Nat × List Nat × Nat × Nat) := []
def cc_59_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f05e03a1740e81b13606c0c881c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d342028212c1a3816300c3c0834fe3ffa3be637d233bd3fa93ba537a1339d2f952b89277d23783f743b60374c33402f342b30272823241f1c1b10170413000f 11 2047 5 31 10 1023 16 65535
def cc_59_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070705450505050343030292821202012101002 0xf54cf140ec4ce840e128dd24d828d424ce38ca34c438c034b93cb534b018ac1499389a3c903c8c3084188014 8 255 3 7 10 1023 16 65535
def cur_59 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_59_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_59_0 p) (Nat.blt p 32)
def hc_59_0 : Nat → Nat := unpackHintV5 0xb47533a981444a0150025952c0922480a4010ca8414109d1ce4270131394a090a3881a10c845c42e0151090c4802020d180b0002 0x0 13 8191 5 31
def hc_59_1 : Nat → Nat := unpackHintV5 0xadd50aa0540a091aa21440881011b53606c0d81b0306600c018030054c918f31a4304510a010414c28032006 0x0 11 2047 4 15
def hc_59_2 : Nat → Nat := unpackHintV5 0xe 0x0 8 255 4 15
def nh_59 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_59_2 (Nat.sub p 64)) (hc_59_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_59_0 p) (Nat.blt p 32)
def f_59 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c238c234c038c034053fad3cad34ac18ac14053b05370533052f9a3c052b8c3c8c300527801880140523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423041f212c041b163816300417083c08340413000f 6 10
def ch_59 : Nat → Bool := dagCheckNodeV5 m_59 g_59 ep_59 1 1 bds_59 64 (dagTraceF m_59 s_59 5 f_59) cur_59 nh_59
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 1 1 64 bds_59 (dagTraceF m_59 s_59 5 f_59) (cur_59 0) (nh_59 0) s_59 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_0 : treeBlockF 0 32 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_1 : treeBlockF 32 64 ch_59 = true := by decide +kernel
theorem nj_59_1 : ∀ i, 0 ≤ i → i < 64 → ch_59 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_59_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_59_1 h1 h2)
theorem nc_59 : ∀ i, 0 ≤ i → i < 64 → ch_59 i = true := nj_59_1
theorem lb_59 : LowerBin m_59 s_59 g_59 6 :=
  lowerDagV5 (kn_nil) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0x5555aaaa00000000
def s_60 : List Nat := [0xaaaa00000000, 0x1111222200000000, 0x5050a0a00000000, 0x5500aa00000000]
def g_60 : Nat := 0x1115022a00000000
def ep_60 : Nat := 0x4002800000000000402080000000011100220000000000000000000000000
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_60 : Nat → List (Nat × Nat) := fun _ => []
def nh_60 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_60 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 1 1 0 bds_60 (dagTraceF m_60 s_60 4 f_60) (cur_60 0) (nh_60 0) s_60 4 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_60 g_60 ep_60 1 1 bds_60 0 (dagTraceF m_60 s_60 4 f_60) cur_60 nh_60 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_60 : LowerBin m_60 s_60 g_60 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0x4444444444444444
def s_61 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_61 : Nat := 0x4044404440444
def ep_61 : Nat := 0x440000000000440000000000004004000400040000404000400040000000000000000000000000000000000
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_61 : Nat → List (Nat × Nat) := fun _ => []
def nh_61 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_61 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 1 1 0 bds_61 (dagTraceF m_61 s_61 4 f_61) (cur_61 0) (nh_61 0) s_61 4 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_61 g_61 ep_61 1 1 bds_61 0 (dagTraceF m_61 s_61 4 f_61) cur_61 nh_61 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_61 : LowerBin m_61 s_61 g_61 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_61 nc_61 (by decide +kernel)

def m_62 : Nat := 0x2222222222222222
def s_62 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_62 : Nat := 0x2022200022222
def ep_62 : Nat := 0x200000000220000022200002002000020000000202000002000000000000000000000000000000000000
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_62 : Nat → List (Nat × Nat) := fun _ => []
def nh_62 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_62 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 m_62 g_62 ep_62 1 1 0 bds_62 (dagTraceF m_62 s_62 4 f_62) (cur_62 0) (nh_62 0) s_62 4 = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_62 g_62 ep_62 1 1 bds_62 0 (dagTraceF m_62 s_62 4 f_62) cur_62 nh_62 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_62 : LowerBin m_62 s_62 g_62 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_62 nc_62 (by decide +kernel)

def m_63 : Nat := 0xa500a500a500a500
def s_63 : List Nat := [0x500050005000500, 0x2100210021002100, 0xa5000000a500, 0xa500a500]
def g_63 : Nat := 0x100050005002500
def ep_63 : Nat := 0x400200000000400000020000000000000000000000000000000000001000000000020000000000000000000
def bds_63 : List (Nat × List Nat × Nat × Nat) := []
def cc_63_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0x793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_63_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014 8 255 3 7 10 1023 16 65535
def cur_63 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_63_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_63_0 p) (Nat.blt p 32)
def hc_63_0 : Nat → Nat := unpackHintV5 0xfa27b13925c04dc2654aea160aa084d1a50d28090248023090c68604112080fc47833a11c08bd25a22b111246902a50d400b0002 0x0 13 8191 5 31
def hc_63_1 : Nat → Nat := unpackHintV5 0xa2351027893c09a24a1a501204900461218d0447e23649a08c845292140e145102230e187003041800a1038c1c00a20500188006 0x0 13 8191 5 31
def hc_63_2 : Nat → Nat := unpackHintV5 0x6 0x0 6 63 3 7
def nh_63 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_63_2 (Nat.sub p 64)) (hc_63_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_63_0 p) (Nat.blt p 32)
def f_63 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def ch_63 : Nat → Bool := dagCheckNodeV5 m_63 g_63 ep_63 1 1 bds_63 64 (dagTraceF m_63 s_63 5 f_63) cur_63 nh_63
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV5 m_63 g_63 ep_63 1 1 64 bds_63 (dagTraceF m_63 s_63 5 f_63) (cur_63 0) (nh_63 0) s_63 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_0 : treeBlockF 0 32 ch_63 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_1 : treeBlockF 32 64 ch_63 = true := by decide +kernel
theorem nj_63_1 : ∀ i, 0 ≤ i → i < 64 → ch_63 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_63_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_63_1 h1 h2)
theorem nc_63 : ∀ i, 0 ≤ i → i < 64 → ch_63 i = true := nj_63_1
theorem lb_63 : LowerBin m_63 s_63 g_63 6 :=
  lowerDagV5 (kn_nil) rc_63 nc_63 (by decide +kernel)

def m_64 : Nat := 0x5a5a00005a5a0000
def s_64 : List Nat := [0xa0a00000a0a0000, 0x1212000012120000, 0x5a0000005a0000, 0x5a5a0000]
def g_64 : Nat := 0x1012000010520000
def ep_64 : Nat := 0x40000000000000000000000002000000420000000000000000000010120000100200000000000000000000
def bds_64 : List (Nat × List Nat × Nat × Nat) := []
def cur_64 : Nat → List (Nat × Nat) := unpackCursorV5 0xb162c4a91220c072e0701 0x4cf2060a2031250e9c6cc2a413107842400f 7 127 3 7 9 511 13 8191
def nh_64 : Nat → Nat := unpackHintV5 0xb89702e0582a8550281500984f202e002 0x0 11 2047 5 31
def f_64 : Nat → Nat × Nat := unpackForestF 0x8ea27903011b08a9440226312087842400f 4 9
def ch_64 : Nat → Bool := dagCheckNodeV5 m_64 g_64 ep_64 1 1 bds_64 11 (dagTraceF m_64 s_64 4 f_64) cur_64 nh_64
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV5 m_64 g_64 ep_64 1 1 11 bds_64 (dagTraceF m_64 s_64 4 f_64) (cur_64 0) (nh_64 0) s_64 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64 : treeBlockF 0 11 ch_64 = true := by decide +kernel
theorem nc_64 : ∀ i, 0 ≤ i → i < 11 → ch_64 i = true := fun _ h1 h2 => treeBlockF_at nb_64 h1 h2
theorem lb_64 : LowerBin m_64 s_64 g_64 5 :=
  lowerDagV5 (kn_nil) rc_64 nc_64 (by decide +kernel)

def m_65 : Nat := 0xa0a0a0a0a0a0a0a
def s_65 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_65 : Nat := 0x2020a00020a0a
def ep_65 : Nat := 0x8000000020800000a080002000800020000000000000000000000020200000200000000000000000000
def bds_65 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_65 : Nat → List (Nat × Nat) := fun _ => []
def nh_65 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_65 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV5 m_65 g_65 ep_65 1 1 0 bds_65 (dagTraceF m_65 s_65 4 f_65) (cur_65 0) (nh_65 0) s_65 4 = true := by decide +kernel
theorem nc_65 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_65 g_65 ep_65 1 1 bds_65 0 (dagTraceF m_65 s_65 4 f_65) cur_65 nh_65 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_65 : LowerBin m_65 s_65 g_65 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_65 nc_65 (by decide +kernel)

def m_66 : Nat := 0xa050a050a050a050
def s_66 : List Nat := [0x50005000500050, 0x2010201020102010, 0xa0500000a050, 0xa050a050]
def g_66 : Nat := 0x10005000502050
def ep_66 : Nat := 0x40200000000040000020000000000000000000000000000000000000100000000020000000000000000000
def bds_66 : List (Nat × List Nat × Nat × Nat) := []
def cc_66_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0x793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_66_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014 8 255 3 7 10 1023 16 65535
def cur_66 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_66_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_66_0 p) (Nat.blt p 32)
def hc_66_0 : Nat → Nat := unpackHintV5 0xfa27b13925c04dc2654aea160aa084d1a50d28090248023090c68604112080fc47833a11c08bd25a22b111246902a50d400b0002 0x0 13 8191 5 31
def hc_66_1 : Nat → Nat := unpackHintV5 0xa2351027893c09a24a1a501204900461218d0447e23649a08c845292140e145102230e187003041800a1038c1c00a20500188006 0x0 13 8191 5 31
def hc_66_2 : Nat → Nat := unpackHintV5 0x6 0x0 6 63 3 7
def nh_66 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_66_2 (Nat.sub p 64)) (hc_66_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_66_0 p) (Nat.blt p 32)
def f_66 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def ch_66 : Nat → Bool := dagCheckNodeV5 m_66 g_66 ep_66 1 1 bds_66 64 (dagTraceF m_66 s_66 5 f_66) cur_66 nh_66
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV5 m_66 g_66 ep_66 1 1 64 bds_66 (dagTraceF m_66 s_66 5 f_66) (cur_66 0) (nh_66 0) s_66 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_0 : treeBlockF 0 32 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_1 : treeBlockF 32 64 ch_66 = true := by decide +kernel
theorem nj_66_1 : ∀ i, 0 ≤ i → i < 64 → ch_66 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_66_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_66_1 h1 h2)
theorem nc_66 : ∀ i, 0 ≤ i → i < 64 → ch_66 i = true := nj_66_1
theorem lb_66 : LowerBin m_66 s_66 g_66 6 :=
  lowerDagV5 (kn_nil) rc_66 nc_66 (by decide +kernel)

def m_67 : Nat := 0xf0f0f0f0f0f0f0f0
def s_67 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_67 : Nat := 0x1010107010503070
def ep_67 : Nat := 0x40200000000060000020200000006000400040000000000000000010101020100030201010104010500040
def bds_67 : List (Nat × List Nat × Nat × Nat) := [(m_33, s_33, 5, g_33), (m_46, s_46, 5, g_46), (m_57, s_57, 5, g_57), (m_55, s_55, 4, g_55), (m_29, s_29, 5, g_29), (m_66, s_66, 6, g_66), (m_21, s_21, 6, g_21), (m_59, s_59, 6, g_59), (m_18, s_18, 6, g_18), (m_13, s_13, 4, g_13), (m_4, s_4, 4, g_4), (m_24, s_24, 5, g_24)]
def cc_67_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xaceb0a0e80a0280a023588611805f17c1f07c1f06d1655816050940501224812040900400e207401 0x204bcfa525498a88c9d29cc9426e2f351493464c95a60ab24051102880143c0a249091474814a3c992cd495694a25a4d211c050c6925b4525ae90d4466bc2b560e2d0514af69f5b4ba5a3cad0e1486f23b70a5ae4ccd246504f1c23880fc106e001f 10 1023 4 15 11 2047 17 131071
def cc_67_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb8959090906d68535050502d282828050000 0x5cd6ad6b382497d20b64c6e8bd6c5d9128d84e592633c5da1aed417286bd3b4e8d28b4506606924598e28be92a248cb131 8 255 3 7 11 2047 17 131071
def cur_67 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_67_1 (Nat.sub p 32)) (cc_67_0 p) (Nat.blt p 32)
def hc_67_0 : Nat → Nat := unpackHintV5 0x7bd71e11c6cd71b0066a439a90065c91695c588395b0e550394d0e534014d00534014d00514410b7442c01011434978d20032050995e264008f1418178600015850275e001380000 0xbaa7971cba9793d3df830317a71c0d67533d5473cba2d4db4303279e759e2c79c314d3d67531d57a5d3db4303272d9e7679e9cfa944a959674cb2d35cf3d756000db08c313c39c030e7e0d4d0c270c0c0c20c5e9c300c3838b435b0c0c09c0c3062c39c30c25e0d6d0c30270c0c0c14d9c30c30839f434f030c0c09c8322ea5d534f59007c86c4 18 262143 7 127
def hc_67_1 : Nat → Nat := unpackHintV5 0xa902250549281a44068f021e8547a0015890548194c0653000b09c2a8189c0e1e0901c5c000700000 0x31c79c71c71e93d3cf0c0c1c7039c71c71c71cb8b8b50c0c1c71c71c79c7a1e1cb2c751d1cf3c70c0c709e71c71c79c71cb875d71e873d1d34c751c31c070c9e79ea71e74f0c8ba9e5e971e2e53537e0c0c9c74d03 18 262143 8 255
def nh_67 : Nat → Nat := fun p => Bool.rec (hc_67_1 (Nat.sub p 32)) (hc_67_0 p) (Nat.blt p 32)
def f_67 : Nat → Nat × Nat := unpackForestF 0x1824905a7d917ac8bb613905a5d4170168f335e99a74c0d0168714598a28c49181486fa5e7d29028edd29c094b622f3114982b4c15604999cd48e694725a39211e908f474794a3c991c05012465b492da28213c86ba435104238ad7856ac083f0a2d05148106e001f 6 11
def ch_67 : Nat → Bool := dagCheckNodeV5 m_67 g_67 ep_67 4 15 bds_67 49 (dagTraceF m_67 s_67 7 f_67) cur_67 nh_67
set_option maxHeartbeats 0 in
theorem rc_67 : dagCheckRootsV5 m_67 g_67 ep_67 4 15 49 bds_67 (dagTraceF m_67 s_67 7 f_67) (cur_67 0) (nh_67 0) s_67 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_0 : treeBlockF 0 32 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_1 : treeBlockF 32 49 ch_67 = true := by decide +kernel
theorem nj_67_1 : ∀ i, 0 ≤ i → i < 49 → ch_67 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_67_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_67_1 h1 h2)
theorem nc_67 : ∀ i, 0 ≤ i → i < 49 → ch_67 i = true := nj_67_1
theorem lb_67 : LowerBin m_67 s_67 g_67 8 :=
  lowerDagV5 (kn_cons lb_33 (kn_cons lb_46 (kn_cons lb_57 (kn_cons lb_55 (kn_cons lb_29 (kn_cons lb_66 (kn_cons lb_21 (kn_cons lb_59 (kn_cons lb_18 (kn_cons lb_13 (kn_cons lb_4 (kn_cons lb_24 (kn_nil))))))))))))) rc_67 nc_67 (by decide +kernel)

def m_68 : Nat := 0xcccccccccccccccc
def s_68 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_68 : Nat := 0x4044c04440c4c
def ep_68 : Nat := 0x4400800000004480000080800040048004000400004040804000c0800000000000000000004044004440040
def bds_68 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16), (m_35, s_35, 7, g_35), (m_15, s_15, 4, g_15), (m_48, s_48, 5, g_48), (m_36, s_36, 5, g_36), (m_52, s_52, 4, g_52), (m_38, s_38, 5, g_38), (m_11, s_11, 4, g_11), (m_0, s_0, 4, g_0)]
def cc_68_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xf81aa6e3dc0b81702d0da0b03412804e19c1306604c094328240c80847082103e27c0f81d1343680c841c001 0xa91f94a3b2646e488cc5c9f1183b200663e0ac78119cb4f3769666d1cbda18b24e2b29c3a05065aa0b8141b8a634d78612f8b15214028251483d2f0694e096c00cd402da404c510849c0d148152f05453076a408d08080a51b4fa169736d1e61a1caa4f934972291e4121c7a3f8d477008ddd519b614f602967451c70a18a93f13276224dc40998712f0c2560649c04918001f 11 2047 5 31 11 2047 19 524287
def cc_68_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x98251942145e9525413244910440c5300c02c483200801c45214050140500c830084200802000800 0x7cd02012f7e4ade9277848efb5cbcd46bb50ac972aa50a68fe823b928de0a3376171715c54051c13452051695c50051b5606a571614c681713014620b19134600d120145b141724d5891544504e1012828440f10834 10 1023 4 15 11 2047 18 262143
def cc_68_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x8642211087d3e1d4cc6432190ba5c2e146a04924104803c9548440200e47038150140000 0x2a24da49266245909066c50b6132325cb2092ea3fb88eed237b08cea460801b29460a29b1f86c9b141f05c9b142584c969427c609d14263607a1b2504c8c97220248cd4223508654244608e9b22a5c781b21024 9 511 3 7 11 2047 18 262143
def cc_68_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x94a5094250942328c2306a5374c1304c13044910440f22d0b02c0a1280a0280731c0701485001400 0x3795d8a557d818f4053ea4ef852fc943dc13f184b8411d8043f007fb813fed7bf25eda57f115b8255d7953ec0939460e21337a6cdc093a23fe68ef8237da8cf5134d1583395ccc1732134c60d35b4fd2d2f2b47c4d0f094e 10 1023 4 15 11 2047 18 262143
def cc_68_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xd0340d02f5bc2f0a96a0a8264982519424190204801b56c1745c1705c152541323d0f03c0b406801 0xa04b93e94278ae4e9509c0b92e97e691b8d94f9926e1449e5da9cb3497f464304fe501249351742bed656d4cab9c9538e4bce657da4ada8157372a6e4575a0aca7155362a29b14220261695c86029144fe249dc393785266e213d9825a504734087191622e2942450702beca56d24ab99953832990450204263e824 10 1023 4 15 11 2047 19 524287
def cc_68_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x3440 0x28a2f5134e 3 7 1 1 11 2047 19 524287
def cur_68 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_68_5 (Nat.sub p 160)) (cc_68_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_68_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_68_2 (Nat.sub p 64)) (cc_68_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_68_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def hc_68_0 : Nat → Nat := unpackHintV5 0x8fa058a852810987ee227b23c7b200789297810875e236a8b6654545b3a1572414da9842dad3f93435d9c3293428d9c28d002622b25111251002143d20311203001c63d11da90c558020a50002000000 0x2eaaaaaa6aaaa955ad6b95aaaaaaab755555544545478a95555555555595dbeaab70e1cf22387288a954e31ec3c3d95555403816481d50c7510003180ce10ea0b614004305541555514555000000aa00000aa0000950020000aa0b6000040400000010aa0000aa00a0800000005016ea9554080000000000002a8060016c01544004000154a2a2002aaa802d85055554382a3800aa8228aaaaaaa00000155410aa0000000100000015400016c0006aa00000220ab54500004000aa4544401550416e82aaaa00a8700aa8228aaaaabb818de1e1ef7b071e860f28aa225553eed814f060030000554818ea8631800ce400555430800a0b6aa82aaaa28aa004000154000015400012a0040001540000016c80800000021540001540141055555555 20 1048575 8 255
def hc_68_1 : Nat → Nat := unpackHintV5 0x9c40259189283dea60522892f194bc010f203e854ea1036c3cb52629044a4002682886141fc1c7f001e01c463210414350c0d40030050744c1d0004c280a09028000a00014140005 0x175db1db5de5577baea977baeaa569aaaaaaa2a2aaa8f15455555556eaaa995555555555555dec384ef70c390ef6074d8b76b9dbd8e080ebbdabdaf7b214deea82a3872889577b87bb6397b5ee77b 18 262143 8 255
def hc_68_2 : Nat → Nat := unpackHintV5 0x98654b816570b2b8091c848e023720f3d062ee27741340e8a2043c2a0c24eb366919308818400b2205900268c0e8985f2a279013c00901c480021850c0981498050a0005 0x551451c3955510aaaabbddb1cee86d55554d55552aaaaaaaad5551ce73d355552aaaaaaa8000005300002a80002a9b0839cdeddd6c39b23696cd8b439b6d8e66b0e6c8839bd8e5dee8696d69bd8717b0e6c8b70d77b 17 131071 7 127
def hc_68_3 : Nat → Nat := unpackHintV5 0xf30cbc408eec27bb00eec03b605ec417ac05d694ac298ab456911ca281e8505994825e0796416401969271881c6200178105cc156a09594154a1b528013e0c47880e43a142500050 0x70e5500d8ef6b000000016b000000005ac0000000360100000000010305500000050415481ef7b191b866f7103dec726f7b8646daaaa2a21d5438a8ab755543aaaa555555555555dece107dec8d9b376f6382761f7b861c868a28e1caa22555aaaaab755555555115151e2a5555555555555000000a6000055000055 18 262143 8 255
def hc_68_4 : Nat → Nat := unpackHintV5 0x9f6509a254952508ada589914885147dea77bc227803c6cab6676545d5a1594414fc9844fad3b39c3793a2e5942955024b4a2460524105241002311023100221101d1501755c125500c560023a200023 0x2a80000000001555400000080002a8000154000156540000000002aaa80000200008d8000000000400155000002000aaa0000abb0039b2a1c1446c0a8200079c0e154453c743a21550555545154dbc00d871e001c000070e550080381ce46e82a0e0551c7471d0451c955555504551540080001640002a80002a80008d8000100000055000001102a8000002820ab000501b0002aa1550028222a3d011b00aaaaaa8228555555411455000002360001c000002a80020008182a8000200882a80010070038001b0000001801002a800800802a800000000e1caa2000006c00020000000002060aa000080220aa00000001540000aa00aa00000000003872aaa8ef61cdbb03a0000000000000aa008aa318c60000000000aaaa0000000001540000aa0000ab35cd60000000000b9cd60000040000000000001b0180040000aa08002800022a8011c0801 20 1048575 8 255
def hc_68_5 : Nat → Nat := unpackHintV5 0x1759c500d4a49c151400054 0x46c00000000000aa0206000400aa02200000aa21b010002aa5523614054100050470aa82aaaa2855415555145500000000aa00005500550000000aa000055000055 18 262143 8 255
def nh_68 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (hc_68_5 (Nat.sub p 160)) (hc_68_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_68_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_68_2 (Nat.sub p 64)) (hc_68_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_68_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_68 : Nat → Nat × Nat := unpackForestF 0x169f44d3805a5ce25c9c4a13857270a84e05c0168f328de649b80b43966a72cd240527ca0240149724d44052380a430147f1c978051dc0c58818a50a4fe149dc404c8526f0c0521499c0c508129902502042600a37766bcec979dd273b94b7a030f4051dca1bb81f77026ec0900519b6a3f6d476e3181c42636a376e4d8dc091b5198094f6169ed44d185a5b3560662b8cc17185a3b193463068c2d0d84a70094b3b6b876d45611fac23b5b098b08dd64122c2333b6a076970ed282a4603b47ea318145361da3b4a8c0951413628253604b4a094130ed1ba1460424d88cd41092e21b50432a084090ed199e12f3c2567cd00f0939e1233b0b80251c75a79c1341d69669580d0ae1a05c1d68e604d0c416180341d68658934b628162451d29c3c8fc791d93c50270803c8dc94140f2331e076420f0841a0f0331e0563c08c740a00943168a62cd7865aa0b25f170282c548049f8a0140127625148049b809330f4bc024bc34a70092b0b6900914c22288424e046a40b148152f023420124e0405004918001f 8 11
def ch_68 : Nat → Bool := dagCheckNodeV5 m_68 g_68 ep_68 3 7 bds_68 164 (dagTraceF m_68 s_68 8 f_68) cur_68 nh_68
set_option maxHeartbeats 0 in
theorem rc_68 : dagCheckRootsV5 m_68 g_68 ep_68 3 7 164 bds_68 (dagTraceF m_68 s_68 8 f_68) (cur_68 0) (nh_68 0) s_68 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_0 : treeBlockF 0 32 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_1 : treeBlockF 32 64 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_2 : treeBlockF 64 96 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_3 : treeBlockF 96 128 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_4 : treeBlockF 128 160 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_5 : treeBlockF 160 164 ch_68 = true := by decide +kernel
theorem nj_68_1 : ∀ i, 0 ≤ i → i < 64 → ch_68 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_68_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_68_1 h1 h2)
theorem nj_68_2 : ∀ i, 0 ≤ i → i < 96 → ch_68 i = true := block_join nj_68_1 (fun _ h1 h2 => treeBlockF_at nb_68_2 h1 h2)
theorem nj_68_3 : ∀ i, 0 ≤ i → i < 128 → ch_68 i = true := block_join nj_68_2 (fun _ h1 h2 => treeBlockF_at nb_68_3 h1 h2)
theorem nj_68_4 : ∀ i, 0 ≤ i → i < 160 → ch_68 i = true := block_join nj_68_3 (fun _ h1 h2 => treeBlockF_at nb_68_4 h1 h2)
theorem nj_68_5 : ∀ i, 0 ≤ i → i < 164 → ch_68 i = true := block_join nj_68_4 (fun _ h1 h2 => treeBlockF_at nb_68_5 h1 h2)
theorem nc_68 : ∀ i, 0 ≤ i → i < 164 → ch_68 i = true := nj_68_5
theorem lb_68 : LowerBin m_68 s_68 g_68 9 :=
  lowerDagV5 (kn_cons lb_16 (kn_cons lb_35 (kn_cons lb_15 (kn_cons lb_48 (kn_cons lb_36 (kn_cons lb_52 (kn_cons lb_38 (kn_cons lb_11 (kn_cons lb_0 (kn_nil)))))))))) rc_68 nc_68 (by decide +kernel)

def m_69 : Nat := 0xff00ff00ff00ff00
def s_69 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_69 : Nat := 0x1100170015003f00
def ep_69 : Nat := 0x40028000000060000002a0000000000000000000000060004000c0011001200100030001100140015000000
def bds_69 : List (Nat × List Nat × Nat × Nat) := [(m_31, s_31, 5, g_31), (m_45, s_45, 5, g_45), (m_50, s_50, 5, g_50), (m_51, s_51, 5, g_51), (m_44, s_44, 5, g_44), (m_14, s_14, 4, g_14), (m_5, s_5, 4, g_5), (m_42, s_42, 5, g_42), (m_16, s_16, 4, g_16), (m_12, s_12, 4, g_12), (m_22, s_22, 6, g_22), (m_63, s_63, 6, g_63)]
def cur_69 : Nat → List (Nat × Nat) := unpackCursorV5 0x28499121d3870a8601 0x202eab5d206c716882b3b476246811c41b801f 7 127 3 7 11 2047 15 32767
def nh_69 : Nat → Nat := unpackHintV5 0x8b001dc5056a095a003e188f8003b828846a002100000 0xa1e1ea9c34c35d4d6c4c0c75c36d64359c76db1e5d7950c00b0b024e0cf0cf4b4b51c1c09c3c187874c700cf0cf834b4b22027032c1e838c31e5c396d1d7d90d1c203c0c2c4 18 262143 8 255
def f_69 : Nat → Nat × Nat := unpackForestF 0x405d168e248d5ae884728b4415841b801f 4 11
def ch_69 : Nat → Bool := dagCheckNodeV5 m_69 g_69 ep_69 4 15 bds_69 9 (dagTraceF m_69 s_69 7 f_69) cur_69 nh_69
set_option maxHeartbeats 0 in
theorem rc_69 : dagCheckRootsV5 m_69 g_69 ep_69 4 15 9 bds_69 (dagTraceF m_69 s_69 7 f_69) (cur_69 0) (nh_69 0) s_69 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69 : treeBlockF 0 9 ch_69 = true := by decide +kernel
theorem nc_69 : ∀ i, 0 ≤ i → i < 9 → ch_69 i = true := fun _ h1 h2 => treeBlockF_at nb_69 h1 h2
theorem lb_69 : LowerBin m_69 s_69 g_69 8 :=
  lowerDagV5 (kn_cons lb_31 (kn_cons lb_45 (kn_cons lb_50 (kn_cons lb_51 (kn_cons lb_44 (kn_cons lb_14 (kn_cons lb_5 (kn_cons lb_42 (kn_cons lb_16 (kn_cons lb_12 (kn_cons lb_22 (kn_cons lb_63 (kn_nil))))))))))))) rc_69 nc_69 (by decide +kernel)

def m_70 : Nat := 0xf0f0f0f0f0f0f0f
def s_70 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_70 : Nat := 0x107070f05070f0f
def ep_70 : Nat := 0x40008000000060800000a080006000800020000000000000000000001020200000200000104040005040000
def bds_70 : List (Nat × List Nat × Nat × Nat) := [(m_34, s_34, 7, g_34)]
def cur_70 : Nat → List (Nat × Nat) := fun _ => []
def nh_70 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_70 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_70 : dagCheckRootsV5 m_70 g_70 ep_70 1 1 0 bds_70 (dagTraceF m_70 s_70 7 f_70) (cur_70 0) (nh_70 0) s_70 7 = true := by decide +kernel
theorem nc_70 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_70 g_70 ep_70 1 1 bds_70 0 (dagTraceF m_70 s_70 7 f_70) cur_70 nh_70 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_70 : LowerBin m_70 s_70 g_70 8 :=
  lowerDagV5 (kn_cons lb_34 (kn_nil)) rc_70 nc_70 (by decide +kernel)

def m_71 : Nat := 0xaaaaaaaaaaaaaaaa
def s_71 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_71 : Nat := 0x2022a00022a2a
def ep_71 : Nat := 0x28000000022800002a280002002800020000000202080002080800020220000220200000000000000000
def bds_71 : List (Nat × List Nat × Nat × Nat) := [(m_40, s_40, 7, g_40)]
def cur_71 : Nat → List (Nat × Nat) := fun _ => []
def nh_71 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_71 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_71 : dagCheckRootsV5 m_71 g_71 ep_71 1 1 0 bds_71 (dagTraceF m_71 s_71 7 f_71) (cur_71 0) (nh_71 0) s_71 7 = true := by decide +kernel
theorem nc_71 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_71 g_71 ep_71 1 1 bds_71 0 (dagTraceF m_71 s_71 7 f_71) cur_71 nh_71 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_71 : LowerBin m_71 s_71 g_71 8 :=
  lowerDagV5 (kn_cons lb_40 (kn_nil)) rc_71 nc_71 (by decide +kernel)

def m_72 : Nat := 0xff00ff00ff00ff
def s_72 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_72 : Nat := 0x17007f0057007f
def ep_72 : Nat := 0x40000000000068000000280000000000000000000600080002000800120020000200200014004000540040
def bds_72 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 7, g_32)]
def cur_72 : Nat → List (Nat × Nat) := fun _ => []
def nh_72 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_72 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_72 : dagCheckRootsV5 m_72 g_72 ep_72 1 1 0 bds_72 (dagTraceF m_72 s_72 7 f_72) (cur_72 0) (nh_72 0) s_72 7 = true := by decide +kernel
theorem nc_72 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_72 g_72 ep_72 1 1 bds_72 0 (dagTraceF m_72 s_72 7 f_72) cur_72 nh_72 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_72 : LowerBin m_72 s_72 g_72 8 :=
  lowerDagV5 (kn_cons lb_32 (kn_nil)) rc_72 nc_72 (by decide +kernel)

def m_73 : Nat := 0xffff0000ffff
def s_73 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_73 : Nat := 0x177f00003f7f
def ep_73 : Nat := 0x2800000000000000000000000068000000400000060800000c0800001220000030200000144000000040
def bds_73 : List (Nat × List Nat × Nat × Nat) := [(m_28, s_28, 7, g_28)]
def cur_73 : Nat → List (Nat × Nat) := fun _ => []
def nh_73 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_73 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_73 : dagCheckRootsV5 m_73 g_73 ep_73 1 1 0 bds_73 (dagTraceF m_73 s_73 7 f_73) (cur_73 0) (nh_73 0) s_73 7 = true := by decide +kernel
theorem nc_73 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_73 g_73 ep_73 1 1 bds_73 0 (dagTraceF m_73 s_73 7 f_73) cur_73 nh_73 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_73 : LowerBin m_73 s_73 g_73 8 :=
  lowerDagV5 (kn_cons lb_28 (kn_nil)) rc_73 nc_73 (by decide +kernel)

def m_74 : Nat := 0x6666666666666666
def s_74 : List Nat := [0x2222222222222222, 0x606060606060606, 0x66006600660066, 0x666600006666, 0x66666666]
def g_74 : Nat := 0x6066604462666
def ep_74 : Nat := 0x440200000000660000022200006006000420040000606000402040000000000000000000000000000000000
def bds_74 : List (Nat × List Nat × Nat × Nat) := [(m_39, s_39, 6, g_39), (m_41, s_41, 5, g_41), (m_42, s_42, 5, g_42), (m_29, s_29, 5, g_29), (m_9, s_9, 4, g_9), (m_61, s_61, 5, g_61)]
def cur_74 : Nat → List (Nat × Nat) := unpackCursorV5 0x987c7871545050494841240b01 0x2d4d55161354494d24993564588d492634d0d346d297464918946a8ddd37149c01f 8 255 3 7 10 1023 14 16383
def nh_74 : Nat → Nat := unpackHintV5 0x2c8188d2521c18850217e96598615016518293c0a4c8289e94012680004 0xffffffbff7ff7ffbffffffaffff38eabfffd4ef3c00ffffff6fbff7ff7ffbffffff5ffffa3ffff34d5f7cf003ffffffdfec74fffebfffffeffdffdffeffccffffe5ffff6657fcf002fcfdfcfefef7fbceafdf7f7cd653c0f0000000f 18 262143 8 255
def f_74 : Nat → Nat × Nat := unpackForestF 0xb534637893623514dcb4a2d18a4634d0946149c01f 4 10
def ch_74 : Nat → Bool := dagCheckNodeV5 m_74 g_74 ep_74 2 3 bds_74 12 (dagTraceF m_74 s_74 7 f_74) cur_74 nh_74
set_option maxHeartbeats 0 in
theorem rc_74 : dagCheckRootsV5 m_74 g_74 ep_74 2 3 12 bds_74 (dagTraceF m_74 s_74 7 f_74) (cur_74 0) (nh_74 0) s_74 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_74 : treeBlockF 0 12 ch_74 = true := by decide +kernel
theorem nc_74 : ∀ i, 0 ≤ i → i < 12 → ch_74 i = true := fun _ h1 h2 => treeBlockF_at nb_74 h1 h2
theorem lb_74 : LowerBin m_74 s_74 g_74 8 :=
  lowerDagV5 (kn_cons lb_39 (kn_cons lb_41 (kn_cons lb_42 (kn_cons lb_29 (kn_cons lb_9 (kn_cons lb_61 (kn_nil))))))) rc_74 nc_74 (by decide +kernel)

def m_75 : Nat := 0xffffffff00000000
def s_75 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_75 : Nat := 0x1117177f00000000
def ep_75 : Nat := 0x668000000000006006800000000000606080000000011121220000000001114144000000000
def bds_75 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 7, g_32), (m_28, s_28, 7, g_28), (m_33, s_33, 5, g_33), (m_35, s_35, 7, g_35), (m_40, s_40, 7, g_40), (m_30, s_30, 5, g_30), (m_1, s_1, 4, g_1), (m_37, s_37, 5, g_37), (m_34, s_34, 7, g_34), (m_53, s_53, 5, g_53), (m_31, s_31, 5, g_31), (m_4, s_4, 4, g_4), (m_9, s_9, 4, g_9), (m_6, s_6, 4, g_6), (m_5, s_5, 4, g_5), (m_13, s_13, 4, g_13), (m_7, s_7, 4, g_7), (m_14, s_14, 4, g_14), (m_11, s_11, 4, g_11), (m_10, s_10, 4, g_10), (m_3, s_3, 4, g_3), (m_2, s_2, 4, g_2), (m_0, s_0, 4, g_0), (m_8, s_8, 4, g_8)]
def cc_75_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xc86f3bc2f0bc2c3ac692a4290a064490240902408c62188211751d0741c1701b16c1b060cbd06801 0x3448065180f96c1e0d8389706cae0d05c1968e3b15c611806044158da1d194522a858460f0d81815031aa0856a0eacc1b1982c3304457060d80b15c102a01844288ae4cd6c91a590232172642c1684c2b89056110941411c24230383e020652ad1e4525c5a3b86296fe4ed9491ae84b530766208c04098001f 10 1023 4 15 11 2047 19 524287
def cc_75_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xc9320c8320c8311c0700bc6b4ac2b0a85dd705c06c5b06c192641722b4a024490204711843304801 0x811b5cc657f155b046741b1b8546ed51dd6a73599c4666c1999c579515e425b8c92e12312e48a085a7c15de85678129a84768119902e0408979605e98111223c088786c540f18262428c971623a4c9686e581b5586c1c1954862281546845100f828324ed592b6638480d020469b0c930441b10c57304c0d920 10 1023 4 15 11 2047 18 262143
def cc_75_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc29aa4290a0680a02809c6709c1da705c06c5b06c192641722b4a02449020471184330481004001 0x3234bc692f1233b252ac04ac011af83e820caf02e2c08ab866ae48ee35bb696ed233b256ac05aac15aa83e780caa02e2208a8960a2d8221213e049d06c980b29362868c681623a48a786e9c1b6686c7219658627e155c045660b828229295a3a6638480d8208a9b0c930881b21c57304c1b844 10 1023 4 15 11 2047 18 262143
def cc_75_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xb86e0b46d0b42b2ac292735c0701b15d1705c1705c1615455050504401003c42d080200441000400 0x3ea60fad82282146047716cf0063f362f898bd96ef45b7c96cda597b962e65576145860c50821ce0642811d6513a46ddb1979c55d451b716cd65535b54df5ab6d66d919b5166cf15fb457ea56b9157e255b814ad251f4146c416ed04b840c50021cc0641011c215b0923 10 1023 4 15 11 2047 18 262143
def cc_75_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x9410a21041180300200388700b3158ab0560869082104028010016a2c0544a81501742c0580b01422805000a 0xa0d85f2329f4f9dd329a184c0219e064a41151500bd309bd866a61504c8b922990f92c32980b8a4228f9668a53a19460d599d54e71517648d60599714e58514a08ca0132704e434a8f92a52468552e4d2975485704b920a504212604c941390d6a3e5a8e95a295b8d4a5c1216416e30293c08490134908e2b4b8492a0d4a8951a213e754c96c4b480ce1c19160451c2385d6e125a8356a0956814f9c1326316d1833800644411 11 2047 4 15 10 1023 18 262143
def cc_75_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x909018100100 0x281617e4c69129774866c61520c68c294b085f640 8 255 4 15 10 1023 18 262143
def cur_75 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_75_5 (Nat.sub p 160)) (cc_75_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_75_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_75_2 (Nat.sub p 64)) (cc_75_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_75_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def hc_75_0 : Nat → Nat := unpackHintV5 0xe8403f2b8b795c01cae00e570071f863671478e729b568ed950b2bc0753e1008a5a5bc4475d7058eb8007440c3850e9b944ad563a5ab8023052d0b0686b6d135005983924a8cc847e641865c843bfc0010e00000 0xf063e0fc0b2e03a05a07060eaaaaaaa940000e2c587062c5835a55028000e0c18787c0e1f000000040785c0e172a0b000038b161c18b160e162c58b1e2cb8080b160007061c1870e1c3831e3c180000022aaaa80070e2c183162c593060c5c2c58b1e2e016a2c0e0c183064c1833e2c162c383161c1830e3c78f1e1c780003d0151680070e1c387162c3870e0c5831e2c78b100e2c39b260c19b260c1870e0c39b063c79b878f37070e1c38f0e0d58f0600000000000a000a8aaaaa000c183061c78f0e0c18306000000aa8aaa001c38b162cd870e0c18b170b162c78b805a8b039b061c1831e8c500e1cf8b058b0e0c187075eb81c183066c39306070e0c5831e3c78f063c0001e80a8b40038b0e0c183060c58b060c18f163c588070e4cd93261c383060c193060c5830e9c7871e3c9c3c7938183060c783000000000005550005455500070f1f0f83e8b0e0c1d50faa87d07a87d40ea1f55000000000002aaa8aa802800503063e0fa2e2707360c99b066c1d5550000002aaaaa0007264c3d5550000002aaaaa0007060eaaa8000001555550020f07a8dd50381d44eaa8258383061c787063c18000000aaaaaa8800070e2c387060c583063c5971e5c582007060c3970e0cb8300e00c2e2875069750 21 2097151 9 511
def hc_75_1 : Nat → Nat := unpackHintV5 0xd5f53616ccadbd7d69a22b4d00598076c284d5de1bab51d507a9a3766513e3e77e90b4c3999b456ca41b62715afe8a97b022b1c5e58703aae8a9096707e0352c3969470d45865a2be02158038958b400a5200002 0x140c18795a1188c07caaacaa2c3c1c3d5503a54613546c983066c983061c3830e6c1870eaaa1e9a070f80d9b0367c038071580c1e4aaaaaaaaaaa820c183075534230380c0644aaaaaa8307a8dd40eaa3e014b21cd8381c3d17a2d83c2da0e0e81d7ae87060c19b0e4c1a1c383a95a1188c07caaacaa2c3d038183aaa54613070e4cd93261c383060c1930750787c0c1aaa83a684e070264c099f00600c1e4aaaaaaaaaaa820c7c7c464c99f4587060c3c3e070f80f8007c00020e1cf9b3e6c387060cf933e4c1830005095555500040014383061e1f0387c01c0183cb92aaaaa5d55410e1e83830740d5460129706293266c9a0caf5d01882c99b260b060c383062013061c183060c1831f0f8000441830e0c1872e0c187061c183060c7a31e8c000f8aaa2d40098b164c98b161c3870e1cd87060c183064c1972e202b164c58327170e1eb8f0e8c7871e0d1830e1c801955000e1c387063d38387c3c78f2f43e1e2c5a31f0e170809c59b161cdc5d18f060eb8f061d187063c18320065540038f561c183060e1f0f1e3cbd0f878b168c7bf85c208f063e9168b2e87060c3c3e070f83c7e071f8055555559547aaa1c58f0e0c58f070f163c78f1e5d5163d5500 21 2097151 9 511
def hc_75_2 : Nat → Nat := unpackHintV5 0x9594aa31d24830cb5e732871543d8f7af5a7cb16482b4f1d05208df3ed4a8d6d243458accd6203188e8c18252fb058b44542cd81caec252244b883a2b18743c5c62b0ea43c3a4020e800835a2308329c090be01308800026 0xe0c3830e1c38706bc78300e00000028003067c99f260c19f878f1e3cfc02d15555400400143830e0c3870e1c18f060703803078ad7543aaaaa82a83062d583063c5971e5c5b70016a1c387ae3c383061c783060c1870e3b158756ba0d543870e1d61e3e87c3c58b563e1c2e5e03d0615c0e0c0060c183663c7ab038756ba0d543870e1d51972e8c00da7369c58b569e59b162d060f003ab561c183060c01e3d5ae835147a2d5438f0eb0f1f0043e1e2c5b31f3e1720c183060c3870e1c183060c0e070180c1e0f0e1c3d7061c5870ea8b162c58b016a83060eb83062c183162c58b1602c387060c183060c18306830e1c387060c1830381c06030783d55555504387160c18b170b162c78b859f00162d4589e3707362d0e2c3aaa83060c1a0c1831e3cdc3c79b83870e1c183060c0d9b0367c0e070180c1e2aaaaaaaaaaa083060c1d5550360f50fa81aaad4230380c064410f0a5555555555541060c1830ebc787060c18300006000070e7cd9f361c382801f878f1e3cfc02d5515540040014183060c38f0e0c1830601c0603078aaab5d506aa821c38b4e1c3aa3c5971e5c5b70016a0c18f5899b26836bd749831e97164cd932703061c183545a4c1c0e0703947a1f0f975541830e0c18701830e0c383060c1971e3e1f42f17975551697552744c9d070e1c387361c183060c19306a09755c4e064cf815c0ebc0006bc1c3c7c074baa0aa1c3870e0d1a706a233e001b466d1d2f472cdd25d4f1b839b3e2f02b80c03af0e10f1f00d2ea82a8746ac383060c1a88cf8004d193474bd1c7274974061f916c01c1830000aaaa09555400055954aaaa200014000583830e0e6aa80e071180c89555555060f40ea275547c029643c0e064e070b68383 22 4194303 9 511
def hc_75_3 : Nat → Nat := unpackHintV5 0x8328ae08a208058e9fcc257e8059ef8547ba81dea0257114b9ac8be6a1089a382663b299689325432f94c82253200148e1d51089940c1b4e60e924ca63fa4c8f6c3e34ac84b5ee62414b46b528125c3c4402b06fd04000df 0x63c2266c980caf5c260cb85c993364c9c0c187060c01e13070381c0e01e0022d165c060c383061d060c3830e0c183065c79787d0001f0b804e8993a0e1c3870e6c383060c183260c02e8f4797143830e0e2aa80000020f40ea2755048743aad06cc00b0b5a03c0e064e071f28383a060c3c050001001e0e1eaa81d0123d1ea5e0facdaa364c183364c1830e1c187360c3870000f45038bc00000000000a6c5a9b16a1d43aad0697600060c183aa8a00000083d46ea0754129d0e8341b3002c2d680e6c1c0e1e03c47c1e3e5070740ebd70383060cd87260c0e1c1d4050001001e81c0c1d550123d1ea5e0facd8387266c9930e1c183060c983a83c5e060c0001d1400000000000a743a9316a4c5a8350697600063e0f8b598b262c383061e1f0387c000000a2d5516aa8b000070e2c58b361c383062c58b260c1802800002c1c1830f1781c5e000000b80070f41c183a06001750ea0d2e5d800566b070e0c1d71e0c3870e1c18f060c76275ae8706aaa83060c1c3c7d0f878b169c7bf85cbc07a1c3815c061c3870e0cc78f4e035ae8706aaa83060c1a32e5d180134e4d38b169d5c7262c5a1c1e0070e1c3834e9c1803d6ba1c7aa28f45aaa831e0e1e3e0087c3c58b663e9c2e438ae2703262d555060d060c187060c5830e1c3871e3c9c3c7938183060c0e070264c099f0180c1e2aaaaaaaaaaa087061c1d5076aa0eaab03a87d54070388c064410f0a5555555555541 22 4194303 9 511
def hc_75_4 : Nat → Nat := unpackHintV5 0xfcf863daec8ebed6baae26e9b087a321de80863872c8d6fd6b3413fc1e592e252aaf44aa97f299e4bda5e4d78c75920c92a79d4a9c23296724b57474156237d3352a43b490e932d2cd6bc8dd2c196d0449cdf0924a800124 0x3458203061c187060c1832e4c984c2600701800030018172e1349a28306030e1c387060c18300e000300003e00c18000306007e2e3cb8f3f01343a1d06834babc003ea7c5a9f160c5b1745a83169f10018f947a0c3e020c187061c183060c7931e131268b543a0d55506a8352e5c1260c1a0c3870e1c183060c0e070180c1e0f50eaa83555516a08b5060d55418355170b162c78b859f00162d4583060c187060c383060c183065cb93265c3870e1c183060c09801c0e030185c526a8743a0d069750060c1830e1c183060c1830e0ea0f078183a060e81d03a0381c09930267c06030b921d0ea4c5a93168341a5d900e0c3830e0781c5e00e0000010070e000c19f267c983060014121d0ebb41a5d8014f8b53e2c3830e0c3a1e070f80e071b80c1e4a1d5555564150e1d54183162c593060d556859f00162d60e0c3830e1c3d70e5e0e0e2e5e0e1cb83072b81c1c381c0e00c2e408c243a1d41a5d959ac803060c1c1eaf5540e83d03abd555550380e070180c88890e8741a0d99990460c18307555507a0754070380c064411f0a43a1d068366585ad208ea060c183060c183060c183060c387a060e83d03a070380d9b0367c0e070180c2e4a6c5a9b168743a0d0697640183060c3c5e060380001800041c39f367cd870e00c180000504bb43a0d069760053e2d4f8b060c1830f0f81a0e1b81c06030792aa835555904387162c59b0e1d418355555a167c0058b58183060c3c5cbc0c183ae0cbc0c38793c1c1832f030601c06030b90230943a0d06976566b201c383075cb830e1c387065c1830ae070600003060c1c3c7d23919b368d5bf8dc075ba8d1e8f000060c060c187060c9830e1c387263c9c4c7938183060c000000000010e875262d498b41a0d2e8007061c1d5072aa0e00103a89d54000000000008743acd06ccb0b5a000e0c3830e1c387063c78300000050ea2aaa800280003062c58b260c18b858b163c5c0000a2c3830e0c3870e1c1970605700380000003066d58306bcb972e5cd80743a1d41a5d00576a6c387ae5c383061cb83060c1870e1c0ae03000e1c3870878fa4723264d1a78713806b751a3d1e0c183061c3870e0c183061c387ae0c39f0e1c03e4cb9300183075c1833e0c19f2e5cd870e0c183060c18343a1d06834babd3e934fa6c18301870e1c383060c1800000070e4c183264e263c98f2701343a1d06834babc01498b5262c3930e0000c1830603060cb8f37171e6e0e1c387060c183000000000005362d4d8b43a1d06834ba000c1830755540c83d46ea060015000000000002cd0e8341b32c2d6800183060c38f1e1c183060c0000015541a8aa0001c38b162cd870ea0002e162c58f17000028b060c1830e5c383060c180005700180070e4d3870e02f265cb972600d43a0d06974015da93 22 4194303 9 511
def hc_75_5 : Nat → Nat := unpackHintV5 0x2820ecca1d5721221c641d130001d 0x30f803c1a2d5160c187061c183060cb93a264c9870e0c1932e3c383060c183060c9930985c126975060c183aa0f5503a0f503a81d40eaa0381c060322e5047c290e8741a0d8bb4b0b5a411833e45c1e00cbc03c 19 524287 9 511
def nh_75 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (hc_75_5 (Nat.sub p 160)) (hc_75_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_75_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_75_2 (Nat.sub p 64)) (hc_75_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_75_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_75 : Nat → Nat × Nat := unpackForestF 0x51929a30532c94e5928cf3619e27d3c06658a9cb151986c330986601f4c02e960a72c14405a3c924692253240a40525c635a8c4b51895a3094c6029014770ed2e1ca34393e870320252e01adc025a802b50055a009f4001901276eed89f5b03ba62772dcee5b5dcb63c018772c4cd15d98ad39c6d738aacc55d98ab3314a6aad4dc5b1aab3354666b6a8d459998a3b3146678aecc0640491af34b5e496bc8cd8491af0465e07cbc0b80425aa35b544b6a88cd50ad2a05a57246a8159501f2a02e0107696d8945b0259624b0dc961b52c362602c4b0c46515d252b1925b474cc6492d11362206c438ae648c4c82d1fc6d3f8aa6415cc82b1904a36ad4741b0dab31b466376a86c198c82399046338ae640b8041194a622f4c052588a4371486d290d8540f0a43101457276ac04d6c95b30134b224d8441b0862b812321e2d83c1b0622b8d25c1a2b83417065a38c230022640416852368a455020ae04158082505d6a0f0d8175982e33063540b0cc0411c0823044570207c0c1b00e2b8185403088040c804098001f 8 11
def ch_75 : Nat → Bool := dagCheckNodeV5 m_75 g_75 ep_75 5 31 bds_75 165 (dagTraceF m_75 s_75 9 f_75) cur_75 nh_75
set_option maxHeartbeats 0 in
theorem rc_75 : dagCheckRootsV5 m_75 g_75 ep_75 5 31 165 bds_75 (dagTraceF m_75 s_75 9 f_75) (cur_75 0) (nh_75 0) s_75 9 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_0 : treeBlockF 0 32 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_1 : treeBlockF 32 64 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_2 : treeBlockF 64 96 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_3 : treeBlockF 96 128 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_4 : treeBlockF 128 160 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_5 : treeBlockF 160 165 ch_75 = true := by decide +kernel
theorem nj_75_1 : ∀ i, 0 ≤ i → i < 64 → ch_75 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_75_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_75_1 h1 h2)
theorem nj_75_2 : ∀ i, 0 ≤ i → i < 96 → ch_75 i = true := block_join nj_75_1 (fun _ h1 h2 => treeBlockF_at nb_75_2 h1 h2)
theorem nj_75_3 : ∀ i, 0 ≤ i → i < 128 → ch_75 i = true := block_join nj_75_2 (fun _ h1 h2 => treeBlockF_at nb_75_3 h1 h2)
theorem nj_75_4 : ∀ i, 0 ≤ i → i < 160 → ch_75 i = true := block_join nj_75_3 (fun _ h1 h2 => treeBlockF_at nb_75_4 h1 h2)
theorem nj_75_5 : ∀ i, 0 ≤ i → i < 165 → ch_75 i = true := block_join nj_75_4 (fun _ h1 h2 => treeBlockF_at nb_75_5 h1 h2)
theorem nc_75 : ∀ i, 0 ≤ i → i < 165 → ch_75 i = true := nj_75_5
theorem lb_75 : LowerBin m_75 s_75 g_75 10 :=
  lowerDagV5 (kn_cons lb_32 (kn_cons lb_28 (kn_cons lb_33 (kn_cons lb_35 (kn_cons lb_40 (kn_cons lb_30 (kn_cons lb_1 (kn_cons lb_37 (kn_cons lb_34 (kn_cons lb_53 (kn_cons lb_31 (kn_cons lb_4 (kn_cons lb_9 (kn_cons lb_6 (kn_cons lb_5 (kn_cons lb_13 (kn_cons lb_7 (kn_cons lb_14 (kn_cons lb_11 (kn_cons lb_10 (kn_cons lb_3 (kn_cons lb_2 (kn_cons lb_0 (kn_cons lb_8 (kn_nil))))))))))))))))))))))))) rc_75 nc_75 (by decide +kernel)

def m_76 : Nat := 0xffffffff
def s_76 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_76 : Nat := 0x15573f7f
def ep_76 : Nat := 0x2a2800000000004200400000000004020c0800000000100230200000000015540040
def bds_76 : List (Nat × List Nat × Nat × Nat) := [(m_54, s_54, 6, g_54)]
def cur_76 : Nat → List (Nat × Nat) := fun _ => []
def nh_76 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_76 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_76 : dagCheckRootsV5 m_76 g_76 ep_76 1 1 0 bds_76 (dagTraceF m_76 s_76 6 f_76) (cur_76 0) (nh_76 0) s_76 6 = true := by decide +kernel
theorem nc_76 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_76 g_76 ep_76 1 1 bds_76 0 (dagTraceF m_76 s_76 6 f_76) cur_76 nh_76 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_76 : LowerBin m_76 s_76 g_76 7 :=
  lowerDagV5 (kn_cons lb_54 (kn_nil)) rc_76 nc_76 (by decide +kernel)

def m_77 : Nat := 0xffff0000ffff0000
def s_77 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_77 : Nat := 0x1117000015570000
def ep_77 : Nat := 0x440000000000000000000000006000000420000000600000402000011120000100200001114000015540000
def bds_77 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15), (m_30, s_30, 5, g_30), (m_58, s_58, 5, g_58), (m_47, s_47, 5, g_47), (m_7, s_7, 4, g_7), (m_54, s_54, 6, g_54), (m_1, s_1, 4, g_1), (m_20, s_20, 6, g_20), (m_19, s_19, 5, g_19), (m_64, s_64, 5, g_64)]
def cur_77 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0a2a092908280727070707070704640400f01 0x1298c5294262f4a4f19353e3464b4f93a9234a3ca46928aaf11468486e8ed8a1a93b1a46210821d001f 8 255 3 7 10 1023 15 32767
def nh_77 : Nat → Nat := unpackHintV5 0x5e202a697530095e7cae020f91078070e637425b112d28c66463241d8b0e8c73302c0d16000d00000 0x303e00c00075b005ab4003e3000180eae00b56c07c220018f600074e8007e200218ee00074edf2f83f83f8b558c750ea0d972a1ace75aa9ceab3ad0000000000871c100055550000000000871c0001555500180320221cb5822b58b469d9 17 131071 7 127
def f_77 : Nat → Nat × Nat := unpackForestF 0x229486437a5218eda9f05435a7c14ec9a9134a24a449288af11460a46110821d001f 5 10
def ch_77 : Nat → Bool := dagCheckNodeV5 m_77 g_77 ep_77 3 7 bds_77 18 (dagTraceF m_77 s_77 7 f_77) cur_77 nh_77
set_option maxHeartbeats 0 in
theorem rc_77 : dagCheckRootsV5 m_77 g_77 ep_77 3 7 18 bds_77 (dagTraceF m_77 s_77 7 f_77) (cur_77 0) (nh_77 0) s_77 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_77 : treeBlockF 0 18 ch_77 = true := by decide +kernel
theorem nc_77 : ∀ i, 0 ≤ i → i < 18 → ch_77 i = true := fun _ h1 h2 => treeBlockF_at nb_77 h1 h2
theorem lb_77 : LowerBin m_77 s_77 g_77 8 :=
  lowerDagV5 (kn_cons lb_15 (kn_cons lb_30 (kn_cons lb_58 (kn_cons lb_47 (kn_cons lb_7 (kn_cons lb_54 (kn_cons lb_1 (kn_cons lb_20 (kn_cons lb_19 (kn_cons lb_64 (kn_nil))))))))))) rc_77 nc_77 (by decide +kernel)

def g_78 : Nat := 0x1117177f15573f7f
def ep_78 : Nat := 0x44028000000066800002a2800060068004200400006060804020c0811121220100230201114144015540040
def bds_78 : List (Nat × List Nat × Nat × Nat) := [(m_75, s_75, 10, g_75), (m_72, s_72, 8, g_72), (m_16, s_16, 4, g_16), (m_73, s_73, 8, g_73), (m_43, s_43, 5, g_43), (m_68, s_68, 9, g_68), (m_67, s_67, 8, g_67), (m_15, s_15, 4, g_15), (m_69, s_69, 8, g_69), (m_57, s_57, 5, g_57), (m_62, s_62, 5, g_62), (m_71, s_71, 8, g_71), (m_54, s_54, 6, g_54), (m_56, s_56, 5, g_56), (m_70, s_70, 8, g_70), (m_77, s_77, 8, g_77), (m_12, s_12, 4, g_12), (m_74, s_74, 8, g_74), (m_31, s_31, 5, g_31), (m_17, s_17, 4, g_17), (m_28, s_28, 7, g_28), (m_36, s_36, 5, g_36), (m_48, s_48, 5, g_48), (m_58, s_58, 5, g_58), (m_40, s_40, 7, g_40), (m_39, s_39, 6, g_39), (m_30, s_30, 5, g_30), (m_47, s_47, 5, g_47), (m_38, s_38, 5, g_38), (m_5, s_5, 4, g_5), (m_23, s_23, 5, g_23), (m_65, s_65, 5, g_65), (m_29, s_29, 5, g_29), (m_42, s_42, 5, g_42), (m_46, s_46, 5, g_46), (m_26, s_26, 5, g_26), (m_63, s_63, 6, g_63), (m_6, s_6, 4, g_6)]
def cc_78_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x8a245022811408a045022811407c3be01f00f80761bb01d80ec07603b01d80e817403a01d00e807403a01d00e41586a12c0c0001 0xb97607cb6026550090280ec6d0722e8371541a6ba0cb55061a582ed1c15ad40a46604da2818d58040ac08c5f0422b81ed7c0e6b606b5702da9814d2c0968e0405b01c2980c12c05076018330bab785959c2a8de1446b09a3384518c208b60f457058b3024558020296645faee2bd72d7eb66b759b57ab1a9d52d2ea668f5025fa352dd0895e7c4a738a4b98d23ca68fe464771823785919bfa57ddc2b6c91575c4a9a9652d2728e8213f3b09d99a4dcaa2664512f1b49586049c012460003f 13 8191 6 63 11 2047 21 2097151
def cc_78_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8720c0ac4a1280a028094e5094250942145e97050d404110034cd02c8b020c80188600cc3000c00 0x1fa6c7cdd1e8248a9be1a6b8099de2638f9ea347a70de9db607316dc4576e959ad6e691ad9c676499b5d6fb959ecc6fad1ae8c679b18e445b7515db36a62d68e1745e59088145a5f0d964285508014345d159641e05149441c051397c3259068144a5b0601449199194416050c176425105014 10 1023 4 15 11 2047 18 262143
def cc_78_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x8cbf1b8d86c32990c8562a150a8499d0e06934168b051281406830180a442190c0600600 0xbed53224fc492f0a47bc90f547fd11cf2b72badc2dd65b4da23566b1199a36aaed22645aa896e9a57ab5f65c5aa4dc19b5aa0d827c669cd226370975da547672dea4b48889e1fa6488df2157c7c982087c 9 511 3 7 11 2047 18 262143
def cc_78_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x9826090a4088a2080a007c5e1781e0781c25d570584ca300a2244901c8701c052104310841104001 0x1fa333e944762ecf6511d4bb3c96c730f8e41f1cd1db9237778daecd2dd5a3ba06e710d8df5aa22b7c3567838df031adfe33be4637a8b6f115dc0b3371566c6d06ad619dc03338069690cf1f59a38b1a5860488c6d717d203024c 10 1023 4 15 11 2047 19 524287
def cc_78_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x881e4781d1741d06c9b06499064190551505415048d20481021a8601445010440100220801104001 0x252b34fc668c4cd3c912713e4d46699489209da5d224ae7a948f51e9da4d3648c6d906971ed1e36b54636ba8adf4559e8237cec6b9b8cf3118e5a2dc94578e4cd1695a24b24397c85acb0859208a24017c 10 1023 4 15 11 2047 19 524287
def cc_78_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x90a4088a207cdf07c1f07c1f07c1e1781e0781595415054123228801c470148501044004c1000400 0x305b35f934b12ed7a4d2c0bb5d96cac2a969156e636dc45db78ab6c9bed531d9a5db24ab6292ec123d756aad8cd589172eb7e4d67c66df88daf09b3df363bc6b774d5ebcb355956a94c94aa329d2252b71a68e7489fa8d3e50a64 10 1023 4 15 11 2047 19 524287
def cc_78_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x84e10841f27c1f0749d0741b26c1a168191641905c8da340b22c0831c47010c400c4300481004001 0xe0addbed9b5933eed65dc8d1b497364126bc70d68b5a8973492e6847acf8c1d55bf8eb3f0c6ade8b5b69bf6135eaa67d34c7a296f392bdc174cc2c9945f2dcb256954b42c991596ccba63964c5269865f2c8b260257 10 1023 4 15 11 2047 19 524287
def cc_78_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x88202801f17c1e1781d1741b26c1926419064163581512e8b0248812008018860144230800200000 0x7fd657f1647e1347d17c7c134789767b134781767a16c7946d78a4b782477756a8156f805677eb6f7db6b7cb677bb637ab5b79b57779667695675c687045872a7d7423f73a3772c8074c72734707227f7135668257 10 1023 4 15 11 2047 20 1048575
def cc_78_8 : Nat → List (Nat × Nat) := unpackCursorV5 0x8c212841e3781e0709b16c1b06c1a155550541324c130449104050040100400c40a8200441000400 0x8f46d842478e56a8ba6b882678d5658cb648a0248a3568bc66833668b2668aa448982488b7c883568726686a4485a4484e7a8437683b6c8327a92d6f8fd678eb668db568c26f8926b87a67862638525b82a57819648097c 10 1023 4 15 11 2047 20 1048575
def cc_78_9 : Nat → List (Nat × Nat) := unpackCursorV5 0x9826090a408c6308c2128421078de0745d0741a3681a0681735c1705487e1c061144501404110004 0x9f26c9e8249dd709ca6c9c2549b67a9ab6c9517a99a6c98e7a984609497a9726c96a54960249523f94a37a556aa436fa336ba2367a0b639fa6f9e26b9d2679ba639a23f9923b97a3795a339416a933649127d9138c9237e91b7c90a7f90172 10 1023 4 15 11 2047 20 1048575
def cc_78_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xac283a025394223881f37c1f07c1f0785a4681a0681a05908e1886014450104400c4300c01204001 0xab276a8176af144aaa76a7976ae134aa276a7176ad15ca9276a6976ac134a9a7cab23faaa3baa237a9233a823fa7a3ba7237a6a33b7c6fb6c6bb5467b4463b336fb236bb0b67afb63aeb4fadb4bacb47abb43a8a66a61669b23f98a37a4d68a3b6ca2d70a1b6ca1354a0568 10 1023 4 15 11 2047 20 1048575
def cc_78_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x88220881c6701c0701c0701c0701c0520aa2809124081200801886014450104400c4300c01204001 0xc0b45c0245bfa3fbf23bbea37be233bd34bbcb47bc24bbba47bb23fbaa3bba237b9a33c845bc7457c635bc5357c434fc334bc2347c1343bd956b9014b8164b7144b657cb597cb4944b3964b2934b1d7cb117cb0134 10 1023 4 15 11 2047 20 1048575
def cc_78_12 : Nat → List (Nat × Nat) := unpackCursorV5 0xdc1b83706e0d83b0350ea0d03a0330ccd5a0b0141280446880f11e0306600919201863003186000600000000 0xcda46cc946cbb4aca946d2347d1a4bd1247d0a3bd0237cf94bcf147ce93bce137cd12fcc12bcb127ca123edc6ded457ecb5bec357eab4be5347e3a5be3257e1a4be0a47dda3fdba3bd6a37d2a33a894ac986cc8944bd014c796cc0954bc814c6934bc014c596cc0154bb814bf966c4944bb014bf166c3934ba814be966c295cba014be166c1934b9814 11 2047 5 31 11 2047 20 1048575
def cc_78_13 : Nat → List (Nat × Nat) := unpackCursorV5 0x98cc252fe7c3e1e2cd6432174b85c2e1629b48998b2512812490481d01c0000000000000 0xdfb8ccd87ce057ddf567deb7cde356ab15acd07ccc87cdd57ddca7cdc256aa95acc07cdac80d9c70d8e78d9d67d935bd8357cb87cdb57dda567d7c70d745aaa15acb07cd4024a994aca87cd446dd3960d657dd5a7cd5264d4a56a915aca07cd3024 9 511 3 7 11 2047 20 1048575
def cc_78_14 : Nat → List (Nat × Nat) := unpackCursorV5 0xd834297df670db1685a068173585515054048920445103c8b4248902046214450140230800200000 0xefa3fef237fe567fdc6bfd467fc45bfb457fab6bfa367f935bf8357f5b4ff434bf1b47f034394256ee956ebb49e2a49e023fdd23bdb237d6233df23fda237d206cd187cd106cebd7ceb37cd087ce9a58e7a44e9b5ce7240e885ce7a4ce7354e6824ea24fe924be8247e6243e5d70d007ce4960cf87ce4024cf06ce2d7ce227cce87ce1570ce07c 10 1023 4 15 11 2047 20 1048575
def cc_78_15 : Nat → List (Nat × Nat) := unpackCursorV5 0x7d16950940501404c530485204812044510405003c4f03c0a5280a0208801c4701c0250802000800 0x407596024e900a647fc1242b1561369708b4783d25c1a91e0a47f03a3b8111bbfc8cdee69ef33477e4a23ee5b1f3268f896c7be463dd9dded8cc9526677cb33d8511ea6ccf493479ec03cd9dde5ad494a66778b33c8571e26ccf0934 10 1023 4 15 11 2047 21 2097151
def cc_78_16 : Nat → List (Nat × Nat) := unpackCursorV5 0x9425094250906408c5b842cc4300b12c0a1280912408120080188601804210040088110401004001 0x10d814864b343d17e1d8af0e15b868a9c3052dff0bed30574b023c5d5be26acf1126687d2b3fc5bde02d6d2967608b1aae56d2b2af0b8248311fc128ee0646f01a33851b24255a2104c907568832b2c16d9209acb0426481ab2c0b1a20004900455 10 1023 4 15 11 2047 21 2097151
def cc_78_17 : Nat → List (Nat × Nat) := unpackCursorV5 0xdc361d46f6bc2e1b82e0b0a6698251942236298054d50505404c5304c11229ca0280a01545014005 0x47c4f23d488f396b6d4b3c844fe402771f9378f099c7520238b011b95c90e394771c2392ff1b173798b5b6859e346ad19366794b5b5c59e44adf1ad678ce3546316a042def196b6b4b3b0858d592b6979578913a45e9921e049149718acb1c52e322826916b7e8b13f4549f2234c91025489cb9c3a092258db1245d88e2ac04575aa2ab10d6a882333c45ada92ce96945 10 1023 4 15 11 2047 21 2097151
def cc_78_18 : Nat → List (Nat × Nat) := unpackCursorV5 0xd0740cc730cc312a9ea0a469098dca701b1685a0681a06095354141501131e870184420c42104401 0x12d171975c64b72325a7013037e97dbe4bc9ca5c2ff2c9737b8b5b7c59e578db2ad6a7b4b5b7859e61adf2c567959b34a8d5a0a2def596b6ecb3b1058d5d2b69a1579493249c5c64e719269349413f49e9f24c2e72546d922b53d45adb82cf28d6f92eb3c9299a474ad0396f7a0b5b6e59d862c6ad95b4c8abc8b1a23a2fb1c171904a447c4d2414991e930 10 1023 4 15 11 2047 21 2097151
def cc_78_19 : Nat → List (Nat × Nat) := unpackCursorV5 0xf4394c2700bc6f0b86e0b46d0b06c0b01ee6cdb0685a068182601715c1705c1434c45e1404108802 0x13f3454e0a2a1c4fcc12674145b9fe2bcfa9595f2b69b957430a79ee52cd328e5f1439ed324f2912774f93aa449ea37cf11ae768cf3a4639cdb34e499a0f2def916b70cb3b1858d0a29e7a94b344a397850e6d6d3343614249fcdf5a26dcf13636c9aab84d19e2676d9333544189fce15aa6e6df35b6b9a5b3ccad8e644d50696f7c0b5b8259d8a2c68293f3cc9d99c4dcba26731364974becb65c5ef2b6df957 10 1023 4 15 11 2047 21 2097151
def cc_78_20 : Nat → List (Nat × Nat) := unpackCursorV5 0xe43c07806c2d81b0331e41c8190320640c8190320640998b4150aa0540a8150281500984478800c218030003 0x2950494a024a71225260929acf14ca6ca481222c4fe968af4ab5ba51abd26d2e9268f4894ba409dd1e4cdc80ae9e84744c1f9b20de9facf4f46ba7633d3716e988af32356a5d2b3ea5adc72ceb215b4f0aba2453cfb2966c147310a1d1c091632934437ca1ab85191b68b8af4535ba25abd0ed2e8568f39a4a7d0adb8c55d612969d14743c9f9f24ecd526e61133a0d225039e2804d93f254 11 2047 5 31 11 2047 21 2097151
def cc_78_21 : Nat → List (Nat × Nat) := unpackCursorV5 0x9604a0a34eeb87313525a80d02597ab895c090f48024011c28e04701ea8d1266132092388083c210706103001610b00504052001 0x25a8bd5f134afe38d7adc65969f2634b8d9a3c4ed0d2049d65b6fb29b1d70d6eb46af63a6fb1131d3e96e8b4af2c23f92d1dc6a8de264676096faf0b1bf856dda2ae8f93f4009d9c64dcc92665112f218958b849c2c2464292b16c93d751567a497372475bca5a9051ca025e4192b1649385448c9f25e2c127ae2b3d4f15ab76ad4f26ba2933cf096e6b4aefd96b764b3ada56d462ae4e92f204958ac49c28246b614915493d6b1b6b48af55b4aa752dd1295e7649734a477e8adbb055d6a296a214726c978fe4ac5124e13123ac41256497eb04a733245abcafd5c54d4228a4d12f1f89589e49c2424756b569d12dcca95d682b6a0957260978f84ac4d24e1112312c9389449eab8cd55366a8d37d369ae874cf4126384cb7bf05add52cec8163258978f44ac4824e10123a6934d029849525e239272509788c49ea8ad553b6aa8537d309ae854cf3fa63844b7bec5adca2cec7163248978f04ac3a24e0f1234689f9fe4ecdd26e64133a91b25455a2a58ab51b4ba85a3acc52d3f28e8c13f3f49d9b64dcc62674b024 13 8191 5 31 11 2047 21 2097151
def cc_78_22 : Nat → List (Nat × Nat) := unpackCursorV5 0x5b1333d0f0384952408114c501401404001 0x26147f28a3b9111bc5c8cd2527e8113b3a89b9964cca825e4412b1ac9385c48ec84fb6197d1a893d8a9c6bf2e25312f1a093d939d2c86fb16a32b08bea424fce426f63244b1638cbcd3abd2e361b7db093ecb88fe3946f60144 10 1023 4 15 11 2047 21 2097151
def cur_78 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_78_22 (Nat.sub p 704)) (cc_78_21 (Nat.sub p 672)) (Nat.blt p 704)) (cc_78_20 (Nat.sub p 640)) (Nat.blt p 672)) (Bool.rec (Bool.rec (cc_78_19 (Nat.sub p 608)) (cc_78_18 (Nat.sub p 576)) (Nat.blt p 608)) (cc_78_17 (Nat.sub p 544)) (Nat.blt p 576)) (Nat.blt p 640)) (Bool.rec (Bool.rec (Bool.rec (cc_78_16 (Nat.sub p 512)) (cc_78_15 (Nat.sub p 480)) (Nat.blt p 512)) (cc_78_14 (Nat.sub p 448)) (Nat.blt p 480)) (Bool.rec (Bool.rec (cc_78_13 (Nat.sub p 416)) (cc_78_12 (Nat.sub p 384)) (Nat.blt p 416)) (cc_78_11 (Nat.sub p 352)) (Nat.blt p 384)) (Nat.blt p 448)) (Nat.blt p 544)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_78_10 (Nat.sub p 320)) (cc_78_9 (Nat.sub p 288)) (Nat.blt p 320)) (cc_78_8 (Nat.sub p 256)) (Nat.blt p 288)) (Bool.rec (Bool.rec (cc_78_7 (Nat.sub p 224)) (cc_78_6 (Nat.sub p 192)) (Nat.blt p 224)) (cc_78_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 256)) (Bool.rec (Bool.rec (Bool.rec (cc_78_4 (Nat.sub p 128)) (cc_78_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_78_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_78_1 (Nat.sub p 32)) (cc_78_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)) (Nat.blt p 352)
def hc_78_0 : Nat → Nat := unpackHintV5 0xa919daa2b9989dd9389791929448d29031068c40fc8850fc7f72387b80fc75818071510c6ac1a46359da5b89f456a13a4ef9ea4a193847d0924089d23bc93036b9442cc27e22aa861b61d216c12814908c0dd9ae09791801a1f6000068000000 0xa81ea23aaaa84eaaaaaa8f665a5a666603130313a0303aaa0727aaaaa55038f87eaaaaa17a8bea17a82eaaaa83eaa2faa9500000000000000000202a81c1c2c2c2e07070781c1c1e0784e84c3e84c3ea999696999980c1c0c1c0c0c1c1c0c0c1c1e070380e81e5000000000000002a0ba07a07070781e13a13a13aa6669a66660340c1c0c1c1c0c1c1e070380e81e50000000000002a81c1c1c1c2c1c1c2c1c1e81e07a3e81e81e0781ea907a60785d9999980c1c1c0c1c1c0d030781c0e03a07940000000000008deaaaaaaaaaaa999a6999980d0307a07aaaaaa50000000000002aaa070faaaaaaaaa81e8faaa6a6a17666666aa81c0d0307aaaa94000000000000aaaa81e0faa81eaa8faa81e07a83e0fa81ea0faa66a660340d131303a070000aa81e07a84e37a81ea13aaaa81e0faa81eaaaa8f66a660340d131303a07000007171713070b073b0b0b1307070b372f070f072f370f230707230b0b503035170341c5d171745d0b45d170303503030740c1c9c0c1c9c0c1c0c1c0c1c0c1c0d400000000000000aaa81eaaaaaaaaaaaa66665a5a6603070307aaa81e03aaa9400000000000000a81c1e81e0785c1c1e81e07a3e81e81e0781ea907a607a3d9999980c1c1c0c1c1c0c1c0c1e40e03a0794000000000000a07aaaaaaa83e84eaaaaaaa3d99a6999980c4c0c4eaaa07279aaa94000000000000132384cee230b82c2e85c2e1387e2f83e2f83e0ba999603580d85d82d980c4c0c4e0350303982c9c0e0b03a139400000000000000aa07a3c1c1e81c1c1e0784e84c3e84c3ea999696999980c1c0c1c0c0c1c1c0c0c1c1e070380e81e504c1c1c4c4c8c4c4c4c4c4c8e0b0b89e8ae0102a07070b0707a81e8fa0707a070f81e07aa41d6960785d9999980c0c1c1c0c0c1c1c0c1c0c1e070380e81e501c9c1c1c1c1c1cfc1c1c1c1e0b0b89e96e01020faaaaaaa07a3eaaaaa665a5a666603070307aa0727a0303aaaaa9423070723a8ae27aaaaa80400781e81e8fa0707a0f84eaa81c1c1c4e81c3c1d99999969680c1c0c1e070380e81c0c0c1c1c0c0c1c1e501c1c1c1e131383e83c1c1c1cfc1c9c1c1e010281eaaaaaaaaa81e8faaa65a5a85d99999a03aa81c0c1c0c1eaaaa5227aa8fc1c1c1c1eaaaa0102a84e0f81eaaa6650307030780c9cac9cae271381ea070781e8faaaa83c3c3e81c1c1d99999969680c1c0c1e070380e81c0c0c1c1c0c0c1c1e508c1c1c8e2b2783e83c3c3c3cac3c9c3c3e0102aa83eaaa3eaaa07a83eaa999999969680c4c0c4eaaaa03aa81e509c4c4daeaaaa0faa83e0102a07a88eaaaa13aaaaaaa3d99696999980c4c0c4e80c0eaa81c9eaaaa509c4c4dae27aa8feaaaa01001c1c1c1c1c1c1c1c2c4c4c2d0741d1342d1745c0c1c0c1c0c1c0c1c0c1c0c1c0d40707278f070707070b131313130b2727272703010001c1c1c1e070707130781c3c1e0781c1c1e00007070000723071307070b230707230b6b6b0b41d1745d0b45d1703070307030703070307030703508c8c1c1c1c1c9e3c2c9c9c2c9c9c9c9c0c005002323230b88c8c8d6c2e230f2388e230f1780001c1c8c9c00001c1c1c2e0ba138aea99999980c4c0c4e0b0380e84e509c4c4c4c4c9e82e3c2c9e89ea89e001400ac8c4c1c4c1cac8c2c2c9cfc3ea8fc3e80004c1c002aaaaaaa66666603270327aaaa9427272727aaaa278faa8004088ea07aaaaaaa80020700083e2307072396c3eaaa66a0307030780ea89ea2b96e83e0faa6666660327032789c0e03a0f942727272789c9e0f0faa278f80400f230f070f070f0fa0f0f0fa0f0f0fa0000f07000a82c2c2c2d1745d1742d1745c0c9c0c9c0c9c0c2c0c9c0c9c0d427270b270b27270301002c2c2c2d1745d1742d1745c0c9c0c9c0c9c0c2c0c9c0c9c0c0d540e3c5c8c5c5c5c5c5c2c2c5c5c5c2c2c5c3c5c5c5cbc5c3c0c0c0d5000000000000005c00b0b0b0b0b0b0b0b0000000000 24 16777215 10 1023
def hc_78_1 : Nat → Nat := unpackHintV5 0xc10000c10000c03034bad158b1d240ac196ea5e18e9ea9ce9701ea8ff1c489e1848610f47e49f27681f27179426b3990602ac45a29804e52f64a210c4311c43cc1943152dc2d390625e1d624c84620c90019e9b80f5aa40b19100431ba00010c 0x1f83c3e9073380b82e83e0fa25555551f07071f50b0b555a5555550303030380c0e03a03545aa030303030000000000000088cbe2f2f230b82e83c2e0f8bc3e0b0b82e0f82c2e3d5547d5592f554bd542d59592f543d0f5555555555540c0c0c0c0c0e0380c0c0e030380e80d6555038f00000000000000000007070b0b8f0f0b1307070f0b0f0b0b555582c2e0f81e83c1c3c3c3c3e07a1383c1c1d540c0c0c0c0c0e0380c00004c1c4c1c1c4cbc8c3c2c1c1c2c2c2c3c2c2e3d5554bc4cde07a1384c1c1e0b0b83e07a0f070f5503030303030380e0300005550b9070707070b070707130707131384c3c4e130f0b0b0b0b5555555555030303030380c0c0c0c0c0c0c0c0c0c0c0c0c0d44000000000000004c1c1c2c8c1c1c8c2c2d555555550b0b073b13070b370f072f372f070f55550303030303030303030303030303510303030303030303000000000000000b0b0b1f13131f1f13131f55555551f1f130713071f8f544c1d551f1f1f1f5503030303030303030303030303035103030303000000000000130b13a3e0f0b0ba82c2c2c2c3c7e0f0f5551307071350fa0f070f070f1f1f0f1f4b070f0755030303030303a0303000083e87ea82c4eaa13a3e95561f4baaa87c7c4c1c1c4d6a9540e80e03aa00000707075555070781c1c2e3d070707070781c1c1e070f070707070b0b0b0b555555555503030380c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d44000000000000002c2c2c2c2c7c7c2c2c2c2d55555547c8c7cec7c7c8d54b0f1f2f4b2f1f0f55550303030303030303030303030303510303030303030303000000000000000b0b0b0b555235550b54bd50f555555540c0c0c0c0c0c0c0c0c0c0c0d40d5540e3c00000000000002a81c1c2c2c81c1c1e0b0ba0707a81e13a130fa130faa665a5a666603070307030350303076070380e81e5000000000000002a81e8f0707a07070781e13a130fa130faa665a5a666603070307030307070303070781c0e03a0780d540e3c1c4c4c8e1307131384c4c4c4c8e1385c4c4c4e1385e0b82e0b82e0f84e2f83e030354000000000000000001302a81c1c1c1c1c2e81c1e81e2a0707a070f81e07aa5a5a66666603030740c0d40c1c0c1e070380e81e5000000000000002a07070b0707a81e8fa0707a070f81e07aa41d6960785d9999980c0c1c1c0c0c1c1c0c1c0c1e070380e81e0355038f07070781e170707073b81e170707072381c1c1c1e0782c1c2e0782c1e0783e078be0780c0d50000000000000000001c083ea07aaaaaaa207aaaaaaa999696999980c1c0c1e96039aaaa940000000000000083eaaaaaa81e8faaaaa999696999980c1c0c1ea81c9e80c0eaaaaa9540e3e1f88ea23aaa23a85eaa85eaaaaaaaaa5400000000000000000800781ea281e83e1381c1c1c1eaa81c1c1c4e81c3ea81c1d99999969680c1c0c1e070380e81c0c0d40c0c1d94000000000000000781e81e8fa0707a0f84eaa81c1c1c4e81c3c1d99999969680c1c0c1e070380e81c0c0c1c1c0c0c1c1e0355038f070781c1c1e0782e0784e0783c1c3e0783c1cbe070707070f81e1707070781e0f80c0d50000000000000000001c081eaa07aaaaaaaaaaa2aaa5a5a66666680e6940c1c0c1eaaaa500000000000000281eaaaaaaaaa81e8faaa65a5a85d99999a03aa81c0c1c0c1eaaaa9540e3eaa85ea2fa85e0788ea07aaaaaaa0faa8beaa540000000000000000080aaaa07aa9980d03402a84e0f81eaaa6650307030780e5038f1384e67aa1f87eaa0ba87eaaa500000804e07a81c1e07a3caaaa07071717a371f371fa0707aa0f0f6666665a5a0307030781c0e03a070303503030760355038f0000000000000004e07a81c1e07a3eaaaa0f0f0fa0707076666665a5a0307030781c0e03a07030307070303070780d540e3c1c7e17072385e0b85e1f82e0f83e0f83c3c3c3c3e0f85c3c3c5e0f83e030354000000000000000001702aa83eaa2aa81ea1faaaaaaaa6666665a5a03130313aaaa80d6a65000000000000002aa83eaaa3eaaa07a83eaa999999969680c4c0c4eaaaa03aa81e9540e3e1faaaaaaaa0faa8beaa0fa85eaa83ea540000000000000000080a81ea1faaaaaaa13aaaaaa8999696999980c4c0c4e039a5aaaa9400000000000000 24 16777215 10 1023
def hc_78_2 : Nat → Nat := unpackHintV5 0x7ff04e7901bc6e9a9a6b68cc65e9605d023a58792250f1e2464aaa4318cc42e80c4298143ce16e344a263238842d114a2609c21a42f219b02417e8721548a8112908082a4003f10e0118b600d81000d800009810009800009800000026000000 0x3c8c1c2c8c5d81c0c430b230702c2c8c1c1c8c2c2c2c2d55555541e5550b0b550fa0f55550303030303030303030303035440c0e03030303030300000000000000070b0b0b230b0b23070b0b0b0b8f2f070f072f0f230707230b0b0b0b5541d3b555541d51f542d50b54bd50f5555555555540c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d40d5540e3c0000000000000000020f07a88eaa13a9591f56644d1f6666643d5560303995a3c00008e2380f83ea95555555543c3e8dc7cdc7e9695555540c0c0c0e030380e80d516a80c0c0c0c000000000000003c3c3c8e23a2382e82c3c8c3e3e230f0f88cbea9523547d5523555923547d59592f543d0f5555555555540c0c0c0e030303030380e030380e80d6555038f0000000000000000000b07a0707070783e0b0f0b41d13544d1f544d1342d1f642d90f555030303036540e3c00004c1c1c2c3c8c070f0f0b0f0f0f730b5555555079542e1b1f1b1b0b95543c3d55540c0c0c0c0c0c0c0c0c0c0c0d440e030303030303000000000000001307070b0f230f8f070f0f0f0b0f0f0f0b072f0f0b0b070f0f070b0f0f0f541d5235550b543d50f5543d5541d0f5555555555540c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d40d5540e3c0000000000000000020782e07aaaa41d135665647d91f666655503a0303995a3c00021f9a1fa84e07a230703c8ea2f955555541c1d5687c7e9695555540c0c0c0e030380e80d5103aa0303030300000000000000070f0fa0b8be0b1381e88c8e23070f0f230f8fa8be5564bd552f5507548d55656543d55555555555030380e0303030303030380c0e03a03595540e3c0000000000000000008c2d47e82d42d543e82d540c0e0380c0281c2c8c2c3c2c3c4e0782c3c2d1347d51f47d567550b5664bd0f43d55540c0c0c0c0c0d95038f00000230b230b0f0f0f02c3c3c2d5555555546e0b86c7c6c6c2e5550f075555030303030303030303030303510380c0c0c0c0c0c000000000000008c2c8c2c3c3c3c3c3c8c3e3c2c3c3c2c3c8c3c2c2c3c3c3c2c2c3c3c3d523547d51f542d50f4bd50f43d550f5550f43d55555550f45d55550303030303030303030303030303030f0333030303030303503555038f00000000000000000083e81da9683eaa0fa66650744d9999595a3c0207aaaaaa5665647d0741d99995540e80d95a3c0002aaaa295555561ba81e96955556955540c0c0c0eaaa946a0380e8000000000000002e0ba0f0f83e0b0b8f83e0b88c3c3e0f0f82c3e0b0b5551f542d59592f543d0f5565550f43d555555555550303030380c0e03a03030380e030303595540e3c0000000000000000002c1ea070baa0f81d0741d0747d0b6541d1f541d07643d55540c0c0c0d95038f000013130f0ba2f0fa41d1364bd0b643d7341d0f56540e3c007c1c1c7d961f07038 24 16777215 10 1023
def hc_78_3 : Nat → Nat := unpackHintV5 0x8c194a84e9cc79c2ca75a1086cb23c66d1785de23c5699d25109644af98441e2463ee0c03be0c036e1402f19f227e1ce1ff9fa1af14213e9c208f2be07d84607981006086405a81804d8340108f400e00a00e00000b80a00002e000000000000 0xa070b130b0f0b070781e070f0b55503070307030340e3d44d134dd37547d1f5642d0b47d0f6564000004c1c1c2c3c1c1c0b0f0f0b1b95542e1b1b1b1f0b81c1d55555555555540c1c0c1c0c1c0c1c0c1c0c1c0c0c1e0303070740c54000000000000004c1c1c2c3c3c1c1c1c1c3e3c2c3c3c2c3c8c3c2c2c3c3c3c2c2c1c1c1d55555555540c1c0c1c0c1c0c1c0c1c0c1c0c0c1c3c1c9c0c3c0c0c1c1d40e3d551f548d50b547d50f543d50f43d550f555545d000000000000000000aaaa8aa81ea1b55a5a555555555555503130313aaaa80eaa0745000000000000000b82e83c3e130f82c2e3e0f82e230f0781c3c3e0b0f82c2d55555555540c4c0c4e0b0380e83c0c0e0780c3c1d40e3d551f555950b543d5950f43d55955559000000000000000000371f13071307371f0b82e0b0b55583e0fa555a255555555550313031303031307aa82c0e03a0f5150000000000000088c4c1e072f230b82e83c2e0f1384c3e0b0b82e0f82c2e3d55555555540c4c0c4c0c0e0780c4c1e0b0380e83d40e3d551f5552f55592f556542d50f5655590000000000000000000b9555070707070b070707130707131384c3c4e130f0b0b0b0b555555555550307030703030780c0c1c1c0c1c0c1c0c1c0c1d140000000000000142e0ba0f83c1c1c2c2e3c3c2c4e81c3c1c1e83c3c3c4c1c1c3c2c3c2c2d555540e0384c4c0c1c0c1c4c00000144e81c4c1c1e84cbd0c4c1c4c1c1c4cbc8c2e0b83c2e0f83c1c1c2c2c2c3c2c2e3d555540e0384c4c0c1c0c1c4c000000015500071307070707070b130b130b07070707074307070707074327272727070707070b13130b555555555555503030707030307070307030703070703070703070307030703074507070b0b8f0f0b270f270f1307070f0b0f0b0b550307030727272727130707130f0b07070b0b0b0f0b0b8f550307030740270b270b1307070b27272727230707230b0b555555550307030703070307030703070307030745544c1c2c1cec2c2c4c1c1c2d0cbc1c3c1cbd0c3c8c1c1c8c2c2d555555555540c0c1c5c0c0c1c5c0c1c9c0c1c9c0c1c0c1c0c1c0c1d1400000000000000001c2d0707070707070795541c1c1c1c2c2c2c2c1e070f0781c1d55555555540c1c0c1c0c1c0c1c0e070703030707030703074500000000000000132313133b13230b0b0b0b547c4c4c7c4cbc7c3c7cbc4c3c2c2c2c2d555555555540c4c0c4c0c0c4c5c0c0c2c2c0c2c9c0c2c2c0c4c0c4d14000000000000002c2c2c2d5555540c9c0c9c0c9c0c2c0c9c0c9d40e3d55235550b5550f54bd5545d0000000000000002c2c2c4c4c4c4c2c2c2c2d5555555542e50b0755130f1384e130f5555030303030303030303030303510380c0c0c0c0c0c000000000000002c2c2c2c2c2e3c2c8c2c2c2c8c2c8c4c4c8c8c8c4c3c4cbc8c3c2c2c2c2d513547d55135551f48d50b550b42d52f543d555555555550303030303030303030303030303030303030303503555038f0000000000000000000f8f07907577683e3e3d5a3c1c1e41d2f0f50f1741c0e3d0f50fa3c5d0f9941c0c1c1c1c2c8c1c1c1c2e3c1c1d5556542d43e83d540c0c0c0d0380c0c0c00003e83d070f80c1d0c 24 16777215 10 1023
def hc_78_4 : Nat → Nat := unpackHintV5 0xc5c980bb6a98b7390cb0b1a2aca902a699849bd2b297c9029149a08e20ca8c18828811028181a47ae1a87788d67430d66b52386760fc63f0dc5dc18c5619ea4ec1d643fab23cf1c231dac62ee0be29616020ca2619c1c20ebac209495c000252 0x4e07a20faa03030303aaa531f531fa0f0faa03036666665a5a0303030380c0e03a030340c0d40c0c58000000000000004e07a23a3e83c3e83eaaa070f0fa0f0f0f6666665a5a032380c0c1e0382e03a0383e0383e030307030f80e03030f0380e0381c0c0c0c0c0e030380e80c0c0c0c0c0c0c0c0d40e3d6035400000000000000000207aa80eaaaaaaaaaa8aa969699999996a60303030303aaaa103680000000000000283eaaaaaaaaa88e8faaa5a5a666666aaa03a8bea0388ea07aaaaaaaaaaa03aa80c0c0c0c0eaaa940e3d695000000000000000000aa2383e0faaa99947e1399e53a87e1faa82ea1faaa80c0c0c0e0340e3d94000008e23a0f8aaaa03030303a371f371fa0f07aa03036666665a5a0303030380c0e03a030340c0d40c0c558000000000000008e23a83c3e23a3eaaaa0f0f0fa0f0f0f666666583e1743d680c7e03032380e0b80e1f80e0f80e0f80c0c3c0c3e0380c0c3c0e0380e17030303030380c0e03a0303030303030303035038f580d5000000000000000000aaaa8aa81ea1faaaaaaaa6666665a5a03030303aaaa9a580c5800000000000002aa83eaaa3eaaa0fa83eaa9999999696a1faaaaaaaaaaaa0fa80eaa80ea03030303aaaa80eaa035038f5a54000000000000000002aaaaaaa9981e07aa81e07a81e1faaaa80c0c0c0d038f65000084eaa0fa1381eaaaa0783eaa40e3d9402a07a87eaaaaaaaaaaaa8999696999980c0c0c0d6a603aaaa1600000000000000aaa23aaaaaaaaaaa8f665a5a666687eaaaaa03a8bea03aaaaaaaaa80c0c0c0e80c0eaa80cceaaa940e3d695000000000000000000aa030303030381c1c1e07070781e13a130fa130faa665a5a666603030303030303030303030380c0c0e0303a031600000000000000aaaaa07aa3eaa0781ea0f83e0783ea99a9990340c0c0c0e80c0002aa0781ea138de0784eaaaa81eaaa8f66a6640d03030303a03000003030313070b073b0b0b1307070b372f070f072f370f230707230b0b507175171741c5d171745d0b45d170340c0d40c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c50300000000000000aaa81eaaaaaaaaaaaa66665a5a6603030303aaa80e03aaa16000000000000001381eaa8f83eaaaaa81c1e0f1faaaa0f66a6640da030303030300001f2387cee230b82e80c0e87e2f83e2f83ea999617582d85d82d980c0c0c0e40c0d60380c0c0c0e03a0316000000000000000b0b0b0b45d1745d0b45d1703230303030303030b0303030303030f0303032f03030317030303030303030303030303035038f5030354000000000000002e55501c1c2d541c1d44c1c1c4c4e130f1384c3c2c2c2c2d55555555540c1c0c1c0c0c1e030307070307030703070307450004c270000000000000b0b0b07070b8f07070b0b070707130707131323130f1313130f0b0b0b0b555555555503070307030307070303070703070307030703075038f5544d513544d235544d5542d50b543d52f5551340000000000000000001e555070b555070701c1e07070781c3c1c1c1c1c2c2c2c2d55555555540c0c1c1c0c0c1e030703070307030703070307450000000000000007070707070b0707070707070b8f072f07070707070f070707070b0b0b0b555541d1755555503030707030307070307030703070307030703075038f5541d5541d3b5541d507542d50b543d52f5550740000000000000000020f07a84eaa07a95607039a3d665647d51344d99995900000f0f5551381e371fa371fa01e0f55a5aa555555555503070307aa0303070781c0e03a07515000000000000000f0f0f1381e88e0ba0b07070f8f81c3c3e0707aa55555555550307030780c1c1c0c0e0781c0e03a075038f5547d5235648d5523555951f543d5955640000000000000000001c1c1c1c1c07070b0f0f0b5507941e070707130781c3d55555555555540c1c0c1c0c1c0c1c0c1c0c1c0c0c1e0303070745000000000000000707070707070f8f070707070b0f0f0f130b070707070b070707130707070f07555555555503070307030703070307030703030707030307075038f5541d507542d513543d50f541d0f5541d55550740000000000000000001c1d5541c4e81c1e81e07a95560701ea955555555540c0c1c1ea80c1c0c1e070380e81d14000000000000001c1c1e1381e0782c1e07a072381c1c1c1c1c3e3e84e13955550745d5555540c0e0780c1c1c0c1c0c1e070380e81d40e3d550755592f5541d50756544d50f565559000000000000000000 24 16777215 10 1023
def hc_78_5 : Nat → Nat := unpackHintV5 0xcb8298c53194b9faceb5f900ac2276a27a6a99e2268f82988a41508441808300507db9527769947069c06b6142617a7a57ea644d42aa47b1643d0aaa345a2c2e598023daa02398102278482220161e98e21859900e1a900a11020349b20000d2 0x1381e81e0faa581d0763d9999582e17a0b83e0f83e0f81c1c0c1c0c1e070380c0ea80e3e5a030707030381c1c7c1c3c1c8c1c3e81c3c3c7e80c0c0e956a83c5c1c3c1c3c3c5c3e81c3ea0000000000000000000b82e83e0faa61344e51666371f13071307371fa0b5680c0ea83c0e95680c4c0c4e0b0380e896aa03031307000000000000000b82e83e0faa61344e42d8f582d985c8e07130785d583e0f83e0f82c2c0c4c0c4e0b0380c0ea80e3e5a031307030381c3c7c3c3c3c3c3e82c2c2c2e80c0c0e83c5d543daa0f170f0f070f0f170fa070fa80000000000000000021ba81eaaaaaaaa9556aa9655555545540c4c0c4d556aaaa15400000000000001507548c2e0b942e0f83d0f5543ea944d555550b63d540c4c0c4d40c0d5541c9e0b0380c0ea80e3d543c7c3c3c3c3c3d43d555541c3e82c2c2c2c2c2c3e80c0c0d43c5d5556a0000000000000000000b81c1c1c1c2c2c2c1c1c1c1c2c1c1c1c3c1c1c3c3e0f0f0f83c3c2c2c2c2c4c1c1c4c4d1384d1382c2c2c2c3c3c3c3c0c1c0c1c0c0c1e030307070307030703070300c1c0c1c000000000000004c4c4c2c1e070b81c1c1c3c0c1c3c3c3c3c3c3c3c2c2c2c2c4c1c1c4c4d131344c2c2c2c2c3c3c3c3c0c1c0c1c0c1c1c0c1c1c0c1c0c1c0c1c0c0307030700000000000000781c1c1c1c1c1c2c1c1c2c1c1c1e070707a3c1c1c1c1c1c1c1c3e3c1c0c1c1c2c2c2c2c1d070741c1c1c1c1c2c2c2c2c3c3c3c3c0c1c1c1c0c1c1c1c9c0c1c0c1c0c1c0c1c0c1c0c030703070000000000000070707607541d51307070b130742c4d0f03070f070f43c3d0741d55075550b03070307070741c0d0000007071381e130780e0f070f41e81d0741c1d070b0b55507070707070b13130b0f0f0f0f07070380e07070307030700000130b5130b0f0f550707061d1307070b5543c0c1c3d43d50b0f0f0b5555555540c1c0c1d41d5030703070307031540000000000001555070f44d541c1c1c1d5550f8f070307070b0f0f0b555541d8f51355555507030703070307030703070315400000000000003c3c2e0b82c2e0380c3c3d07a0759070744c2d8f42c4c5d2c1e81c4c1c4e84c5c8c1c1c4c1c4d43c3c3c3c2c2c0e0384c4c0c1c0c1c000003c3d5076544d9507544c2e0b82c2d0b80e030f0f0f50f41d9550755542d8f0380e13130350700000070f0f13070b073b0b0b1307070b0f0f0303070f0f030f070f070f0f0b0f0f0b41c5c1d17230707230b0b0f0f0f0f03030727030307270307270307270307030703070300c1c0c1c0000000000000001c2c1c1c1c1c1c1c1c1e0707070b0781c1c1c1c2c2c2c2c1e070f0781c1c1c1c1c1c2c2c2c2c1d0781d0783c3c3c3c0c1c0c1c0c1c0c1c0e07070303070703070300c1c0c1c000000000000001c1c1c1c1c1c1c1c1c1c3c3c1c1c1c1c1c1c1c4e3c1c1c1c1c1c1c1c3c3c1c1c1c1c2c0c2c2c1d070741c1c1c1c1c4c4c4c4c3c3c3c3c0c1c1c1c0c1c1c1e3c0c1c0c1c0c1c0c1c0c1c0c030703070000000000000507544c4c4c4d5550f0f83e0f5543e0382d44d5555544d8f550313031355541e3e80c2c0e8550000000000000132313133b13230b0b0b0b0b0b0f0b0f0f0f0f0b0b03030b0b0b030b0b0f0b0b0b1f13131f1347c5c7d13170b0b0b0b0b0f0f0f0f031303130303132703030b0b030b27030b0b030f0300c4c0c4c0000000000000002c2c3c3c3c3c2c3c3c2c2c2c3c3c3c3c0c9c0c9c0c9c0c2c0c0c3c3c0c3c0e3c0c9c0c9c3c8c3c3c3c3c3c2c2c3c3c3c2c2c0c0c0c3c5c3d0f43c3c3cbc3c00000000000002a80c0c0c0c82e0303a0b07a84e13a130fa130faa665a5a6666030303030340c0d40c0e030380e80c5800000000000002a82e8f0b23a0b230b84e23a130fa230faa665a5a6666031f80c0c4e03031f032380e0303130380e0382e0382e0383e038be0384c0c0c0c0c0c0c0c0c0c0c0c0c0e030380e80d40e3d603540000000000000000023eaa3c1ea60783cbc3ea3c3eaa9aaa80c0c1c2c2e0381e07a3e07a0f83d99980c0c0c0d0340c0c0c0002a80c0c0c0c2c2e80c0e82e2a530fa530f81e23aa5a5a666666503030340c0c0c0c0c0e030380e80c40d80c00000000000002a0b230b0b23a82e8fa070fa0f81e23aa5a5a666666030380e030307033b80e03031f80c0c1e0382e0382e0383e038be0381c0c0c0c0c0c0c0c0c0c0c0c0c0e030380e80d40e3d603540000000000000000020fa80eaaaaaa8aaaaaaa999696999980c0c0c0e6035aaaaa160000000000000083eaaaaaa88e8faaaaa9996969999a1fa88eaa23a80eaa80eaaaaaaaaa03030303aa0333a0303aaaaa5038f5a54000000000000000002aa0707aaa9984e0784e13a84e1faaaaaa80c0c0c0d038f650000 24 16777215 10 1023
def hc_78_6 : Nat → Nat := unpackHintV5 0xdf08df6dbc3935722d999c23ac8a088620449af5a3516ed180b4286855b48c29d82054021d49bf0844a806f24841791c210087e8c53f9c8b1d4e500c974205af938248d1e10c030c77a1cc30796b15146507ac5bc2f01cc0b917e03a84401b00480001b0 0xb82e0b83e0f82e8be88c7cee1f2380c0e0b89e0b82c7eaaaaa617985c0c0c0c0e0303030380e00c0c0e0380c0c0e0303800000000000002a948ea87e1fa92e4b84e1faaaaa559555645c0c0c0c0e03a80e3c00008e23a0f83ea80c0c0c0eaa8dc7cdc7e9695455555555540c0c0c0e030380c0e00c3c0c0d555540000000000000192388e565603032380c0c7d5540d6035580e1f80e0b83e0f543d96aa032f48d8f55555555550345d540c0c0c0d50340d6030380c0c0c0c0e03030f038f55000000000000000000aaaaaaa5980eaaaaaaa9231a69a665a5a03030303aaa280eaa039600000000000000aaa81ea23aaaaaaaaa9199969699812aa27aa89eaa000c0c0c0eaa80eaa80e3e580c0c0c0eaaa07a88eaaaaaaaaa48d8f5a69a5a5a6656aaaaaa80ea03a85eaaaaa03030303aaa03aaa038f96a80e03a000000000000000200004e07a0783eaaa80c0c0c0e8dc7cdc7e969555123537555555540c0c0c0e030380e0300c0c0c0d5555400000000000001987d5a13a5a9a55561f81e13aaa5598f9550350380c0e80c000164dd5584e079603555550380c0c1e03032380e80e0b65543e0783eaa030755552363d4dd555555540d55030303030380c0e030303030380c0c3c0e3d54000000000000000002aaaaaa603a5aaaaaaaa6466665a5a03030303aaa280eaa039600000000000000aaa88ea1faaaaaaaaa9692363d999696a176656aaaaaa80ea03a85ea0faa8beaa03030303aaa03aaa038f96aa0333a0303a000000000000000000aaaaaaa81ea1fa59aaaaa6646665a5a03030303aaa280eaa039600000000000000aaa8dea1faaaaaaaaa9a4de663d699696a176688ea37a56aa80ea03a85eaaaaa03030303aaa03aaa038f96a80e03a00000000000000000066666a96a69555aaaaa95598f5566030396030303030000aaaaaa87ea07aaaaa5a55555155555503030303aaa8aa55555000000000000005656aa5aaa87d60355555aaaaaa9955aaaa595555598f5555645d540c0c0c0d955aaa80eaa80e3d540000000000000000002c2c0c0c0c0c0c0c8c0c0c0c0c0c0c2cbc3cbc3c2c3cbc2c0c0cbc2c2c0d03030340c5c3cbcbc3c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c3c0e3c0c0c0c0c000000000000002e070707070b0b01c1c1c1c2c2c2c2e07070783c1c1c3c3e03030f83c0c2c2c2c2c4c1c1c4c4d1384d1382c2c2c2c3c3c3c3c0c1c0c1c0c0c1e030307070307030703070300c1c0c1c000000000000002c2c2c1c1c2e3c1c1c2c2c1c1c1c3c1c1c3c3c3c3c3c3c3c3c3c2c2c2c2c4c1c1c4c4d13131344c5c2c2c2c2c3c3c3c3c0c1c0c1c0c0c1c1c0c0c1c1c0c1c0c1c0c0c1c3c0c3c0e3c0c1c0c1c1c4c3c8c1c3c1c4c3c1c3c3c4c3c8c1c3c1c3c3c4c3c1c3c1c3c2c2c1c2c2c2c1c2c0c0c0c3c5c1d0f41c3c1c4c3c0000000000000000001e070707070707070b0781c1c1e070701c1e07030780c0c1c1c1c1c2c2c2c2c1d0781d0781c1c1c1c2c2c2c2c3c3c3c3c0c0c1c1c0c0c1e030703070307030703070300c1c0c1c000000000000001c1c1c1c1c2c1c1c1c1c1c1c2e3c1c1c3cbc1c1c1c1c1c1c3c3c1c1c1c1c2c2c2c2c1d07070741c5c1c1c1c1c2c2c2c2c3c3c3c3c0c1c0c0c1c1c0c0c1c1c1c9c0c1c0c1c0c1c0c1c0c0c1c1c0c3c0e3c0c1c0c1c1c1c1c1c1c1c3c1c1c1cec1c1c1c3c1c1c1c8c1c1c1c1c1c1c1c1c2c1c2c1c1c1c2c1c1c1c0c0c0c1c5c1d0741c1c1c1c1c00000000000000000281c2d44c2e0f83d541d50307030703a038f4b0f4b0f07071f0f1f0f0707130f1f0f130f0f82c2c2c2c3c7e030355a00001781c1c1c1c3c3c4c1c1c2c6c6c2e1b1f0b83c1c1c3d40c0d542c3c3c2c41d555555555030703075079540c1c0c1c0c1c0c550000000000000045d1307070b542d50f07070f543d0f50b0f0f0b41d8f555555540c1c0c1d541c9d40c0d40c1c0c1c0c0c1c3c0c3c0e3d541c7c3c8c1c3c1c8c3c1c3d5541c3d43d542c2c1c3c3c7c1c2c0c0c0d55541cbc3c0000000000000000001e07a0781ea945984d139981c1c1d50707a07070713a0303aa0703a55a0307030781c0e03a25aa80c0c1c1c000000000000001e07a0781ea90763d60761344e66560b81e1381e0f81e0f81e17070307030781c0e0303aa038f9680c1c1c0c0e070707070707070707a07070713a030303a071755076a81c5c1c1c1c3c1c1c1e81c3ea0000000000001c2700000000781c1c1c1c1c1c1c4c1e07070781c1c1c1d5540c0c1c1c1c1c2c3c3c2d55554544d5555550780c1c0c1c0c1c0c1c0c1c0c550000000000000050744d550b0707070750f2f5550f0f070707070b0f0f0b55550763d44d55540d5507030703070307030703030707030f038f5550755555070f0707072307070707070707070b07070713070703030350717555507070700000000000000000060744eaaaa81d9aaa0703aa0303aa3c4c3c4c3ea81c1e0f1faaaa0f1fa0396a000008f687ea8f1381e81e0faa581d0763c66665070707070f6a0c7c7e80c0ea83c0e95680c1c0c1e070380c0ea80e3c96aa0303070700000000000000 25 33554431 11 2047
def hc_78_7 : Nat → Nat := unpackHintV5 0xb3d16cab3a26a73102a071b09b015c91d24c8da10c86d9b282b9087c21a678210072317c6b01cc6778e264a8b45a928656a0fc4fa9be46fa2c4021b6346aee30011a2fc80e2f900e2819de27c81426e03a1bcac614d9bc0aa28e04698e00011a 0xaa070723171381e531fa531fa81e0f55a5aa155555555503070307507075581c0e030f2070f5500000000000000644e07959581e0f543d96a90763d555555503070307541d03581c0e030f038f80c1c3d541c7e23072387d5562752f5582e1f87e0b80c0d55541c3c3c000000000000000002aaaaa919999a0795aaaaaaaaaa55a03070307aa8a96a81e03a00000000000000aaaaaa41d8f5a69a6656aaaaaaaaa03070307aaa038faa96a81e03a81ea07aaaaaaa956aa17a89eaa85e078000000000008270000000aa070707070713a0707a0781ea55581e07aa555551555555507070307030781c0e03207550000000000000059135560781e58bd5543c3e0781ea955541d8f5135555035541c0c1c0c1e070380c3c0e3e030707555075555589c1c1e07070781e0b81e1381e03035555070707000000000000000000aaaaaa6466665a81e6aaaaaaaa95680c1c0c1eaa032a96a81e03a00000000000000aaaaaa5a41d8f666656aaaaaaaaa03070307aaa038faa96aa0727a0303a87ea23aaaaaaa956aa17a89eaa85e0f8000000000000000002aaaaa999199a1fa81eaa56aaaaa95680c4c0c4eaa2a5aa0780e800000000000002aaaaa9a44e663d699a23a81e95aaaaa80c4c0c4eaa80e3eaa5aa0780ea1faaaaaaaaa55aa85ea27aaa1783e00000000000000000087ea07aaaaaaaaaa555aa555555515503130313555aaaa2a55000000000000005656aa5aa9955aa9655555663d540c4c0c4d955aaa80e3ea9561faa965555589eaaaaa555583e000000000000000000aa07070b0b0b81c1c1e07070781e0fa0f0fa0f0fa0fa0b1381e13684daaaaa03070307030307070303070781c0e0320781c0e00000000000000aaaaaa6681e63d84e4ba81e07a84e0796aa80c3c0c3c4c4e0703800029599599999aa9aaaa595655663c0c3c0c3c4c4e5800001c9c9c4c1c2c1cec2c2c4c1c1c2cbc0c1c3c0c0c3c3c8cbc1c1cbc3c2c3cbc2dcd0717075cc5c8c1c1c8c2c2c3cbcbc3c0c0c1c3c0c0c1c3c0c1c9c0c1c9c0c1c0c1c0c03070307030700000000000000aaa81eaaaaaaaaaaaaaaaa9a9aaa03070307aaa81e03a8aaa00000000000000132384cee230b82e89c2e0f83e0382e0382e0ba2f87e13a617985eaaa80c4c0c4e030f0f030382e0b270382c0c83e13038000000000000002c2cbc3cbc3c2c3cbc2c2c2c3cbcbc3c0c9c0c9c0c9c0c2c0c3c0e3c0c0c3c3c0c9c0c9cbc8c9cbcbc9c8c2c2c9cbcbc2c2c0c0c0cbc5c9d2f49c5c3c3c3c0000000000000082e83e0faa03030303aaa0b070303a0f0faa0f0f1384eaaaa13684da0303030380c0e03803030303030303030380c0e00000000000000aa0ba3c2c8e82c8c2e03031380c0c7e0380c0c4c0e0380c0c7c0c8e0382c0e0382c0c2e0f83e83c3e83c3eaa03132384e23684daaa980e617aa03030303030303030303030380c0e030303030380c0c3c0e3e0303800000000000000000281c2c8c1e07a3e0783eaa030382c0e07a0781e6603030303030307038f030303030000a63e68f0b23882e0783eaaa80c0c0c0e82c2c0c0e81c1ea83c3c8e07aaaa9a680c0c0c0e030380c0e0300c3c0e3c0c0c0c0c0c0c0c0e0303800000000000001a663e8f81e5ee65178fa82c8c2c2c8ea0ba3e0380c0c1c0cee0380c0c0e03030780c0c7e0382e0382e81c3e83c3e0783eaa0307681da2381eaa980e617aa03030303030303030303030380c0e030303030380c0c3c0e3e030380000000000000000000c0c0c0ea80e07070781c1c1e0783e83c3e83c3ea84e0784da136aaaa80c0c0c0c0c0c0c0c0c0c0c0e030380e00e03038000000000000004c1c1c2c8cbc1c1cbc3c2c3cbc2c0c0c0c2c2c1cec4c1c2c3c3c1c9cbcbc1c3c8c1c1c8c2cdc2c3cbcbc3c1d37173741c5c0c0c0c0c0c0c0c0c0c0c0c0c0303030303030303030303030300000000000000aa0f83e83e83e84c1e07a3c0e84c1e0380c0ea87e1387e13aaaa80c0c0c0c0c0c0c0c0c0c0e00c0e80e0303800000000000281ea03aaaa07a3eaaaaaaaaaa9a9aaaaaaa80eaa0303030303aaa2aa00000000000000 24 16777215 10 1023
def hc_78_8 : Nat → Nat := unpackHintV5 0xd9f27acfba8ec62a64bc1286b6d94eafd1c2a4dabea168dc9e08d89809809648708f01d28472a47d29d278792c6daab4696910635984587ab8527980478abc4448d04001123c10fc3a1080312a3a287a2c21a1b6164ad60f31c6035af60000d6 0x2e03030303030303070707070b0707070f07070f0f83c3c3e0f0f0b0b0b0b130707131344e1344e0b0b0b0b0f0f0f0f03030303030303030380c0c0c0c0c0c0c0c030303030303030000000000000003030313070b073b0b0b1307070b0f0f070f070f0f0f0f070f070f0f0b0f0f0b3741c5c1d3717230707230b370b0f0f0f0f03030303030303030303030303030303030300c0c0c0c0c0c0c000000000000001c2c0c1c1c1c1c1c1c1e030303030381c1c1c1c2c2c2c2c1e070f0781c1c1c1c1c1c2c2c2c2c1d0781d0783c3c3c3c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0e00c0c0c0c0c0c0c000000000000007c8c7c7cec7c8c2c2c2c2c0c0c0c3c3c3c3c2c2c3c3c2c2c2c2c2c2c3c2c2c2c7c7d3d1f171f53c5c2c2c2c2c3c3c3c3c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0303030303030300000000000000a070b5230b83e0f4b034b0303031f031f0303031f03130380c2e0f03551355540c0c0c0e038f80e800000c0c5e030303031b1b0b86c7c2e230b230b50f07550f0f0f0f0b0f0f0b55551555555503940c0c0c0c0c0c0c0c030303550000000000000045d230b230b542d50f0f0f0f543d0f50b0f0f0b031f030303230303555030350355030b0303031f0303030f0348d8f5555555555540c0c0c0d540ccd40c0d40c0c0c0c0c3c0e3c0c0c0c0c0c0c0d540000000000000000004c1c1c4c0eaaa1363d99a947e43a87e1faaaaaaaaa0380c0e0000802d681eaa84c0c1c0ea80c0e031faaaa0366a6680c0ea8f80e800004e0780c0c0d50303a371f371fa81e0faaa0707a0f0f46665a5a660303030380c0e03030303aa280e58000000000000004c1c1c4c0eaaa66271f1f27aa80c4e07a0783ea80c8c0c0c0c1c0c0e80c0c0e80c1c0d199999696812272783e83c0c0c0c9c0c9c0c0e000c0c0c0e0303a80e3e80c0ea96030303031381e81e0faa0323030303070303a030303a03070348d8f585d85d9996969582e17a0b83e0f83e0f0303030380e1703031780e0385c5c0c0c0c0e0303a80e3e80c0ea9680c0c0c0c0e0300000000000000005c00003030780c0c0c0c4c1c1c2c6c7c2e1b1b0b83c1c1c3d5541c1c2c3c3c2d45555555540c0c0c0c0e5550303030300c0c0c0c0d540000000000000191f1f55547cdc4c1c1c4d0b1f560b0303943e0781c3c2d544d8f550b40d40c0c0e80c0c000145d375542c4c1c1c2d0f5543c3c1c1c3c2c3c3c2d40d555540c0c0c8c0c0c0c1c0c0c0c2c0c0c0c0c0c0c1c0d55548d8f53755555555035540c0c0c0c0c0c0c0c0c0c3c0e3c0c0c0c0c0c0c0d5400000000000000000181d23aaaa87c0c4c0ea80c0e031faaaa031fa0384d9a99aa0303aa03a8f80e8000008e23940c0c0c0c0da371f371fa83e0faaa0f07a0f0f64665a5a660303030380c0e03030303aa2a80e58000000000000008e23a0f83ea80c7c0c0c0c8c0c0e80c0c0c7e80c3c0d61748d8f66665a5a560b85e82e0f0f0f83e0f172f83c0c0c0c0e0385c0c0c5e0380e17170303030380c0ea038fa0303aa5a030303030380c0000000000000000002e0b8dc7cdc1cdc1cdc7e80d5a83e0faaa0f07a0f0f66465a5a660303030380c0e03030303aa280e58000000000000002e0ba0f83ea80c7c0c0c0cdc0c0e80c0c0c2e80c3c0d85d3790b63d60b665a5a172385c5cde17560f83e0f83c0c0c0c0e0385c0c0c5e0380e0b0b0303030380c0ea038fa0303aa5a030303030380c00000000000000000296aaaa81c0c1c0eaaa80c0e031faa035555580c0ea8f80e800000c0d5076544d90744c2e0b90b83e0f0f0f0f50f55075542d8f80e030303035030000aa86ea07aaaaaaaaa555a555155555503030303aaa5552a5500000000000000661303070355aa80d5aaa96a3e03a002555230b82e50b83e0f43d550faa031f0303030303503555550303a0303030ba030f0355555542d8f5555550303030350303555033380c0ea038fa0303a9540000000000000000002c2c3c3c3c3c2c3c3c2c0c8c0c0c0c0c0c0c2c0c0c0c0c0c0c3c0c2c2c3c3c3c3c0d03170340c0c0c0c0c0c0c0c0c0c0c3c0e3c0c0c0c0c0c0c0c0c0c0c0c00000000000002a81c1c2c2c81e0b0ba0707a81e0fa0f0fa0f0faa1381e13684daaaaa03070307030307070303070781c0e0320781c0e00000000000000aa07a3c1c1e81c1c1e0783e83c3e83c3ea84e0784da136aaaa80c1c0c1c0c0c1c1c0c0c1c1e070380c3c0e3e03070f81c0e071384c1c4e131313132384e2713131384e2382e0b82e0b80c0e179984c1c3c3c000000000000000002a81c1c1c1c1c2e81c1e81e2a0707a070f81e07aa07681da0781eaaaa03030707030307070307030781c0e030f2070781c0e00000000000000a81c1c2c1c1ea07a3e078bc1c1e81c1c3c3e0781ea81da07681e07aaaa80c0c1c1c0c0c1c1c0c1c0c1e070380c3c0e3e03070781c0e07070781e270707073b81e27070781c1c1e0782e0782e0780c0e179981c1c1c1c000000000000000002a944eaa55950307030780e3e92e4ba87e1fa84e13aaa9543e0000 24 16777215 10 1023
def hc_78_9 : Nat → Nat := unpackHintV5 0xeb20d871bc7ab612599a0420ac4f1665f78602e1834958b302a8388452243f26de4692a61928a415e42d04a1fe6304ed92347088c835306298a23ecad1300537862280c3611fa4187ef21c35b93812cd02082a2782d52801678060a78188410258000410 0xb81e030350340c0e81c1c2c2ea0784eaa84c3e84c3d13184d82d0b96969980c0c4c0c0c0e032aa0303030303a03960000000000000003030307030303130b81e03030781e13a0303a030faa465a5a666604031303030303031382c2e27a2780030313030303aa80c0e80e3c0e80e580c0c0c0c0c0c0c1c0c0c0c4c2e0780c0c1e0784e80c0e80c3ea91363d6135a5a60b42e66540c0c4e0380c0c0c0c0e0385e0b82e0b82e0f84e2f83e1713030313030303aa80c0e80e3c0e80e5a030303030380c0000000000000001300002c1c1c2c0c0c1e030303035070755130707130b0b0b0b1384c3c4e130f5444d42d555555503031303030303030300c0c0e5550303030355000000004c270000000513503035555503030303070303031342d550b0b07070b0303074bd550f13070713031303030303030f0b0b0b0b55551363d555542d55540d550303031303030303030303030303030b038f03030303550000000000000000000b82e0340c0c0c0d682c1c2c2ea1384eaa84c3e84c3d91996969980c0c0c0e032aa0303030303a03960000000000000060b80c0c0c0c0c7e80c0c0e80c5e1387eaa80e80d84d1319903a603a3d980c0c7c0c0c0e80c0c0e80e3ea03a039600000000000000303031f0303031f0b82e03030b84e1fa0303a030faa584d1363d035a580e176666540c0c5e0380c0c0c0c0e0385e0b0b0b82e0b1782e0f85e2f83e131303031f030303aa80c0e80e3c0e80e5a03031703330303030380c0000000000000000002c2c0c0e0b0ba0f83c7d0742d0b41d951f6543d550f63d540c0e0380d030340002aa13a81e96956aaaaaaa955555554540c0c0c0e8a9556a954000000000000000c0c0c0c0c0c8c2e0b80c0c2e0f83e80c0e80c3ea91f544d5035550340d550b542d50f5555555550f63d5550303030303aa80c0e80e3c0e80d50340d5540000000000000000002e0b84c4c4c1c4c1c4c4e82c1c2c2ea0f83ea940c0e40c0d99996969180c0c0c0e032aa0303030303a03960000000000000003030337030303230b82e03030b83e0fa0303a030faa665a5a6643d8f583c5c7e13171385c0c0c5e0380c0c0c0c0e0385e0b82e0b82d583c3c0c0cdc0c0c0eaa0303a038f03a039680c0c0c0c0e030000000000000000000b0b030382c2e41d0747d1f42d0b547d1f541d0783e0f45d55543d8f030380e030350300000b82e83e0faa131313071307131350b07550303aa03035555515555030313030303a03280e80e955554000000000000000c0c0c0c0c0c8c2e0b80c0c2d513547d550340d5503550b542e0f83e80c0e80c3ea945d5555555555543d8f0303030303aa80c0e80e3d035540c0e80d540000000000000000002e0b84c4c4c1c4c1c4c4e82c1c2c2ea0f83eaa80da566665a5a6403031303030380caa80c0c0c0c0e80e58000000000000007e1f80c0c7c0c0c0e80c0c0e80c3e0f83e6a030380c3d9999a69900c0c7c0c0c0e80c0c0e80e3ea03a039600000000000003030337030303230b82e03030b83e0fa0303a030faa665a5a666427272727032703030303032782c2e4080030327030303aa80c0e80e3c0e80e580c0c0c0c0c0c0cdc0c0c0c8c2e0b80c0c2e0f83e80c0e80c3ea99969699960f43d8f0f1f83c3c4e0f03030f80e030303030380e0f82c2c2e0b82c3e0b56170f030337030303aa80c0e80e3c0e80e5a03030f03330303030380c0000000000000000f00000c8c0c2c7d0740d0342d0b43d0f63d540c0c0cce9073340000c8c0c2d0747d0340d0344d0b42d17550f63c0c0c0cce8cd41c0000c0c0c0c0c8c2c2c2c2c0c0c2c7c4c4c7c0c0c0c0c2c2c2c2c7c4c4c7c0c0c0c0c2c2c2c2cdcdc0c0c0c0c0ccc2c2c2c2c2c2ccc4ccc4ccc4ccc4c00000000000000c0c0c0c0c0c8c2c2c2c2c0c0c2c0cbc0c0c0c0c0c3c2c2c2c2c0d03030340c5c2c2c2c2c0c0c0c0c0c0c0c0c0c0c0c0c0c2c0e3c0c0c0c0c0c0c0c0c000000000000002e03030303030302c2c2c0c0c0e0b070383c3c3c3c3e0f070f83c3c2c2c2c2c4c4c4c4c4d1384d1382c2c2c2c3c3c3c3c0c0c0c0c0c0c0c0c0e03030303030300c0c0c0c0c0c0c000000000000002c2c2c2c2c2e3c2c8c2c2c2c8c2c3c3c3c3c3c3c3c3c3c3c3c3c2c2c2c2c0c7c0c0c0c4c0c0c0c7c0c8c0c0c0c0c0c4c0c0c0c0c0c0c2c0c0c0c2c0c0c0c3c0c8c4c4c8c8d13171348c5c2c2c2c2c3c3c3c3c0d03170340c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c3c0e3c0c0c0c0c0c0c0c0c0c0c0c0000000000000000000c0c0c1c1e030303070b0b80e0707070b8f0f07070f81e07070737660303030380c0c0c0c0c00001e0303030303030b0b0380c0c0e0b0702c3e0f0f0781c1c3c1c1c3c2c2c2c2d8d3798d3788c1c1c8c2c2c2c2c3c3c3c3c0e030303030303030303030303030300c0c0c0c0c0c0c0c0c00000000000001a668f03070340ded0745d03538f0707070b0707070b8f0f07070f03030303070307030307030b070353070737030303a030700070b0b0b230b0b23070b0b0b0b8f0f0f070f070f0f0f0f07070f0b0b0b0b0303030303030307033b03030303031f030303070303030b0303030b030303070341c5c1d3717230707230b0b0b0b0f0f0f0f0340c5c0d030303030303030303030303330303030303030303030f038f0303030303030303030303000000000000000000 25 33554431 11 2047
def hc_78_10 : Nat → Nat := unpackHintV5 0x81283f1f30234799c649d112ac7140609b3623469986818f62e062283617fd11a5e3038976d03e5a8865959f206546c42146d15c4f644a13011b047089f90b421c3db4a38e921b633fcc98baf2a0266d0a089a2021c7cbd85e72701238ac825647005d47080002ea 0xaaaaaaa81ea1f55a5aaaa5555155555032703278aaa5a5555000000000000000b82e83e0faa47d507542d50b543d555543d8f55540c9ccc0c9e80e3c0c0e80e83d50740d554cc8c9ccccc9c8c0c0c0c3c3ea83c3d5541c9d4cd555556a0000000000000000000b82e83e0faa6666461b1b1b071b071b1fa0b030303a0f0f950f07a55a0327032780380e83e5aa80c0c2c1c000000000000002e0ba0f83ea999990f63d60f171f81c5c1e1782e0b82e0b560f0f0327330327a038f0303a03a0f9680c5c1c0c0e07332327333327230303030f0faa0f0fa55aa171717170727171733a0717a80000000000000000002e0b93c7d3c1d3c1d3c7d40c0d560f83eaa83c1e83c3d55555555440c9ccc0d3c9e803a555a03a0f55000000000000000b82e541d51f542d50b83e0faa517555555550f63c0c9ccc0c9e80e3c0c0e9035541c0e83d54cc8c9ccccc9c8c0c0c0d4cd555541c9c3c3ea83c3d5556a0000000000000000000b82e83e0faa666664371f4f074f07371fa0b030303a5aa0f695680c9ccc0d3c9e0300c0e03a0f96aa03030b07000000000000000b82e83e0faa6666583d0f63c3c7e070f0783e0b82e0b82d585c3c0c9ccc0c9e80e3c0c0e80e83e5a030f0f0727030f030381ccc8c9ccccc9c8c0c0c0c3c3ea83c3e956a83c3c3c3c1c9c3c3cce81c3ea0000000000003c2700000000327a0340d1f41d0b42d0f5030f63d540ccc8c8c0c0d073340c0000327a03030f63d0f030303031f0707170b0b0b0b50f0f033323230303170733070300000c9e90340d0747d0b42d17550f63c0ccc8c8c0c0d334f541c1c0c0000707a330f03033700c9e80c0c0c0d0f0f63c0c3c0c0c0c0c0c7c3c7c1c1c3c1c3c2c2c2c2d45c3c0ccc8c8c0c0c3c3c1c1c3ccd3c1c0c000f09c003032703030303030b0b07070b030303031f07071f0b0b0b0b030303031f07071f0b0b0b0b030333072307070723030303330733073307330700c00000000000009c9c0e0382c2e0f83c7d95076547d0742d0b43d550f63d540e0389c9d0703400009c9c0e0382c2e0f83d983d8f43c7c5c6c1e81c5c1c5e87c1c1c5c2c2c2c2d43c3c0e0389c9c0c1c0c1c00009c9c0e0382c2d50741d51f47d0741d1f47d0b42e0f83d1755550f63c0e0389c9c0d41c00009c9c0e0382c2e0f83d990f0f63c7c3c7c1e81c3c1c3e87c3c7c1c1c3c1c3c2c2c2c2d45c3c0e0389c9c0c3c1c1c3c0c0c1c00003c2701c9c9c2c0c1c2c0c0c2c2c2c2c1c1c2c2c7cbc1c3c1cbc7c3c7c1c1c7c2c2c2c2c7d07170747c5c7c1c1c7c2c2c2c2c0c0c1c2c0c0c1c2c0c1c9c0c1c9c0c03070307030703070307000000000000000b0b0b0b0b0b0b0b0b0b0b0b0327330327030b038f03030b0b032703270327032733232733332723030303330f272f332f270f3317274cd27170b0b0b000000000000000b0b07070b0b0303030b0b070b0b0b070b1f07071f0b0b0b0b072f1f0f1f2f070f1f07071f0b0b0b0b0747c5c7d07173737030303030303030300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c000000000000002e0b80c0c0c0c0c0c3c3e82c1c2c2e80f83eaa80c0e80c0c4e13aa84da136aa80c0c0c0e032aa0303030303a0380c0e000000000000000f0f0f0303031f0303031fa0303031f0303030303a03230b82e82e0b82e0b03030b0f130f8f84c3c3e131380e2f0303a03030f0faa1f84e985e61703680daaaaa03031f03030380c0c7c0ccc0c0c0c0e03aa80c0e80e3c0e80e030380000000000000000002c1c1c2c0c0c1e030303030781c1c2c2c2e0f1301c3c3c2c2c2c2c2c2c0e03030383c3c4c1c1c4c2c2c2c2c4d1384d1383c3c3c3c0c0c4c0c0c0c0c0c030380c0c0c0c0c0c0c0c0c0c0c0c0c0c000000000000000c0c0c1c0c0c0c4c2c1c1c2c0c0c1c3c4c3e3c1c3c3c3c0c3c0c0c0c0c0c3c2c2c2c2c2c2c1c4c3c0c0c3c0c0c0c0c0c0c0c0c0c0c1c3c2c2c1c2c2c2c1c2c3c3c3c4c1c1c4c0d03030340c4c2c2c2c2c3c3c3c3c1d0f170f41c3c0c0c4c0c0c0c0c0c0c0c0c0c0c0c2c0e3c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0000000000000000002e0780c0c1c1c0c0c0c0e81c1c2c2ea130703c4e82e0ba80c0e80c0c4e07aa84da136aa80c0c4c0c0c0e80c0ca038faa0303030303a0380c0e00000000000000070f0f03030303a032fa0303031303030303070303031382e0b82e0b0b81e03030784c7e13070f0f130f8fa0303a030fa0b82e984e6171381e03680daaaaa030380e030303030313030303aa80c0e80e3c0e80e030380000000000000000002c2c2c2c0c0c0c0c0c0c4e0b82c1c2c2c2e0f0f0f02c2c2c2c0e03030383c1c4c4c4c4c2c2c2c2c4d1384d1383c3c3c3c0c0c0c0c0c0c030380c0c0c0c0c0c0c0c0c0c0c0c0c0c000000000000007c2c2c2c0c0c0c0c0c7c0c0c0c0c0c0c3c0c3c3c3c3c3c4c0b0f0b0b030303030303030f8f1f13131f1f1f1f1f0340c0d030f0f0f0f03031f0303030303030303031f038f030303030303030303030300000000000000303031f0303031f0b0b0b0b03030b0f0f0f0f0f130f8f03030f2f0303030303030f0f0b0b0b0b0f1f0f03030f030303030303030303030f0f0b0b0b0b0b0b0b0b0f0b0b0f0f0f1f13131f0340c0c0d03170b0b0b0b0f0f0f0f0f43c5c3d0f0f03031f03030303030303030303030b038f030303030303030f0333030303030303030303030000000000000000000b0b0b0b03030303030313942c1d544c4c4c4c2c2c2c2c4e130f1384c3c55555555540c0c0c0c0c0c030395540c0c0c0d54000000000000011740c0c0c7c0c0c0c7d5540d40c0d542c2c2c2d50b42d40c0c2c7c4c4c7d50f4bd40cbc0c0c0c0c0c3c2c2c2c2d1363d555555540d17555503031f03030355033350303503030303030303030b038f0303030355000000000000000000 26 67108863 11 2047
def hc_78_11 : Nat → Nat := unpackHintV5 0x94d86824961408ef06d226d29e8380c69f4333a7774b31ce61ee6fd0791a962bc66907918362dc5dcc61965324055e06d93f53064ab4a410994283f28678edd1da3558c38c1628027e90e09191c21eb8b586de1a015d0b5048a1d40e707702302d805a06400002d0 0x3a03230b230b83e0f0b2f6650f63d0f1f07071713171317a1f171b13a0b0b0b0b0b171f0b50f0f232389e0b270b03070307000003a03230b230b41d1f547d1f544d13542d50b83e0f0b2f45d555543d8f232389e0b270b03507000003a03230b230b83e0f0b0f66543c3d8f1f07070f130f130fa1f0f1f0fa0b0b0b0b0b0f1f0b5170f232389e0b270b0307030700000f09c03030b0b0b0b0b030b230b0b0b0b0b230b1f13131f132f1f0f1f2f130f0b0b0b0b0b1f13131f1347c5c7d13170b0b0b0b0b031323032300c0c4c9c0c0c2c2c0c2c9c0c2c2c0c4c0c4c0c4c0c4c000000000000002c2c2c2c3c3c3c3c4c3c2c2c2e3c2c3c2c2c3c7c3c1c3c1c3c3c2c2c3c2c2c2c7c4c4c7c2c2c2c2c3c3c3c3c3d0f170f43c3c0c4c7c0c7c030b030b030f030f03030f0703030f070313031303002c2c2c2c3c3c3c3c3c3c3d5c3c9c3c3c9d5c9d5c4c01f1f130713071f1f0b0b0b0b0b0f0b1f0f1313130f0b0b0b0b0b0b0f0b0b0b8f1f13131f1f47c5c7d1f170b0b0b0b0f2f2f0f03131f031f00c7c0c0c4c1c0c0c4c7c1c9c0c2c0c2c0c4c0c3c0c4c0c4c0c01f271f1f1f1f1f570b0b0b0b0f2f270f2757275713002c2c2c2c7c4c4c7c2c2c2c2d131344c5d0b63d42c2d1745c5c7c4c1c4c1c5c5d5170f1717172f170f0b0b0b03131f031f00c2c0c2c0c4c0c4c0d44c0c0c4c1c0c0c4c1c0c00b0b0b0b275727571751717171757172717171301507547c2c2c2c2d42c7c4c4c7d2f5543c2c2c2c2d44d555550b63d540c4c7c0c7c40d5507030b030b03130313550301275550c2c2c2c2c9d0c9d0d544c0230b230b0f0f0f0f0b0f0f0b47d507542d51f543d555543d8f55540c8c8c0c8c0327030b030f030f541d0355503002d0c9c2c3c3c3c3d54349d5549c0230b230b230f230f0b0f2f0b45d1745d0b43d8f50f0f171f1707170717170b0b1717171f0b0b543c3c3c0c8c8c0c8c0327030b0327030f03517030317070303170703002d5c9c2c3cbc9c3c5d45c5c5c5d5c5c9c5c5c9c0230b230b541d51f547d50b230f230f0b0f2f0b517555555550f63c0c8c8c0c8c0327030b40d55070327030f5503002d0c9c2d275550c3cbc9c3d549c0230b230b0f0f0f0f0b0f0f0b45d1745d0b50f0f43d8f0f1f0f070f070f0f0b0b0f0f0f1f0b0b543c5c3c0c8c8c0c8c0327030b030f030f0351703030f0703030f0703002d5c9c2c3c3c3c3c5d45c3c3c3c3d5d5c3c3c9c9c3c3c9c0230b230b232323230b0b232323230b0b032323032300c9c0c2c0c9c0c9c0c9c0c9c0c00b57270b275727572757275727008c2c8c2c8c8c8c8c2c2c8c8c8c8c2c2c0c0c8c8c0c8c0e3c0c9c0c2c0c9c0c9c0c9c0c9c0c0c0c2c2c8c8c8c2c2c8c3c8c8c8cbc8c3c8c5c8d2348c5c8ccc8c000000000000023003c3c1c1c1c1c7c3c2e0782c0e80c0e80783e83c3e81c1ea87e0787da1f6aaaa80c1c0c1ea80c0c1c1e00e03a0781c0e000000000000000f0f0f0b81e82e0b82e0b07070f8f81c3c3e0707aa1f81e985e617aaaa03071f031f0780c1c7c1c9c0c7c0c0e07a038f0303a03a0781c0e071f071f071f071fa1f23071f07271f1f1fa07230303030f0faa070fa0747daa80000000000000000001c1c1c1c1c07070b0b0b0b0b0b070707070781c1c1e070303030781c3c1e0781c1c1c1c1c1c2c2c2c2c3c3c3c3c1d0781d0780c1c1c0c1c1c0c03070307030703030780c0c1c1c0c1c0c1c000000000000001c1c1c1c1c1c3e3c1c1c1c1c2c2c2c2c2c2c1c1c1c1c2c1c1c1c2c1c1c1c3c1c1c1c1c1c2c2c2c2c3c3c3c3c1d07170741c1c0c1c1c0c1c1c0c2c0e3c0c0c1c1c0c1c0c1c0c0c1c1c0c0c1c1c0c1c0c1c1c1c1c1c1c1c1c1c0c0c0c1c3c1c1c1c3c1c1c1c1c1c3c1c1c1c9c1c1c1c1c1c1c3c1c5c1d0741c1c1c1c1c0000000000000000020781e0701ea81e07aaaa80c1c1c0c1c1c0c0ea80e3c1c0e81e070381c1c1c1c1c1c0c0ea80c0c1c1ea81e0707aa00000000000007070707070707070303a0703a0781ea0707a070f81c07a0b82e07681da0781eaaaa03030707aa030707030707a00e80e81e07038000000000000001c1c1e070b81e0781c2c2c1e07a071f81c1c1c1c1c3e3e82e0ba607985c1e07aaaa80c0e0780c1c1c0c1c1c0c1c1e80e3c0c0e80e81e070381c1c1e81c9e81cbc1c1c1c9c1c1c1c1c1c1c1c1c0c0c0c1c3ea81c1e81d076aa0000000000000000000b07070b0f070702c2c2c2c7e070707071f1f0b82c0c0c0c2e07070783e0f0f1f07071f0b0b0b0b0f0f0f0f1f47e1f47e03070307030300c0c1c0c1c0c1c0c0c1e0303070703070307000000000000000b07070b0f0f070707070f8f0b0b0b0b0f1f0f0b0b0b0b0b0b0b0b0707071f07071f0b0b0b0b0f0f0f0f0f43c5c3d0f0f03071f031f07030b038f0303070b030703070303070f0727030f0303070703070307071f071f071f071f0303030f0f070f0f0f070f0f0f0f0f070f07270f0f1f070f070f1f170747d0717070b0b0000000000000000001781c1c1c1c7c5c2c1c1c2d540c0d47c1c1c7c7e1f0f1f87c3c2c2c2c2c55555555540c1c0c1d41e550300c1c0c1c0c1d54000000000000011742c1c1c2d50b42d47c1c1c7d50f4bd42c2c2c2d0763d555555503071f031f07550727503035030b038f0303070b0307030755071f071f071f071f555072751f550303031f0f071f1f2f070f5555070b0b0000000000000000000781e81e07aa4660b42e66070707541c1e81c0c0c0e81c3ea81c1e95680c1c1c0c1c1e00e03a0796aa03030707000000000000000781e81e07aa41d8f581d82d0b999582e0782e0783e078be0785c1c0c1c1c0c1c1e80e3c0c0e80e81e5a030707030381c1c1c1c1c1c1c1c1c0c0c0c1c3ea81c1e956a81c5c1c1c1c9c1c1c1e81c5ea0000000000001c270000000070707070707070713131313515555030707030707030307070313038f40c1c0c1d541c1c1c1c1c1c0c0d555070707075550707070000000000000781c1c1c1c1c1c0c0d5541c1c1c1c1e07070781c3c1c1c1c1c2c2c2c2d55554542d5555550780c1c1c0c1c1c0c030703070307550000000000000050750b5550b0b070707074bd550f070707070b0b0b0b55550763d42d55540d5507030707030707030b038f0303070703070307555075555507270707070707070707030303070f0707072f070755550707070000000000000000000b81e81e1faa6466665070707071f682c0c0c0e87c3ea87c3e95680c1c0c1e0300c0e03a0796aa03030707000000000000000b81e81e1faa581d0763d9999582e0b82e0b83e178be0f81c1c0c1c7c0c7c1e80e3c0c0e80e81e5a03071707270317030381c1c7c1c7c1c7c1c7c0c0c0c7c3ea81c3e956a85c5c1c5c1c9c5c5c7e81c5ea000000000000000000 26 67108863 11 2047
def hc_78_12 : Nat → Nat := unpackHintV5 0x868c77a0452bc7d58779efe0b07860731dbc0b871a8a91c1a0a06cd0731ac00e86578b118b714e5e9489172210654610513e027046e91310a72263b1cf00e520ea3390b70c6d0ee2c38af89f52322084ea07381d2173cb4849227a0b04e8816a2ae0280650000140 0x4dd55275070701135542c4c2c4c2c1c1c1c1d2f5543c9d0d0c9c1c1c1c1c2c4c4c2d5555541d8f5135555035540c0c0030300c0c0c0c0c0c0c0c0d544c00b0b0b0b0b0b0b0b274747271f13131f0b0b0b0b45d1744c4d131742d8f50b0b45d1717271717174717171723130713071717545c3c5c5c5cbc5c3c2c2c2c0c0030300c0c0c0c0c0c0c0c0c0d40c0c0c0c0c0c0c0c0c4c0550d527541d5230b0b0b0b0b0b0b0b50b274343271f13131f4bd550f0b0b0b0b555135555542d8f5503000c0c0340d55030303030303030303551f431f271f07071f1f0b50b0f0b0b0f0b5550303030327009c2d0c2c8c2d0c2c3c3c3c3c3c3c3c3c2c3c3c2d27550d523541d50b5550f55555550f63d55503000c0c030303030303030303540d035551f471f271f07071f170b42d0b0b1f43d0b170b0303030327009c2d1c2c8c2cdc2c9c3cbc3c8c3cbc3c2c3cbc2d1745d1745d1742d0f63d43c3c5c9c5c5c5d1c5c5c5c8c5c1c5c1c5c5c2c2c5c5c5c2c2d50f0f0f03000c0c0303030303030303030350303030303030303030b1f271f431f1f07071f50b170b0b5550303030327009c2d0c2c8c2d0c2d543549d507548d5542c9c3cbc3c8c3cbc3c2c3cbc2d45d55555555543d8f03000c0c030303030340d550303030303551f471f271f07071f0b1f0b1f0f0b0b42d0f0b45d0b170b03030303030327009c2d1c2c8c2cdc2c3c3c3c3c3c3c3c3c2c3c3c2d1745d1745d1742d43c3d0f63c3c9c3c9c3c3c3d1c3d1c3c3c3c8c3c1c3c1c3c3c2c2c3c3c3c2c2d50f170f03000c0c03030303030303030303503030303030303030327009c2d1c2c8c2c2c9d1d1c9c8c8c2c2c9d1d1c9c8c8c2c2c0c0030300c0c0c0c0c0c0c0c0c0c0c0c0c0c0ccc0c0c0c0c0c0c2c8c2c2c0cbc0c0c0c0c0c3c8c8c2c2c0d03030340c5c8c8c2c2c0c0c0c0c0c0c0c0c8c0e3c0c0c0c0c0c0c0c0c0c0c0c0c0c030000000000000002aaaa8aaa07a80eaaaaaaaaaaaaaa6a680c4c0caaaa80eaa07aa000000000000000b0b0b0b0f0f0f0f130f0b0b0b8f0b0f0b0b0f1f0f070f070f0f0b0b0f0b0b0b1f13131f0b0b0b0b0f0f0f0f0f43c5c3d0f0f0303131f031f038f030b030b030f030f03030f0703030f07031303130303030b82c2c2c2c2e0f0f0f0f0f83e1f2f0f0f0f0f0f0f0f81c8c3e1f0f0f070f1f84d1f44e13331f0000000000000000007c01f0313071380c0c2c2c2c2c2c2c2e0b0b0b87c3c4c3c2e0f070b82c2c2c2c0b1f13131f1f47e1f47e0b0b0b0b0f2f2f0f03130300c0c4c1c0e1307030b030b0313030f03130313000000000000001f1f130713071f1f0b0b0b0b0b0f0b1f0f1313130f0b0b0b0b0b0b0f0b0b0b8f1f13131f1f47c5c7d1f170b0b0b0b0f2f2f0f0303131f031f038f031f030313070303131f0727030b030b0313030f031303130303031f1f1f1381c8c7e1f2f131f07230b82c2c2c2c2c2c7c2e0f0f1f0f1387e1f2f0f0f1f84d1f44e13331f0000000000000000007c00b0b0b0b1f13131f0b0b0b0b44d175142d1745c0c0c4e130717030b82d50b87c3c7e1f87c3c2e550b80c4c0c030b030b03130313035130384c1c0c0c4c1c000000000000002c2c2c2c7c4c4c7c2c2c2c2d131344c5d0b63d42c2d1745c5c7c4c1c4c1c5c5d5170f1717172f170f0b0b0b0303131f031f038f030b030b031303130351303031307030313070303030b82c2c2c2c2e1f0f1387e130f1785c5d547d1385e17171317072317171f1381c5c4ccc7c000000000000000001f01556aaaaaaaaaaaaaa955555545540c4c0c555aaaaa5500000000000000541d51f0b0b0b0b50b1f13131f4bd550f0b0b0b0b5135555542d8f550303131f031f038f40d5507030b030b031303135503030351f5555507230b82c2c2c2c2c2c7c2e1f0f1387e130f51f17555513331f0000000000000000007c0aaaaaaa555aaaaaaaa555519555550323032aaa9695554000000000000008c2c8c2c3c3c3c3c2c3c3c2d1f541d50b547d50f555550f63d555030323230323038f0327030b030f030f541d035550303030b88c8c8c2e0f0f0f0f0f83e232f0f0f55507235235555552333230000000000000000008c0230b230b1b0f1b0f0b0f1b0b45d1745d0b5143c0c0c5e170717030b86c7c6c6c2e0f0f1b543c1c3e551780c8c0c0327030b031b030f035170386c1c0c0c5c1c000000000000008c2c8c2c8c3c8c3c2c3cbc2d1745d1742d0f63d43c3c5c7c5c1c5c1c5c5c2c2c5c5c5c7c2c2d50f0f0f030323230323038f0327030b0327030f0351703031707030317070303030b88c8c8c2e0f0f2388e0f0f1785c5d548d1785e1717171707231717231781c5c8ccc8c0000000000000000023008c2c8c2d5540c0c2e431f431f0b88c3c8c3c2c3cbc2c5e0f072383c3d55555555440c8c8c0c8c0327030b55527070327030f5500000000000000230b230b541d51f547d50b230f230f0b0f2f0b517555555550f63c0c0c8c8c0c8c0e3c0c9c0c2d035541c0c9c0c3d540c0c0c2e2323230b948d555541c8c3c3c8c3c8e2388cbc3c3d48c5d55548ccc8c0000000000000000023008c2c8c2c3c3c3c3c2c3c3c2d1745d1742d43c3d0f63c03030f83c1c3c0c2e371f371f0b943e0f83d179545e030323230323038f00c9c0c2c0c3c0c3c0d45c0e270703030f07000000000000dc27000230b230b0f0f0f0f0b0f0f0b45d1745d0b50f0f43d8f0f1f0f070f070f0f0b0b0f0f0f1f0b0b543c5c3c0c0c8c8c0c8c0e3c0c9c0c2c0c3c0c3c0d45c0c0c3c1c0c0c3c1c0c0c0c2e2323230b83c3c3e0f83c3c5e551783e0f0f0f0f07230f0f230f81c3c8ccc8c000000000000f09c00000023007c7c4c4c7c7c0c2c2c2c3c3c4c1c7c4c3c4c3c7c3c4c4c4c3c2c2c2c4c4c3c3c7c3c4c3e3c7c4c4c7c7d1f1f47c4c7c7c4c3cbcbc3c0c4c7c0c7c031f130703131f078f0313030b0313030f031303130000000000005547c0c2c2c2d55513171f13131f4bd544c7c7c4d44d5555544d8f5503131f031f155070313030b031303135500000000000003a03230b230b83e0f0b0f1f41d136547d950b42d0b47d0f55543d8f55232389e0b270b41c0d0000 26 67108863 11 2047
def hc_78_13 : Nat → Nat := unpackHintV5 0xeaf84173a03bb84231daca2aecfe0ce63748fb0183456333b2aca89e55d010aa6c0f951b036a8700d54280229ca0954051c09980d54764aba1ca3d0fc623e74413e364c7a9a62188c6919058396223fd040f045f45fd30a23c1850bccc282dc6140002dc 0x89c0e3ba3d076647c1d1768f03338f4316956aaaaaaaaaaaaa9555555545540c0c03a555aaaa5500000000000000031f03a03030303a031f4b1f07071f030b1f80c0e960383c2c3c2c2c3c2d555540c0c0c0c7c0e3c0c0c0c0c2c0c0c00000000c0ccc0c0e03030388c2c2c0e03030380c3c3c3c3c3c2c3c3c2d035550340d5523541d50b5550f555550345d55550f63d555030303030303030323038f030303030303030303540d0355500c000000000000000000089c2e0b37030383e0f0f0b66170b0f63d0f1f0707171f171b13a13171317a0b0b0b0b0b171f0b50f0f0380e03030303030300001786c1c5c1c5c5c8c2cdc2c6c6c2e1b1f0b86c3c6c3d40c0c0d03030b0f1b0b45d17503943e45d0b43c43c3c0c0c0303030380c0c0c0c0c0c0c0c0c0c0c0c0d40c000000000000000c7c0c6c6c0e80c0c0c0e87c1c1c7c0c2c7e0303a170b80e0f42d0b0b1f6643d0b170b030303031f038f030303030b0303000000030333030380c0c0e230b370b03038bc0c0c0e03030f0f230f2f0f0b0f2f0b503940e45d1745d0b43d8f50f0f030317030380c0c0c0c0c0c0e1717231707170717170b0b1717170b0b543c3c3c0c0c0c0c0c0c0c0c8c0e3c0c0c0c0c0c0c0c0c0c0d40c0c0c0c0c0c0c0c0c0300000000000000000002270b82cec0c0d0747d51344d51f47d0b47d0b42e0f83c3c2d17555550f63c0e0380c0c0d40c0000ee5380e63c0c1d0c89c0e3ba3d07503563c0cce3c0c1d0c8f81c1e63c0ccc2c7e8f8f4bc0e1f0b40e3c0d4308c2c2c8c3cbc3c2c3cbc2d4cc1d542e1f1f0b80c0c5e0380c0d55555443d8f5555030300c0c0c0c0c0c0c0c0c0c0d55554000000000000000c7c0c2c7e0303a80e0f0b1f03a03030303a031f1f1f07071f50b170b0b55555030303031f038f0b0303030303031f030703000000030333030380c0c0e230b0b5540d035540d541d5235550b0380c0c0e030f230f2f0f0b0f2f0b5175555555555550f63c0c0c0c0c0c0c0c0c8c0e3c0c0c0c0c0d40c0d5540ccc0c0c0c0d540300000000000000000002270b82cdc0c0e0f83c3c2d985c2d0f0f63c7c3c7c1c1c3c4c3c7c3c7c3e84c3c4c3e82c2c3c3c2c2c2c2d45c3c0e0380c0c0c3c0c4c0c0c0c0c00003c03e33070f070f0f230b370b371f0b8dc7c2e0f0f0f0f0380d03942c3c3c2d1745d40e51791742d0f4030300c0c0c0e0303030303030303030303030303503000dc270000000000000380c0c0c0c1c0c3c1c1c1c1c0c4c0c0c0c0c1d0707030303030303030f8f0b0f0f0b41d0740c0e40c0e8f44d0b43d00c0c0c0c0c0c1c0e3c0c0c0c0c0c1c0c0c0c0c0c0c0c0d40c000300000000000031f031f1f03a03030303a1f07071f0b03a03030382c7c3c2e0383c2d0b43c2d991742c5c2c0c0c0c0c7c0e3c0c7c0c1c0c0c0c0c0c2c0c0c0c0c000002270b82cdc0c0e0f83c3c2d985c2c9c9c9c9c9c2c0e0380c0c8c2cdc2c3c3c3c3c2c3c3c2d1745d1742d0f4232727230b3f3f0b0f005c0030300c0c0c0c0c0c0c0c0c0d40c0c0c9c0c0c0c0c0c9c0c0e03030388c2cdc2c0e03030380c3c3c3c3c3c2c3c3c2d40e50391745d1742d0f40303272703030303030327232727230b27270b4017000c0c0c0c0c0c0c0c8c0e3c0c0c9c0c0c0c0c0c0c0c0d40c0c0c9c0c0c0c0c0ccc0c0e03030388c2cdc2c0c0e2f03030380c0c3c3c3c3c3c3c2c3c3c2d03503940c0e1745d1745d0b50f0f43d8f03030f030380c0c0c0c0c0c0e0f0f230f230f070f070f0f0f0b0b0f0f0f0b0b543c5c3c0c0c0c0c0c0c0c0c8c0e3c0c0c0c0c0c0c0c0c0c0d40c0c0c0c3c0ccc0c0c0c0c0c0c0300000000000000000f000001d1c1c1c1c1c1c9c1c1c1c1c007070b0b0b0b0b0707070707070b8f072f07070707070f27474727070707070b0b0b0b0741c1c1d071727374327070707070b0b0b0b43374337030303030303030303000c0c0303030303030303030303030307004c2c4c2c1c1c1c1c3c3c3c3c1c1c3e3c1c1c1c1c2c3c3c3c4c2c1c9c1c1c1d1c1c1c1c1c1c1c2c1c1c1c4c1c1c1c3c1c9cdd0c9c1c1c1c1c2c4c4c2c3c3c3c3c1d07170741c1c0c0030300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c1d1c1c1c1c1c1c9c1c1c1c1c0071307070707070b130b130b07070707070723270f2f0f0707070707070f8f0b0f1313130b0741c1c1d071727374327070707070b13130b0f2f2f0f030303030303030303000c0c0303030303030303030303030313002c2c2c2c2c2c2c2c3c3c3c3c3c3c3c3c4c3c2c2c2e3c2c3c2c2c3c9c3c3c3d1c3c3c3c8c3c1c3c1c3c3c2c2c3c2c2c2c9d1d1c9c7c4c4c7c2c2c2c2c3c3c3c3c3d0f170f43c3c0c0030300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c4c01f272f471f2f27271f23130713071f230b0b0b0b0b0b0b0b0b0f0b270f2f0f1f0f1313130f0b0b0b0b0b0b0f0b0b0b8f274747271f13131f2f47c5c7d2f170b0b0b0b0f2f2f0f03000c0c03030303030303030303030303030303030303030307004c2c4c2c1c1c1c1c9d0d0c9c1c1c1c1c2c4c4c2d1745d0763d41c1d131344c2d1745c1c9c1c9c1c1c1d0c1d1c1c1d5070b070707130707070f0707072f070707170703000c0c030303030303030303035030303030303030303 25 33554431 11 2047
def hc_78_14 : Nat → Nat := unpackHintV5 0xf3508a748ca3b82e431ad028ec4724259392028288e92d727a92688a40f508206e01903300881680640a402200409cffe0087fb0083fb4049f8c09ce702ac6362042ec05e14a058085c3e8363196169c8f88fc4a42953d210a08102c8b10034260000034 0x80c0e0b37270b41d1f547d1f544d1342d0b83e0f45d55543d8f88e0b270b0350700000b0b0b0303030b0b0b0b0b0b3b0b0b270b1f13131f132f1f0f1f2f130f0b0b0b0b1f13131f1347c5c7d13170b0b0b0b37370300c4c0c0c4c8c0c0c2c2c0c2c9c0c2c2c0c4c0c4c0c4c0c4c000000000000008c2c2c8c8c2c2c8c8c2c2c0c8c0e3c0c0c8c8c0c9ccc0c2c0c9c0c9c0c9c0c9c0c0c0c2c2c9ccccc2c2ccc3c9cbcccbc9c3ccc5c9d3349c5c8c8c8c0000000000000002c2c4c9c2c2c2c2c2c2c2c2cec2c0c0c0c7c4c4c7c7cbc4c3c4cbc7c3c2c2c2c2c2c7c4c4c7c7d13171347c5c2c2c2c2c2c0c0c0303030303030303030303030303030303030303030303000000000000000303030303070327030303030307030b07070703030707070b03030b3b0303030303030b0b0707070707070b8f072f07070707070f032f03030303030f0723070707070b0b0b0b0741c1c1d07170340c0c0d03170723070707070b0b0b0b3737030303030303030303070333030303030303030307038f0303070303030303030303030303000000c0000000000000000030307031303030303030b0707070703030f2f0303030303030f0f07070f8f070707070b0f0f0f130b0303072f03030303030303030303070f070707070b070707130707070f070340c0c0d0317070707070b13130b0f0f0f0f0741c5c1d0707030303030303030307038f030307030303030303030303030703330303030303030303030300c0000000000000000000030303030380c9c0e03030307030f070707030307071307070707070b03130380c0c0e07130707070707072303038bc0c0c0e03030f0f0707070707070f8f0b0f1313130b0741c1c1d07170340e0340e0723070707070b13130b0f2f2f0f03030303030303030307033303030303030303030703230303070303030303030303030303000000c00000000000000000b130b0b0f0f0f0f130f0f83c3c3c4e8f030f0f070f070f0f80c0c0c0e03030b0b0b1f13131f1f13131f0f0f0f0f0f0f170f0f0f030300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0000000000020fa81eaaaaaaa83eaaaaaa2aaa9a9aaaaa030300ea0380eaaaaaaa8000000000000000c0ccc0c0c2c0e0303030382c2c2c2c2c0e03030380c3c3c3c3c3c4c3c2c2c2e3c2c3c2c2c0c0e03030303030380c0c0c3c3c3c8c3c1c3c1c3c3c2c2c3c2c2c2c0d0380d0387c4c4c7c2c2c2c2c3c3c3c3c3d0f170f43c3c0c0c0c0c0c0c0c0c7c0e3c0c0c2c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c03000000000000000000028f63e3e63c4c7c7c0e8f2f0340c4c8f8f438f90e3e1f130b0f43c2c4c0c0b0b0b0b1f84c1c4c1c7c7c0e0b0b03030387c3c4c4c4c3c2c2c2c3c0b0b0b8f0b80c0c0e03031f13131f0b0b0b0b660f2f2f0f03030300c7c0c0c2c0c0c0c0c0c0e03030303030303030303030300000000000000003033303038bc0c0c0c0c0c0e0303032f1f23130713071f23030b0380c0c0e0b0b0b0b0b0f0b0380c0c0e030f1f0f1313130f0b0b0b0b0b0b0f0b0b0b8f0340e0340e1f13131f2f47c5c7d2f170b0b0b0b0f2f2f0f03030303030303031f038f030303030303030303030b030303030303030303030300c000000000000000000007070707070707070b13130b441d1342d1745c0c0c0303030303030303030350300702c4c4c2cfcfcfcfc5c003070003030703130380c0c0e070707070380c0c0e030f070707070b13130b503940e441d1342d1745c0c0c9c9c0c0d40c0c9c102c4c4c2c9c9c9c9c5c0030303030303030307038f030307030303030303030350303030703030303030703130380c0c0e070707070380c0c0e030f070707070b13130b40d40e5030385d0763d41c1d131344c2d1745c0c0d40c0e0355030385d5070b070707130707070f0707072f0707071707030303030303030307038f030307030303030303030350303030307033303030303030300c000000000000000001c00005030355555031750703030744d550b031303030303030b0713070707074bd550f032f03030303030f0723070707070b13130b5555550345d550748d44d555503035550333030303030303030307038f0303070303030303030355000000c0000000000000000b130b0b1f13131f1f13131f44c4d13175131344d8f0345d17171307130717503030303503170f1717170f0b0b0b030300c0c0c0c0c0c0c0c0c0d40c0c0c0c0c0c0c0000000000005e1307130717170b0b0b0b50380d0387c4c4c7cde370f378dc3c2c2c2c2d131344c5d40e50b90b10b0b45d17030300c0c0c0e0303030303030b03030303030303035030000000000000003033303030b0380c0c0c0e0b0b0b0b0b0380c0c0e030f1f13131f0b0b0b0b503940e44c4d131742d8f50b0b45d17030317030380c0c0c0c0c0c0e171723130713071717545c3c5c5c5cbc5c3c2c2c2c0c0c0c0c0c0c0c0c7c0e3c0c0c2c0c0c0c0c0c0c0c0d40c0c0c0c0c0c0c0c0c0300000000000000000002a96956aaaaaaaaaaa965554663d5555540c0c03aaaa555aa55000000000000000303335540d035540d541d523030b0380c0c0e0b0b0b0b50b0380c0c0e030f1f13131f4bd550f0b0b0b0b55555135555542d8f5503030303030303031f038f40d550303030b030303030303035500c000000000000000000089c2e0b3b030383e0f0f0b1f41d1f6544d950b42d0b47d0f55543d8f550380e030340c0d000094c0e3b9a3d0c 25 33554431 11 2047
def hc_78_15 : Nat → Nat := unpackHintV5 0x8f04e9a2a723481f5151e434747085111b99110666cff18492a4592cff145b3e04b6cc011ba2423f8ceb8f6a0f23838ae0e0001c3738190d1a16832943a8b5e28e2a805f098922e1ef8e587a802c1db41d86ab18417287084792a20e287782692420210f28000108 0x32303230b230b03030380c0e0f0f0f0f0380c3c0e03030b0f0f0b45d17503940e45d0b50f0f43d8f0f1f0f230f070f070f0f0f03030303030383c0c0c3c0c0e030b0b0f0f0f1f0b0b543c5c3c0c8c0e3c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d40c0c0c0c0c0c0c0c0c0000000000000000f00000c8c0c8c2c8c2c0c0c0c2c0c0c0c8c8c8c8c0c0c0c3c0cbc0c0c2c2c8c8c8c8c0d03170340c0c2c2c0c8c0e3c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c000000000000001c1c1c1c1c2c1c1c1c1c1c1c2e3c1cbc1c1c1c1c1c3c1c1c1c1c2c2c2c2c1d07070741c5c1c1c1c1c2c2c2c2cdcdc0c1c0c0c1c1c0c0c1c1c1c9c0c1c0e3c0c0c1c1c0c1c1c0c2c1c0c1c0c1c0c1c0c1c1c1c0c0c1c1c1c2c0c0c0c0c1c1c1c2c0c0c0c1c2c1c2c1c1c1c2c1cec1c1c1c3c1c1c1cbc1c1c1c5c1d0741c1c1c1c1c00000000000000000001c1c1c1c1c1c3e3c1c1c1c1c2c3c3c3c4c2c1c1c1c1c2c1c1c1c4c1c1c1c3c1c1c1c1c1c2c4c4c2c3c3c3c3c1d07170741c1c0c1c0e3c0c0c1c1c0c1c1c0c4c1c0c1c0c1c0c0c1c1c1c9c0c1c0c0c1c1c0c1c0c1c0c0c0c1c2c1c1c1c4c1c1c1c3c1c3c1c1c1c3c1cbc1c1c0c0c0c0c1c1c1c9c1c1c0c0c1c1c1c3c1c5c1d0741c1c1c1c1c00000000000000000001c1c1c1c4c1c1c1c1c1c2c1c1c1c1c1c1c8c1c1c1c1c1c1c3e3c2c3c4c4c4c2c1d07070741c5c1c1c1c1c2c4c4c2c3cbcbc3c0c1c0c0c1c1c0c0c1c1c1c9c0c1c0e3c0c0c1c1c0c1c1c0c4c1c0c1c0c1c0c1c0c1c1c1c0c0c1e07270380c0c1c1c1c3c0c0c0c1e070707130781c3c1c3c1e0781cbc1c1c1e0741d0781c1c1c0000000000000000002aa83ea8aa80ea0faaaaaaaaaaaaaa9a9a0300c4eaaaaa03aa81ea8000000000000002c2c2c2c3c3c3c3c4c3c2c2c2e3c2c3c2c2c3c8c3c1c3c1c3c3c2c2c3c2c2c2c7c4c4c7c2c2c2c2c3c3c3c3c3d0f170f43c3c0c7c0e3c0c0c4c7c0c2c2c0c2c2c0c3c0c3c0c0c3c1c0c0c3c1c0c4c0c4c0c0c0c2e0b0b0b0b0b83c3c3e0f83c3c3c3c3c3c3e07270f8cc3c3c1c3cce134cd1384c7c7c00000000000000000007e030313031f1f0b0b0b0b0b0b0b82c2c2e1f0f1313130f0b83c1c2e0b0b0b0b02c7c4c4c7cdd378dd3782c2c2c2c3cbcbc3c0c7c03131f030313070384c1c0c2c2c0c2c2c0c4c0c3c0c4c0c4c0000000000000007c8c4c1c4c1c7c8c2c2c2c2c2c3c2c7c3c4c4c4c3c2c2c2c2c2c2c3c2c2c2e3c7c4c4c7cbd1f171f4bc5c2c2c2c2c3cbcbc3c0c7c0e3c0c0c4c7c0c0c4c1c0c0c4c1c0c2c2c0c2c2c0c4c0c3c0c4c0c4c0c0c0cbcbccc4e07271f8bcbc4cbc1c9c2e0b0b0b0b0b83c3c4e2f83c3cce134cd1384c7c7c00000000000000000001c1c1c1c1c1c1c1c2c4c4c2d0763d41c1d131344c2d1745d5070b070707130707070f0707072f07070717070307038f0303070703070703130703070307035070303070707270307030307070303030781c1c1c4c1e070f0781e07070781c5d541d0780e0303550740d0781c5c1c1c1c000000000000709c0000000141d135542c1c1c1c1d2f5543c1c1c1c1c2c4c4c2d55541d8f513555540c0d5541c9c0c1c0e3c0c0c1c1c0c1c1c0c4c1c0c1c0c1d5540c0d555541c5c0c0c0c1c2c1c1c1c4c1c1c1c3c1c1c1cbc1c1d41c5d55541c1c1c00000000000000000002c2c2c2c7c4c4c7c2c2c2c2d131344c5d10b45d171717130303031782e0b542e370f378de370f0b9542e0300c4c0c2c2c0c2c2c0c4c0c4c0d44c0e130703031307000000000000000b0b0b0b1f13131f0b0b0b0b44c4d131742d8f50b0b45d171723130713071717545c3c5c5c5cbc5c3c2c2c2c0c7c0e3c0c0c4c7c0c2c2c0c2c2c0c4c0c4c0d44c0c0c4c1c0c0c4c1c0c0c0c2e0b0b0b0b0b8cc3c4e3384c3c5e551385e1717131707271717331381c5c4c7c7c00000000000000000016956aaaaaaaaaaaaa9655555545540c0313555aaaaaa5500000000000000541d5230b0b0b0b50b1f13131f4bd550f0b0b0b0b5135555542d8f55031f038f0303131f40d5507030b0b030b0b03130313550303035335555507270b82c2c2c2c2e330f138ce130f5555131f1f00000000000000000008f81cde8f41d45e3c0c9e3e0b03a37691f07071f50b0f0b0b0f0b5551f038f031f030703070b0b03031f333781e87e1f070782c2e0fa0f551f1f000000aaaaaa55a5aaaaaaaa55551555550300c8eaaa9695554000000000000008c2c2c3c3c3c3c2c3c3c2d23541d50b5550f555550f63d5550323038f03032323032733030b030f030f541d035550303030b89ccccc2e0f0f0f83e0f0f555072753355555523232300000000000000000001f07071f170b42d0b0b1f43d0b170b1f038f031f030703070b0b03038ce1b07071b1f1b81e82c2e0fa0f961f1f00000230b370b1b0f1b0f0b0f1b0b45d1745d0b443c5c5c5c0c0c0c5e0b86c7c6c6c2e0f0f1b543c1c3e551780c03230327030b031b030f035170386c1c0c0c5c1c000000000000008c2cdc2c8c3cbc3c2c3cbc2d1745d1742d0f63d43c3c5c8c5c1c5c1c5c5c2c2c5c5c5c2c2d50f0f0f0323038f0303232303273303370b0327030f0351703031707030317070303030b89cccccdc2e0f0f278be0f0f179545e1785c5c5c5c1c9c5c5ccc5e071723232300000000000000000008f030781cde8f41d8f03278f030782c0e8dcdd41c2c7c7c1c1c7d42c5c2c2d5547c0e3c0c7c2c2c7c0c0c1c0c7c1c1c0c0e0b0b83e83c7c7c7e07a3387c1c1d547c7c000008c2cdc2d40c0d542e371f371f0b88c3cbc3c2c3cbc2c5e0f072f83c3d55555555440c03230327030b55523070327030f5500000000000000230b0b541d5235550b230f2f0f0b0f2f0b517555555550f63c0c8c0e3c0c0c8c8c0c9ccc0c2d40c0d5541c9c0c9c0c3d540c0c0c2e2733330b94cd555541c9c3c3c9e2f83c3d55548c8c8c00000000000000000007c1c1c7c2c7c3c2c2d0b43c2d1742c5c2c7c0e3c0c7c0c7c1c1c7c0c0c1c0c2c2c0c7c0c0e3387c1c1c7c7c7e07a0b82c2c7c7e0fa0f961f1f00000230b370b0f0f0f0f0b0f0f0b45d1745d0b43d03c3c3c0c0c0c3e0b8dc7cdc7c2e50f83e0f45e551780c0c03032303273303370b030f030f035170388c1c0c0c3c1c000000000000008c2cdc2c3c3c3c3c2c3c3c2d1745d1742d43c3d0f63c3c8c3c1c3c1c3c3c2c2c3c3c3c2c2d50f170f0323038f0303232303273303370b030f030f0351703030f0f0727030f03030f070303030b89cccccdc2e0f0f0f83e0f0f179545e0f83c3c3c3c1c9c3c3ccc3e070f2323230000000000003c270000000080c0e0b37270b83e0f1f41d136547d950b42d0f5543d8f5588e0b270b41c0d0000 26 67108863 11 2047
def hc_78_16 : Nat → Nat := unpackHintV5 0x8100799f4020077d4a59d2619e6f54a89b8b0946a387e99ee14063cc7d97ac28e5cac4095274084fbc9c11db4284328888ef03b439ec3a8d1f2b8324c460c1e0ea2b54a48a1f16c24208b87473821ad44905cc1d2120ca483a71b80ac47b0198232051829000028c 0x2a82e8f0b23a0b230b83e0fa0f0fa0f0faa665a5a6664232323232323232b2327232382c2e408023232323230323272303232382c2e0fa0f9627272727a82c8c2c2c8ea0ba3e83c3e83c3e0f83ea95b5a585e1766666427273b3f27275b3f232b272382c2e408037032727370327272327372382c2e0fa0f9627272727230b2b0b0f0f0f0f0b0f0f0b45d1745d0b43d08c8c9e3c9c9c8c8c2c9cfc9c9c2d005c02727270b8acfcacac2e0f0f0001780008c8c8c8c9c9c8c2c9c9c2c3c3c3c3c5d45c9c9c9c9c9c9c9c0c9c9c9c0c9c9c8c2c8c2c3c3c3c3c2c3c3c2d1745d1742d0f4232323232302c9c9c2d005c0003030303030303030303030303503030303030303230b230b0f0f0f0f0b0f0f0b45d1745d0b43d08c8c8c8c8c8c9e3c2c9c9c2d005c002323230b88c8c8d6c2e0f0f0001780008c9c8c8c8c8c8c2c9c9c2c3c3c3c3c5d45c9c9c9c9c9c9c8c0c8c8c9c9c8c8c0c8c8cecac2e0b82c2e0f83d988e0b89c9c0c9c0c9c2e0ba0f83ea99999909c9cfc9c9c9e82e3c2c9e9002000ac8cfcfcfcac8c2c2c9c3c3c0028002a2727272782c2e0fa0f9627272727272727032727270327270b0b0f0f0f0f0b0f0f0b45d1745d0b43d09c9c2c9c2d005c027270b270b0f0f0f0f17517272727270b0b0f0f0f0f0b0f0f0b45d1745d0b50f0f43d8f0f230f0f0f0f0f0b0b0f0f0f0b0b543c5c3c2c2c3c3c3c3c5d45c3c0c3ccc3c0c3c3c000000000000f00001c2c1c8c1c2c1c2c0c0c0c2c8c1c1c2c2d3cbc1c3c1cbd3c3c7c1c1c7c2c2c2c2d3d07170753c5c7c1c1c7c2c2c2c2c0c0c0c0c0c0c0c0c032303030303030303030303030303030303030000000000000081eaa07aaaaaaaaaaaa8a9a9aaaaaaa80eaa0300c0c0eaaaaa8000000000000000c7c0c2c2c2c2c0c0c0e030b0383c3c3c3c4c3c0e03030f0f03038bc0c0c2c2c2e3c2c3c2c2c3c7c3c1c3c1c3c3c0c0e0303030f0f030380c0c0c0c2c2c3c2c2c2c7c4c4c7c0d0380d0382c2c2c2c3c3c3c3c3d0f170f43c3c0c7c0e3c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0000000000000000001c1c1c1c1c1c1c1c1e07070381c1c0c0c0e070707070b0b02c1e03030380c0c1c1c1c1c2c2c2c2c1d0781d0783cbcbc3c0303030303030303030380c0c0c0c0c0c0c0c0c0c0c0c000000000000000c7c0c7c7c4c1c4c1c7c7c0c0e0303031f03038bc0c0c0c0c2c2c2c2c0c0c0e030b0382c3c2c7c3c4c4c4c3c0e03030f0f03038bc0c0c2c2c2c2c2c2c3c2c2c2e3c7c4c4c7c0d0380d0387d1f171f47c5c2c2c2c2c3cbcbc3c0c7c0e3c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c7c0ccc0c0c0c0c0c0c0c0c0c0c0c0c0000000000000000001e0707070707070340e50381c1c1c1c1e07070781c3c1c1c1c1c2c2c2c2d41e50390741d10b45d1703030303030303803030303030303030303030350300000000000000031f030b0b0b0b03030380c2c0e1f13131f0380c3c0e03030b0b0b0b44c4d13175030385d0350390b63d42c2d1745c5c7c4c1c4c1c5c5c0c0c0c0c0c0e17030317030380d5170f1717172f170f0b0b0b031f038f030303030303030303030303030303035030303030303030303000000000000000000aa555aaaaaaaaaaaaa555155555500c0c0eaa9556a954000000000000000c7c0d507547d55035550340c2c2c2c2c0c0c0e030b03942c7c4c4c7c0e030f0380c0d2f5543c2c2c2c2d44d5540d1755555550b63d540c7c0e3c0c0c0c0c0c0c0d035540c0c0c0c0c0c0c0c0d540000000000000000022382c0c0c8c2e0f83d3d95076547d0742d0b43d550f63d540e0388c0c0c0d0303400016956aaaaaaaaaaaaa955555554555694030303aaaa5500000000000000032303230b230b03030380c0e0f0f0f0f0380c3c0e03030b0f0f0b47d507540d035540d5542d51f543d5555555543d8f55540c8c0e3c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d50340d5540000000000000000022382c0c0c8c2e0f83d983d8f43d3c5c6c1e81c5c1c5e87c1c1c5c2c2c2c2d43c3c0e0388c0c0c0c0c0c0c0c00001e07070707070707130781c1c1e070707070340c0d40c0c1c1c1c1c2c3c4c2d41e50390741d1342d10f03030303030303803030303030303030303030350300000000000000032303230b230b03030380c0e230f230f0380c3c0e03030b0f2f0b45d17503940e45d0b43d8f50f0f171f17071707171703030303030385c0c0c5c0c0e030b0b1717171f0b0b543c3c3c0c8c0e3c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d40c0c0c0c0c0c0c0c0c0000000000000000022382c0c0c8c2d50741d54f53d0747d0b42e0f83d1755550f63c0e0388c0c0c0c0d40c00001c1c1c1c1c1c1c1c2c3c4c2d5541c1c1e070707130780c0c1e0380c0d55554555540307030303030303030303030303035555500000000000000032303230b230b03030380c0e541d51f5540d5540d03547d50b230f230f0380c3c0e03030b0f2f0b5175555555555550f63c0c8c0e3c0c0c0c0c0c0c0c0c0c0c0d035540c0c0c0c0d540000000000000000022382c0c0c8c2e0f83d990f0f63d3c3d3c1e81c3c1c3e87c3c7c1c1c3c1c3c2c2c2c2c2c3c7c2d45c3c0e0388c0c0c0c0c0c0c0c00003c00c1c0c1c1c1c1c0c0c0c0c1c0c1d07070303070303030b0f0f0b41d0740e40e44d0b43d00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d40c0000000000001e07070707070707130781c1c1e0707070703940e0341c1c1c1c2c3c3c2d41e50390741d1342d0f403030303030303803070303030303030303030303035030000000000000088e0b0303230b83e0f66272727270380e23030303032303230b230b03030380c0e0f0f0f0f0380c3c0e03030b0f0f0b45d17503940e45d0b43d08c8c8c8c0c0c0c9c0c9c0c0c2c9c9c2d005c00323038f0303030303030303030303030303030350303030303 26 67108863 11 2047
def hc_78_17 : Nat → Nat := unpackHintV5 0x8bb8008bb8008ac83c85994c85201e83c05882f03482981681205e78f20c72c18c6a9a0a66a8fc60e1725bd9425599904a5ad045a12e4189064128183b49783ab82439a8443790862beaea2549a820394419c19e10a2480cb0fc06699200019a 0x1c8e88c3e03910c2e8a83e0faa5a5550b0b550f07aa0f0f55555443d55548c8e0b0b83e83c0c1c0c1d54000000000000010750703278f41d41d038f3b0303078f07030f80d598f540e3d0763c9cec0c1c0d41c3e9a82c8c2c2c8ea0ba3d55074ed555507547d50b542e83c3e83c3e0f83ea945d5555555555543d8f033b333b0333232382c2e40d55070fa0f550000000000000000005555a981e8f0707a07070781e0fa0f0fa0f0faa555555555107070707130307071303070781c2e0fa07550000000000000013070b070b0b232f07072f0f0b0f2f0b542c2c1cec4c1c2c3c3c1c5cbc5c1c3d555554555541c1c1c1c2c1c4c1c3c1cbc1c1c0c1c9c1c0c1c9d540000000000000281d556a9aaaaaaaaa9555555554603aa81c1c1c1c1eaaa954000000000000002e0ba0f83e0ba2fa231f3b87c8d582e1782e0b555555155551f1f82c2e0fa0f1f0389e031f2755000000000000000b0b555235550b2f0f2f0f0b0f2f0b517555555550f63c2c2d03554cc3cbcbc3d5400000000000002a82c1c2c2c82c2c4e0b0ba0b07a83e0fa5a0f6a999696999904c4c4c4c4c0c4c1c4c0c4c1e0b0b83e83e5800000000000002a82e8f0b23a0b230b83e0fa0f0fa0f0faa665a5a66583d0f63c3c7c3c8e0f0f130f83c3c7c3c8e0f83c3c4c3e0f83e0b82e0b82d585c3c8c8c8c8c8c0c8ccc8c0c8c8e0b0b83e83e5a030f130f0383c0000000000000000f00026a230b2382e8f83e0f60f0781c1c3c1e43c3c1c1c3c1c2c2c2c3c7d4dcecdd4c1c1c0003c5baaaa81c2c2c2c8c2c8c2c7e0b0b82c8e0ba3e0f83e659998dcecdc0c1c0c1c00001cdc0ea82c1c2c2c2c2e82c2e82e2a0f6960f83ea96969999990dc0ddc1cdc0c1c8cdcdc8e0b0b83e83e58000000000000001c0c0e81e3d4c5e3c0e83c9cde3d4c5e3c1c1c3c7c1c2c7c9cdc0e07827a82c8c2c2c8ea0ba3e83c3e83c3e0f83ea95a585e176666583d0f63c3c3e0783c3c1c3cee0f83c3c7c3c8e070f070f83e0b0b0b82e0b0f82d585c3cdc0cecccdc0ccc8cdcdc8e0b0b83e83e5a030f070f0381c0000000000000000f0002a81c1c2c2c2e07070781c1c1e0783e83c3e83c3ea999696999901c1c1c1c4c0c1c1c4c0c1c1e07070b81c3e81e5800000000000002a0ba07a070707983e0f0f83c3ea999a6999901c1c1c1c4c0c1c4c0c1e070b83e81e58000000000002a81c1c1c1c2c1c1c2c1c1e81e07a3e070781c3e607aa41e981e8f6666640703070703070707070781c1e07a0796000000000000070f0f13070b073b0b0b1307070b0f0f5070f0f43c1c3c1c3c3c2c3c3c2d41c5d45c5d071745c5d1742d0f40703072707030727070707070b0713070f070f071750700000000000000aaa81eaaaaaaaaaaaa66665a5a6407070707aaa81e03aaa9600000000000000a87c7e83e0f83c7c7e83e1fa3e0f0f83c3e0f83e691fa61785d9999907c0c7c7c0c7c7c7c7c7e1f1f83e83e580000000000007c8e1f3b88c2e0b0ba0f0b83e0f82d60b9a0fa0b66585d60b61760b641f1f80c7c9c7c0e2782c2c2e0fa0f9600000000000000 24 16777215 10 1023
def hc_78_18 : Nat → Nat := unpackHintV5 0x82a87e82481881304680a82280700e7f504876f2187300fc6d29766761726189765c81425639924b8aac47d0ee4149a240a82840381c3eb860344a9c2de99824ca4820c9001aa18a12f9ea0d31720462340120d000e01000e00000a010000028 0xa2388ea8faa55996695698dcecde4001941c0c9e3d07665378f3b030703950f83e68f41d63c9cec0c3e69a82c8c2c2c8ea0ba3e83c3e83c3e0f83ea9555074ed551f541d50b542d50f5555545d55550f63d555033b333b0333232382c2e0fa0f541d03555000000000000000000a5556a07aaaaaaaaaa55555555150707070780eaa07aaaa55000000000000005682e3b82c4e07a0f83e0f83e070f83c3ea9555555554541c0e2780c1c9c1c1c1c1e071383e81d54000000000000001c2d0707aaa55581e07aaa070fa0707555555555150707070781c1e070307070703070707a07550000000000000088c7e3b1f230b82e560f83e0b83e0b82e83e82d555555554547c7d2c0e2780d2c9e0b0b83e83d540000000000000002c2c3c3c3c3c2c3c3c2d235550b5550f555550f63d5550b0b0f0f0f0f54cd0355500000000000000aa0b070b0b20b82c2e82c1ea0f83e43c3d43c3ea999696999184c4c4c4c4c0c4c1c4c0c4c1e0b0b83e83e5800000000000002a82e8f0b23a0b230b83e0fa0f0fa0f0faa665a5a6643d8f583c5c7e13171385c5c7c5c8e1385c5c4c5e1785e0b82e0b82d583c3c8c8c8c8c8c0c8ccc8c0c8c8e0b0b83e83e5a031713170384c000000000000000002aaa070b230b0b82e2382e8f83e0f41d0766660f0f373b37030703070000aa0b070b0b0b0ba0b0ba0b8943c1e43c3e0f83ea9696999990f183c6c0c6c1c6c0c6c1c8cdcdc8e0b0b83e83e58000000000000001c0c0e81e63c0e85e3e3c1c1c5c9cdc1c0c0e607aa0b230b0b23a82e8fa0f0fa0f0f83e0faa5a5a666643d8f583c5c5e0785c5c1c5cee1785c5c7e07170785e0b82e0b82d583c3cdc0cecccdc0ccc8cdcdc8e0b0b83e83e5a031707170381c000000000000000002a81c1c2c2c2e07070781c1c1e0783e83c3e83c3ea999696999181c1c1c1c4c0c1c1c4c0c1c1e070b83e81e58000000000000001c5c5c4c1c2c1cec2c2c4c1c1c2c6d070f50f0f232f07072f0f0b0f2f0b5070f5170f41c5d171745d0b443c1c0c1c9c1c0c1c9c1c1c1c1c2c1c4c1c3c1cbc1c5d41c00000000000002aaa07aaaaaaaaaaaaa999996969181c1c1c1eaaa0780eaaa58000000000000006c8e1b3b88c2e0ba170b83e0f982d60b82e8be66583d60b61760b461f1f80c6c9c6c0e2782c2e0fa0f96000000000000000b0b2f0f2f0f0b0f2f0b45d1745d0b43d8f50f0f172317171717170b0b1717170b0b543c3c3c2c2c3cbcbc3c5d45c5c0c5ccc5c0c5c5c00000000000000a0ba83e0faa555a50b07550f0faa0f0f55555155551313131382c2e0fa0f13031307130313075500000000000000aa0ba3c2c8e82c8c2d513547d55135551f48d50b542e0f83e83c3e83c3ea945d5555555555543d8f23232323230323332303232382c2e40d55130fa0f55000000000000000000a88c2c8e0ba3e0f83d56542d41e81d550f553b3b0307030700000703070383c1d80d0c 24 16777215 10 1023
def hc_78_19 : Nat → Nat := unpackHintV5 0xbd5126b691b0aec9f2aaa908a3b9bc9d39a0920acc8da11a86d9b280c9847572d66ef1a065b2505e49da5871765471004e29924a80ea4671043d0a5a38d90c32b9882f68d42b78fc25a9741bd27617591e12a92c0eb8fc05ea3403b08e0000ec 0x2aa87e8f6aaaaa0fa1faaaaaaa8f691f1a9aa3d99987c7c7c7e03aaaaaa960000000000000582c2c2e42c8e0b82e170b88e1f8be0f8be0f82ea61748c585d60b61760b661f23231f80c7c9c7c0e2782c2c2ea96000000000000000230b230b232323230b0b5171748d8f45d0b45d17542c2c5c5c5c2c2c5c3c5c5c5cbc5c3c5c5c5c8c8c8c8c2c2c5d45c5c0c5ccc5c0c5c5c000000000000020fa81eaaa6968aaaaaaa999696919987c7c7c7ea0780eaaaaa58000000000000020faaaaaaa1fa3eaaaaa691f96a1765a663d699a1fa87eaa23a85eaa85d5aaaaa87c7c7c7ea3380eaaaaa5aa3380e80000000000000000002e0ba20fa0b82e17171307aaa0b5683c3ea83c3d84d139199969684c4c4c4e0b0b83e83cdc0c4c1cdc0c4c1e58000000000000002e0ba1fa3e83c3e82e0baaa0b0b0b0ba0f0f0f61344e42d8f582d9969685c8e07130785d583e0f83e0f0f070f0f83e170f0f1781e0f82c2c4c4c4c4e0b0b83e83c3c0c3ccc3c0c3c3e5a031307170381c00000000000000000207aa85d6a6aaaaaaa8aaa96969a44e61a6680eaa0713131313aaaa9600000000000000a0faaaaaaaaaa1fa3eaa96969a44e663d699aaa85ea2fa85e23a81e95aaaaaa03aa8cc4c4c4c4eaaaa5aa0780e80000000000000000002e0ba0f8aaaa17071717a0b5683c1ea83c3d994599969687c7c7c7e0b0b83e83c7c0c7c1c7c0c7c1e58000000000000002e0ba83c3e1fa3eaaaa0b0b0b0ba0f0f0f61747e42d8f582d9960f85d0f5a171f85c5c7e17560f83e0f83c3c3c3c3e0f85c3c3c5e0f83e0b0b1f1f1f1f82c2e0fa0f0f030f330f030f0f9680c5ccc5c0e170000000000000000005175542c2c2c2c2d547c4c4c7c2c2c2c2d45c5c8c4c2c5c5d51717171755131313130b0b0b0b37133713171317130000000000000717170b41c2d42c2c2c2c1c1c2c2c7cbc1c3c1cbc7c3c7c1c1c7c2c2c2c2d41c2d42c2d071745c5d10b45d170703072707030727070707070b070b073707370717507000000000000000b0b0b0b0b0b0b0b45c5d1742d8f50b0b45d1717231717171717545c3c5c5c5cbc5c3c2c2c2c2c2c2c2c5d45c5c0c5ccc5c0c5c5c000000000000002c2e070b9582e0b82e0b81e1faa8be0f8be0f555515555550707070781c2e80c1c9c1c0e27a075500000000000000aa555aaaaa2aaaaa55555515555551f1f1f1faaa81e03aaa550000000000000083e5656556555923aaaaaa5a1fa3eaaa6556aa5955645d555555663d547c7c7c7ea3380e9955aaaa954000000000000000002aaaaaaaa8f6aaa9555a07515555555aaaaaa0707070755000000000000aa5a55aaaa8aaaa555a5955155555513131313aaa81e03aaa5500000000000000541d548d230b82e50b87e8fa0f0f43d550fa0b82ea943d555541c3e82c2c2c2e83c3c3d44d555550b63d5555544c4c4c4d035541e0b0b83e83c3c0c3ccc3c0c3c3d54000000000000000002a96956aaaaa2aaaa95556555195555544c4c4c4eaaa0780eaa9540000000000000283d5592f5565595aaaaaa96aaaa1fa3d955aaa95555655555663d5603aa8cc4c4c4c4d955aaaa954000000000000000002aaaa9aaaaa83e81d455555556aaaaa83c1c3c1d54000000000002a9556aaaaaa2a9556955455555547c7c7c7eaaa0780eaa9540000000000000282c2d5547d8f5550f43e0f0f87c83e0b5543d47d55551f63d5551f1f1f1f1f1f1f1f40d543e83d54000000000000151f551f48c2e0b942e83c3e1fa3d0f5543eaaa50f555550f0fa0b0b0b0b0b0b0fa0f0f0f51f5555542d8f55543d175551f1f1f1f40d553382c2e0fa0f0f030f330f030f0f550000000000000000005548c2e0b942e1387d56a9551782ea0baa131313135582c2ea1384c4e0000000000170015548c2c2c2c2d42d2f5543c2c2c2c2d5555550b63d5503554cc2c2c2c2d54000000000000029554a95696aaaaaaa955555554544c4c4c4e03aa81eaaa95400000000000002a82e8f0b23a0b230b83e0fa0f0fa0f0faa47d513547d235544d5542d50b543d5555555543d8f55548c8c8c8c8c0c8ccc8c0c8c8e0b0b83e83d51340d5540000000000000000015a9523a548ea8faaaa55553b3b81c0e0000a555a555a2aaaaaaaa5555555515a81e03a2323aaaa5500000000000000 24 16777215 10 1023
def hc_78_20 : Nat → Nat := unpackHintV5 0xca8aeec361cabf2110b859b2b488f4b0211aa929bea2d9949b39e893c1de8ee1388a21308561307e19d279792872a1b66e212066a9de5e820a52530c4662fc3c029837a9162e724e27e1a41eaa4e1a19241601060f11bc0b90e00789020001e2 0x7a07a81e8fa0707a0f84eaa81c1c1c4e81c3c1d0763d60761344e66581e1741d69582e0784e0783c1c3e0783c1cbe075581e170707581e0f85c1c1c1c1c1e070781e81c1c0c1c1c1c0c1c1e5a030707070381c00000000000000007000281eaaaaaaaaa81e8faaa65a5a85d0763d69a699a96a1755a83d5aaaaa83eaa2faaa03aa81c1c1c1c1eaaaa5aa0780e80000000000000008000aaa0faa2aa560faaaaaaaa4669a665a5a13131313aaaa80eaa079600000000000000aaa0faaa8faaa81ea0faaa47d8f5a69a665a5a56aaaaaaaaa0fa85eaa83ea13131313aaaa80eaa0796a8ce03a00000000000000020002aa8aa9a69690763e66aaa5a81d6aaaaaa81c1c1c1eaa5aa800000000020029661faaaaaaa13aaaaaa891f1a5a5a69a661313131380eaa07aaaa9600000000000000a81ea88e23aaaa84eaaaaaa8f47d8f5a5a5a69a6656aa85ea2fa85eaaaaaaaaa1313131380eaa07aaaa96a8ce03a000000000000000200002c2e560b0b82c2cee85c2e1387e2f83e2f83ea919617582d85d82d984c4c4c4e031327130389e0b0ba84e5800000000000002a07070b0707a81e8fa0707a070f81e07aa41d6960785d1999981c9c1c1d41cfc120b0b89e96e001c0c1c1c1c0c1c1c1c1c1c1e070781e81e581c1c1c1c1e07a07a3e81c1e83e13aaa07070713a070f074666665a5a0484c4e0fa0f5073f07270707800707070781c1e07a0707030707070307079607070707a07aaaaaaaaaa07a3eaa99696a1746666689e963f04aaaa8080eaa0707070707aaaa9607070707aaa0faaa8faaa81ea0faaa4666665a5a04aaaa83eaa0f8013131313aaaa80eaa079627132713a81ea23aaaa84eaaaaaa8f465a5a66660489eaa3faaaa801313131380eaa07aaaa96271327130b82e84e1faa466666014a0b8f0b27a27aa2780000130700b0b273f0faa1f0fa000a84c4c4c4e0b0b89e84e589c4c4c9c4c4c7c0c4c1c9c0c4c1eaaaaa919999812aaa89e3eaa00002070aaaaaa80020f88c9c9c8eaaaa589c9c9c9ea0780e88e5ba0f83ea919999812272783c3ea89e3e00003c1c283c3c3e2e83c3c3e8002a2327272389c9e0fa0f96272727270f030f070f030f07230b0b23230b0b445d1742d1745c102c9c2c9c9c5c02327230b270b27271751727272727230b0b23230b0b48d8f5171745c5d0b45d17542c2c5c5c5c2c2c5c3c5c5c5cbc5c3c5c5c5c8c8c2c2c5d45c5c0c5ccc5c0c5c5c000000000001700002c2c4c5c2c2c2c2c2c2c2c2cec2d51f13131f1f2f130f132f1f0f0b0b0b0b515555555551313131313031327130313270b0b0b0b0b3713371355000000000000005541d175541d0b07070750707070b50b3b5550b0b0707070707070b8f072f07070707070f4bd550f0723070707070b0b0b0b555541d1755550763d42d555070307070703070740d550707070707070707070707070707075500000000000000000050744d550b0707070750f2f5550f0f07070f8f070707070b0f0f0f130b5071755555070f070707070b070707130707070f0755550763d44d555541d1755540d550707070707070707070707070707030707070307075500000000000000000055645d550743c1c1c1d684e0781e0b44d5581c4e0707a072358bd5543c3e07070707070f8fa1384e555541d1755550763d44d555070381e03070740d550707070707070781c1e07a075500000000000000000083ea07aaaa555a0fa9556a29455555655544c4c4c4ea0780eaaaa95400000000000001642d5582e0b99550f83c3e130f82c2e3e0f82d6555550f0f88c3c1e070f0f82c3e0b0b55551f63d42d555555540d55331313131382c2e0fa0f0f0381e030f07550000000000000000000b82eaa13071f1f50b0b5583c4e130fa2a5555511f63d42d55555551313131382c2e37031307370313070fa0f55000000000000005962f555552f88c4c1e071f2342d5582e0ba0f0b65543e0f1384c3e0b0b82e0f82c2e3d55547d8f555550b555503554cc4c4c4c4cbc0e0780c4c1e0b0b83e83d5400000000000000000145d5542c8c2c2d2f5543c8c8c2c2d55548d8f5555503554cc8c8c2c2d5400000000000002aaaa8a9607a9aaaaaaaa6466665a5a1f1f1f1faaaa80eaa079600000000000000aaa0faaa8faaa83ea0faaa5a47d8f66665a5a56aaaaa0faa8beaa0fa85eaa83ea1f1f1f1faaaa80eaa0f96a8ce03a000000000000000000aaa2aa6641d8f9699aaaa1faaaaaaa07070707aa96aa000000000000981e96aaaaaaaaaaaa8991696999987c7c7c7e03aa81eaaaa5800000000000002a1faa1f88eaaaa1faaaaaaa3d691f63d9696a17666656aa85ea2fa85ea0baaaaa0faa8beaa1f1f1f1f80eaa33aaaa96a8ce03a000000000000000000 24 16777215 10 1023
def hc_78_21 : Nat → Nat := unpackHintV5 0xfd38317b1071b9bc799c001bcd8e8e3680c8d2fa68c168c28eac110a527c71a5f069d1ee2148ad89344781ea14c1e0fcb1b67780db36bca0992a468bed1505888dc280c87117851c7b820835510e16d07b0a602104042581a40bc08489b02da2940002da 0x7076542d43e83d510380e0001c1c1c1c2c2c5d07070742c2c2c3c5cbc3c1c1c1c1c1c2cdc1c1c1c0c1c1c1c5c0c0c1c0e81e070b83e81e07941da0395170781e07070000007070707070b0707070707070b8f07630707070707070707070b0b0b0b07530707070707070707070b0b0b0b0303070707270307033b030707030707030707030b0703070307070307030703030303030307070707070703030707070b0707070f0707072f070707170741d07070707070000000000000000000b0b0b0b230b0b230b0b0b0b0b8f2f3b0f3b2f0f23230b0b0b0b4ec5ced1723230b0b0b0b033b333b033323230b0b0b0b0000000000000082c3c3c2c2e0b88c2c2c8e0b82e0b82e2f82c0f2388c3e0ba2fa617985c7e23aaaaa031f271f0389c7c8c8c7e0b0b83e83e8000000000000003c3c3c8c2c8c2c8c8c2c2c8c2c2c3c8c3e3c8c8c3c3c8c8cbc2c3cbc2c8c8c8c8c8d23172348c5c2c2c3cbcbc3c8c8c8c8c8c0c8ccc8c0c8c8c2c2c3cbcbc3c000000000000001c1c1c1c1c2c1c1c1c1c1c1c2e3c1c1c3cbc1c1c1c1c1c1c3c3c1c1c3e3c1c1c1c1c2c2c2c2c2c2c1c1c1c2c1c1c1c2c1c1c1cbc1c1c1c2c1c1c1c1c2c1c2c1c1c1c2c1cec1c1c1c3c1c1d07070741c5c1c1c1c1c2c2c2c2c3c3c3c3c1d07170741c1c1c0c1c1c1c0c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c0c1c1c1c0c1c1c1c1c1c1c0000000000000000002c2c2c2c4cbc2c2c2c2c2c2cec2c2c3c2c3c0f0f0b0b0f0f0b0b0b0b0b0b0f0b0b0b1f13131f1347c5c7d13170b0b0b0b0f0f0f0f1313131313031327130313270b0b0b0b0f0f0f0f131300000000000000230b0b0f230f8f0f0f0f0f0b0f0f0f0b0f2f0f0b0b0f0f0f0b0b0f0f0f23230b0b0f0f0f0f0f43c5c3d0f0f23230b0b0f0f0f0f0f030f330f030f0f0000000000000082c3c3e0b0b0b0b82c2cee8bc2e0f03e2382e0b82e0ba2f87e13a617985eaaa84c4c4c4c4c0e2780c4c9e0b0b82c3e83e138000000000000020782c1c1c1c3e0782c1c1c1c2ea07070707070b81c2cee0781e070b0b0707a81e8f81e2f0707a07070f0f81c7e07070707070f8fa0b82e07681da981e617072381c1eaaaa0703070707030707070381e03070707070707070781c1e07a0781c1e0000000000000000000f0f0f2f0b0b2f2f0b0b230b0b23232323230f0f0f230f8f0b0f2f2f0b2f4bc5cbd2f1723230b0b0f2f2f0f2f032f2f2f032f3323230b0b0f2f2f0f00000000000000a0b0b90b661f0b0f0b560b543c7e0f82d0f90f0b1f47d5550b54dc7c7d4d130342c7c00002a87e0f83eaaa6454047cdc7c7c9e1faa1f83e0faaa9a87d1f691f1f82e555a83eaaa371f1f3787e130380000201f0b0b0b1f82c0c4c0c1c7c2c3c2c0c0c0e0b0380c3c4c2c3c2c2e0f80c3c2cdc7c7cdd982c7c7c0c7c0c0c0c0c0c0c0c2c0c0c0c000004c1c1c2c4c2c3c2c1c1c2c1c2c1c3c2d4c7c7cdc2c7c0c4c1c1c7c0c7c0c2c2c0c7c4e0b0b03030380c0c2c2c3c3e0fa0b961313000001f230b0b0b0b0b0b0b230b0b0b0b0b0f0b0f0f0f0f2302c2c3c3c2c2c2c2c2c2c3c2c2c2c7c8c8c7d1f171f45c2c2c2c2c2c3c3c3c3c7c8c8c7c0c7c9c7c0c9c2c2c2c2c2c3c3c3c3c0000000000000008c2c8c2c3c3c3c3c3c8c3e3c2c3c3c2c3c8c3c2c2c3c3c3c2c2c3c3c3c8c8c8c8c2c2c3c3c3c3c3d0f170f43c3c8c8c8c8c2c2c3c3c3c3c3c0c3ccc3c0c3c3c000000000000003c3c3e82e82c2e0ba2f0f88c3e0f0f82c3ea87e13aaaa84e84c4c4c4c4e0b0b83e83e1380000000000001c3c3e0b82e0b82c2c2e070ba0f82e0b82e070f83c3e2a617985c7e07aaaa81c0e2780c1c9c1c1c1c1e070b83e81e078000000000000002c2c2c2c3c3c3c3c3c2c2c2e3c2c3c2c2c3c8c3c3c3c3c3c2c2c3c2c2c2c2c2c2c2c3c3c3c3c3d0f170f43c3c2c2c2c2c3c3c3c3c3c0c3ccc3c0c3c3c000000000000002c2c1c1c2c2c1cbcbc2c2c1c2c2c2c1c2c7cbc1c1cbc3c2c2c0b070b0f0f0b0b070b1f07071f0b0b0b0b0747c5c7d07170f2f2f0f070707070b070b0707030727070307270f072f070707000000000000001f230b131f230b0b0b0b0b0f0b0f2f0f0f2f0f0b0b0b0b0b0b1f13131f2f1f1f2f0b0b0b0b0f0f0f0f131313132f131f130b0b0b0b0f0f0f0f13130000000000002f232f2f2f2f230b0b0b0b0b0f0b2f0f2f2f0f0b0b0b0b0b0b0f0b0b0b8f2f4bc5cbd2f170b0b0b0b0f2f2f0f2f032f2f2f032f330b0b0b0b0f2f2f0f000000000000000b0b17170b0b0b0b542c8c2c2c2c2d2cbc7c3c7cbd2c3c7c8c8c7c2c2c2c2d555448d5555554b031f271f034b271f23231f0b0b0b0b550000000000000081eaa0f55a5aa5a55aa8a555515555580eaa071f1f1f1faaaa5500000000000000642e0b9590b583c3e1f0f550f0f58bd60b0b8f83e0b87c3c3e1f0f0f5550f0f59560b0f82c2d1f63d555555555551f1f1f1f54cd03582c2e0fa0f0f038ce030f0f550000000000000000000b82e1f171f07aa50b0b5583e0fa2a555155555555551f1f1f1f82c2e1f031f071f031f070fa0f5500000000000000661f1f1f87c7c7d5547d62f550b82e5642d60f0b83c7e1f0f550f0f58bd60b0b82e0f82c2e3d1f63d555555547d1755551f1f1f1f54cd0351f0387e031f3382c2e0fa0f5500000000000000000045d230b230b542d523232323543d2f50b0b48d8f555555548c8c8c8d53340d42c2d5400000000000002a07070b0707a81e8fa0707a070f81e07aa41d6960785d0763d60760b42e660707581e0b5581e0b560b070b81e0b073b81e0f81e2f81e170707030707070307070707070781c1e07a079680c1c1c1c0e0700000000000000001c000 25 33554431 11 2047
def hc_78_22 : Nat → Nat := unpackHintV5 0x2fa50e541acc8917c90da1220006d356aa66850a0c084092ed491e91d231c2d8254f903e4310001f2 0x2c2c2c2c2c2e3c2c8c2c2c2c8c2c8c8c8c8c8c8c8c3c8cbc8c3c2c2c2c2c8c8c8c8c8d23172348c5c2c2c2c2c8c8c8c8c8c0c8ccc8c0c8c8c2c2c2c2c000000000000003c3c3c3ea81c3c3c1c1e0b0b230b82e0b82e0b0b23a82e8f07070f3b81e2f0f0f81c1e070781c3e82e0b8ee81ceea617985c7e07aaaa81c1cec1cec1d8e0307072f0381c1c1c1c1e070b83e0781c1e0780000000000000000001c2c2c2c8c2c2c8c1c2c2c2c2e3c3c3c1c1c3c3c1c1c3cec3c1c1c1c1c2c2c2c2c2c2c2c3cbc3cbc3c7c1c1c1c1c2c2c2c2c2c2c2c2c2c2c1c1c1cec6c1cec1c6cec7c1c1c7c2c2c2c2c3c3c3c3c3d0f170f43c3c1dfc1cec1cec1c1c1c1c1c2c1c2c1c3c1c1c3c1c1c3c0c1c1c3c0c1c1c1c1c000000000000000002aaa864540c1c0c1c01569956983c1e69aa583da681ea5645d56659070360703a0760000045d17070b0b545d0750b230b542d0b50b23070b0b0b0b8f3b071b073b3b1b543d2f51f07071f0b0b0b0b41d3b5555541d550b555507073b073b0753541d035070707070b070b0707075541c000000000000000000299596a19500c1c0c1c0281eaaaaa81e07aa6a0f5981e6aa0fa8be56a0faaa81c0c1c0c1c1e81c0e00000a82c8c2c2c8ea0ba3e81cee8ee0787ea960785d074ed81d07982d0b9985d55607070782d60b82e0b83e178be0f81c1c1cdc1cec1cdc1c1c1c1c1e070b8de81e41d81e030707170381c00000000000000000000c0c0c0e80c1c1c0ea0780c1c1c1c1c0e0782c2c2c2e03070703a03070707070b0b6645d17030303070307030303030703070303030703070000036540d075607070341c1d0381e42c2d81e0343cbd40d075550742d4dc0c0d40c1d030341c0c1c0c0c1d030000003070327070707030303070307030307070b03030307030703030707070707070b8f0707070707077f0303030703070303070707070b0b0b0b070707070707370340c1c0d0303070707070b0b0b0b37370307033b0303030303030303030303070303030303070303030303030303070303030300000000000000000007aaaaaa19aa038f0303030001c1c1c1c2c2c1c1c1c1c2c2c2c2c1c1d1743c1c1c1c2c3c1c1c1c1c0c1c1c1c3c0c0c1c0e070781c2e0f070fa072f0703030381e0f070707079607070000 23 8388607 10 1023
def nh_78 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_78_22 (Nat.sub p 704)) (hc_78_21 (Nat.sub p 672)) (Nat.blt p 704)) (hc_78_20 (Nat.sub p 640)) (Nat.blt p 672)) (Bool.rec (Bool.rec (hc_78_19 (Nat.sub p 608)) (hc_78_18 (Nat.sub p 576)) (Nat.blt p 608)) (hc_78_17 (Nat.sub p 544)) (Nat.blt p 576)) (Nat.blt p 640)) (Bool.rec (Bool.rec (Bool.rec (hc_78_16 (Nat.sub p 512)) (hc_78_15 (Nat.sub p 480)) (Nat.blt p 512)) (hc_78_14 (Nat.sub p 448)) (Nat.blt p 480)) (Bool.rec (Bool.rec (hc_78_13 (Nat.sub p 416)) (hc_78_12 (Nat.sub p 384)) (Nat.blt p 416)) (hc_78_11 (Nat.sub p 352)) (Nat.blt p 384)) (Nat.blt p 448)) (Nat.blt p 544)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_78_10 (Nat.sub p 320)) (hc_78_9 (Nat.sub p 288)) (Nat.blt p 320)) (hc_78_8 (Nat.sub p 256)) (Nat.blt p 288)) (Bool.rec (Bool.rec (hc_78_7 (Nat.sub p 224)) (hc_78_6 (Nat.sub p 192)) (Nat.blt p 224)) (hc_78_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 256)) (Bool.rec (Bool.rec (Bool.rec (hc_78_4 (Nat.sub p 128)) (hc_78_3 (Nat.sub p 96)) (Nat.blt p 128)) (hc_78_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (hc_78_1 (Nat.sub p 32)) (hc_78_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)) (Nat.blt p 352)
def f_78 : Nat → Nat × Nat := unpackForestF 0xc5faf1b7d78d8ec9ce96437daf137d8c912c58e35e263b09bed849f6bc2df60144af638d7c4d2bd6e35e1630062bd75154016bf5bd67addab002d6eb48db5a457005abd5c97eb104957253ab8afd5c54ead6ac00b53aaa33554d980169753d6aa9db5002d1ea18ab52364a85a5d455a2a168e00a5fa3ab3d1d1ae8e8cf4e244a3a2dd339e2994d947457a392b51f15e8f6b747b57a3da5d1ed1e8f2974793ba3c99d1c090014b742c6da162bd0ad6e856af4437ca15a5d0d5c28568e00a57a0d224fb16e80cf14026c9f62bcfcd167d4ac00a539ed324e51be794893946b9dd3e4e519e75489394639c9b34e4998014973256a9beb44c8dbe6ccf13636c991b5cd55c2646cf33678999b64ccd52646c73226a00523cc4d9254adf2cb7e965be4b29ca5d7192c97f96a464b4e02592e72a56795e36ca8d9a55ad52a3560051fca499247adf2627e9313e49ae324d2692617391eb3c951b6474cd2456a91d2b0028ee458d118d6f8da394784fe414991e13b8f09bc7c4f23d4891e1338da38475202362ff1bd808dcae46c5ce31acf1a3568c635464d9a318b400a378bd3242f5be276fd13a7e8acb1c4e9f2287191413489cb9c2f59e238db11c5d88e2ac2e99a20ad51046685d2b43117e188af0c15b86c0a43054e192cd0c14b85c120028cdfe8ab0a3647f9a5c255a1fe68f082647f925c1d5a1fe48f05d6582db23fc8fe08acb042647f91dc0b596058d0ff2377feb2bfe9d1ff4c9004557fc123fc8cc012beeed6777635bbb19df9288eec5b7dcb63bb15ddd6d6eeb677cc9a3bad6df12d8eeb577be463d99ddec8ccf6144775a7bd2d99e9268eeb4b79ec03c99dde4ad4f215c775a3bc2d99e1268eeb437791fbbc8dddd2ac0095b64e36b2715d936b6c9b5775abe3acdf193696e624f74dae39892dd10b8e624773d2639ad51cd048e624372eb8326d1dc92c0e402464d2db2695dc4af8e227c64d25b855c19348ede57d6fdc637959dbc6f8de35664d1fb715f5b84f8dc25664d1db5d5f5b5900d75676c2b3b60d6db1cf0d83576ba3835d1699346ed357d6993e34c991a64acd3c6d69cb034c09193466ca34765125b2891d94476ca237650a5b2851d94276ca13766d233284bd9928cca12b65da532849d9528cca12364c3600255d91288b945b63cb62e515d8d268b935b62cb62e4d5d89288b934f61c9a2e4d2d852b8b934760c9a2e4d0d7c68abe2455f11faf88ed7c46ebe2335c8ab2e6d2d7368eb9a4b5cd23ae68fd73476b9a375cd19ae4050012a6b816453237adc5114c8d6b5d7c5acbe29919d69288a646359cb2298dbd65268a636b58abe2c45f14c6ceb0134531b1abc5114c69eae134531a5ab45714c68eac134531a1aa48fd52476a923754d3e2a48cd4c4cca6a3f5351da9a8dd4d466a6166004a5a515a949ad09436f51db6250dad45ae094367509b6284d51286c6a05684a137a7a9b13d0489426b4eeb825099d384d89c2544a131a6b9e9356d89423f4cd362508ed30cf4984604a11ba589b12c4a8960244a119a528fd2946e9416a004a3a4cd9105ade9037e481be244e31204fe90172416b3a3d1b5056cc8e56a415ab233595196c882a6f44e33226999134888a35644c1220a9ad106f88835641533a1a9990d48882a6342d2220a96d06cf483376419b620c9e9054ae0093f40cb21db5bd012f876d673fab29fc590ed6de7e1343b5b59f45f0ed6ce7c1343b5b19ec4d0ed6b67a16c3b5ab9e11b4f0496782473b4b31dd5a8ed2ac0093b3ae3419d5bce48e473a3f39d1b9c91c0e59007227f33ab39c4d58ce8d46fd6e37db319d168dcaca6e468339379b2970d90486726b35a381ad168ce4ce6a25c339319a4970ce4b667c7a33e3019c95c0126e661642aeb79945f0abace63d6531cb2156dbcc526855b6b30cbe156d9cbf6cc602572fc9a156d8cbd26855b5b2ecb6156d5cb08da5845d2c22a9609bcb04c65a4552c12e960954b0496582472acb31595a8ac8cc562452acab0024cca94c845d6f29d221471cca56e251a7e28d3e11759ca14c845c6f27a3313c9108b8d64e27c22e339331989948845c6325d2211716c93cf449c7a24d3611715c8f8da47b4b23da39169988cad44636b22d2b0024bc892c83756f21cbe0dd59c84aca421641ba379045106e8d64017c1ba338fb1987d288374631eca20dd16c792d8374571c6368e2d2c7168e3886e1c91d8e48dc710d8371661beb50dc55801256363680c6b78bb1fc696902ec7319a3e8cd1c45d6e42f24f18dae0bc92c5e48e3024c17daa0bc90c5d6e018d6716ab28b4da0318de2bc6615da40631ac52afa29a5b14d2b8a4dc0318ce2836013a3309cd20318c626370126bb0931d84969018c5b0ef3d0771e83c4de2237c0f1358835f0410f81e2670fd3607add03d0481e2630edb006315c378b61bc570dd2b062da832adc1946b0ca33864998316b4009270bcb20055bc2d2f8015670acb20051bc292880146b09cbe00519c252d811c6608ca200518c212880145b07cb600515c178da0bc5d05e2a82ed74176aa0bb4b05da380459813ad409c6604da2804558038be01c5700daf806d6c036ae0635600da9806d2c0368e0185b00c2980612c030760205600c19804050012460003f 10 11
def ch_78 : Nat → Bool := dagCheckNodeV5 fullMask g_78 ep_78 6 63 bds_78 717 (dagTraceF fullMask rootStock 11 f_78) cur_78 nh_78
set_option maxHeartbeats 0 in
theorem rc_78 : dagCheckRootsV5 fullMask g_78 ep_78 6 63 717 bds_78 (dagTraceF fullMask rootStock 11 f_78) (cur_78 0) (nh_78 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_0 : treeBlockF 0 32 ch_78 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_1 : treeBlockF 32 64 ch_78 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_2 : treeBlockF 64 96 ch_78 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_3 : treeBlockF 96 128 ch_78 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_4 : treeBlockF 128 160 ch_78 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_5 : treeBlockF 160 192 ch_78 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_6 : treeBlockF 192 224 ch_78 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_7 : treeBlockF 224 256 ch_78 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_8 : treeBlockF 256 288 ch_78 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_9 : treeBlockF 288 320 ch_78 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_10 : treeBlockF 320 352 ch_78 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_11 : treeBlockF 352 384 ch_78 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_12 : treeBlockF 384 416 ch_78 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_13 : treeBlockF 416 448 ch_78 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_14 : treeBlockF 448 480 ch_78 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_15 : treeBlockF 480 512 ch_78 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_16 : treeBlockF 512 544 ch_78 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_17 : treeBlockF 544 576 ch_78 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_18 : treeBlockF 576 608 ch_78 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_19 : treeBlockF 608 640 ch_78 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_20 : treeBlockF 640 672 ch_78 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_21 : treeBlockF 672 704 ch_78 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78_22 : treeBlockF 704 717 ch_78 = true := by decide +kernel
theorem nj_78_1 : ∀ i, 0 ≤ i → i < 64 → ch_78 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_78_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_78_1 h1 h2)
theorem nj_78_2 : ∀ i, 0 ≤ i → i < 96 → ch_78 i = true := block_join nj_78_1 (fun _ h1 h2 => treeBlockF_at nb_78_2 h1 h2)
theorem nj_78_3 : ∀ i, 0 ≤ i → i < 128 → ch_78 i = true := block_join nj_78_2 (fun _ h1 h2 => treeBlockF_at nb_78_3 h1 h2)
theorem nj_78_4 : ∀ i, 0 ≤ i → i < 160 → ch_78 i = true := block_join nj_78_3 (fun _ h1 h2 => treeBlockF_at nb_78_4 h1 h2)
theorem nj_78_5 : ∀ i, 0 ≤ i → i < 192 → ch_78 i = true := block_join nj_78_4 (fun _ h1 h2 => treeBlockF_at nb_78_5 h1 h2)
theorem nj_78_6 : ∀ i, 0 ≤ i → i < 224 → ch_78 i = true := block_join nj_78_5 (fun _ h1 h2 => treeBlockF_at nb_78_6 h1 h2)
theorem nj_78_7 : ∀ i, 0 ≤ i → i < 256 → ch_78 i = true := block_join nj_78_6 (fun _ h1 h2 => treeBlockF_at nb_78_7 h1 h2)
theorem nj_78_8 : ∀ i, 0 ≤ i → i < 288 → ch_78 i = true := block_join nj_78_7 (fun _ h1 h2 => treeBlockF_at nb_78_8 h1 h2)
theorem nj_78_9 : ∀ i, 0 ≤ i → i < 320 → ch_78 i = true := block_join nj_78_8 (fun _ h1 h2 => treeBlockF_at nb_78_9 h1 h2)
theorem nj_78_10 : ∀ i, 0 ≤ i → i < 352 → ch_78 i = true := block_join nj_78_9 (fun _ h1 h2 => treeBlockF_at nb_78_10 h1 h2)
theorem nj_78_11 : ∀ i, 0 ≤ i → i < 384 → ch_78 i = true := block_join nj_78_10 (fun _ h1 h2 => treeBlockF_at nb_78_11 h1 h2)
theorem nj_78_12 : ∀ i, 0 ≤ i → i < 416 → ch_78 i = true := block_join nj_78_11 (fun _ h1 h2 => treeBlockF_at nb_78_12 h1 h2)
theorem nj_78_13 : ∀ i, 0 ≤ i → i < 448 → ch_78 i = true := block_join nj_78_12 (fun _ h1 h2 => treeBlockF_at nb_78_13 h1 h2)
theorem nj_78_14 : ∀ i, 0 ≤ i → i < 480 → ch_78 i = true := block_join nj_78_13 (fun _ h1 h2 => treeBlockF_at nb_78_14 h1 h2)
theorem nj_78_15 : ∀ i, 0 ≤ i → i < 512 → ch_78 i = true := block_join nj_78_14 (fun _ h1 h2 => treeBlockF_at nb_78_15 h1 h2)
theorem nj_78_16 : ∀ i, 0 ≤ i → i < 544 → ch_78 i = true := block_join nj_78_15 (fun _ h1 h2 => treeBlockF_at nb_78_16 h1 h2)
theorem nj_78_17 : ∀ i, 0 ≤ i → i < 576 → ch_78 i = true := block_join nj_78_16 (fun _ h1 h2 => treeBlockF_at nb_78_17 h1 h2)
theorem nj_78_18 : ∀ i, 0 ≤ i → i < 608 → ch_78 i = true := block_join nj_78_17 (fun _ h1 h2 => treeBlockF_at nb_78_18 h1 h2)
theorem nj_78_19 : ∀ i, 0 ≤ i → i < 640 → ch_78 i = true := block_join nj_78_18 (fun _ h1 h2 => treeBlockF_at nb_78_19 h1 h2)
theorem nj_78_20 : ∀ i, 0 ≤ i → i < 672 → ch_78 i = true := block_join nj_78_19 (fun _ h1 h2 => treeBlockF_at nb_78_20 h1 h2)
theorem nj_78_21 : ∀ i, 0 ≤ i → i < 704 → ch_78 i = true := block_join nj_78_20 (fun _ h1 h2 => treeBlockF_at nb_78_21 h1 h2)
theorem nj_78_22 : ∀ i, 0 ≤ i → i < 717 → ch_78 i = true := block_join nj_78_21 (fun _ h1 h2 => treeBlockF_at nb_78_22 h1 h2)
theorem nc_78 : ∀ i, 0 ≤ i → i < 717 → ch_78 i = true := nj_78_22
theorem lb_78 : LowerBin fullMask rootStock g_78 12 :=
  lowerDagV5 (kn_cons lb_75 (kn_cons lb_72 (kn_cons lb_16 (kn_cons lb_73 (kn_cons lb_43 (kn_cons lb_68 (kn_cons lb_67 (kn_cons lb_15 (kn_cons lb_69 (kn_cons lb_57 (kn_cons lb_62 (kn_cons lb_71 (kn_cons lb_54 (kn_cons lb_56 (kn_cons lb_70 (kn_cons lb_77 (kn_cons lb_12 (kn_cons lb_74 (kn_cons lb_31 (kn_cons lb_17 (kn_cons lb_28 (kn_cons lb_36 (kn_cons lb_48 (kn_cons lb_58 (kn_cons lb_40 (kn_cons lb_39 (kn_cons lb_30 (kn_cons lb_47 (kn_cons lb_38 (kn_cons lb_5 (kn_cons lb_23 (kn_cons lb_65 (kn_cons lb_29 (kn_cons lb_42 (kn_cons lb_46 (kn_cons lb_26 (kn_cons lb_63 (kn_cons lb_6 (kn_nil))))))))))))))))))))))))))))))))))))))) rc_78 nc_78 (by decide +kernel)

def wg : List Gate := [⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [3, 13]⟩, ⟨GateOp.and, [9, 12]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.and, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4008241280 * 2 ^ 32 + 3936927872) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4008241280 * 2 ^ 32 + 3936927872)) (13 - 1) := by
  rw [show canon fullMask (4008241280 * 2 ^ 32 + 3936927872) = g_78 by decide]
  exact lb_78

end PEqualNP.Outside.L_meta_47425

theorem PEqualNP.Outside.L_meta_47425 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241280 * 2 ^ 32 + 3936927872) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241280 * 2 ^ 32 + 3936927872) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_47425.table2_from_lowerBin (4008241280 * 2 ^ 32 + 3936927872) 13 PEqualNP.Outside.L_meta_47425.root_lb PEqualNP.Outside.L_meta_47425.wg 18 rfl PEqualNP.Outside.L_meta_47425.wfits PEqualNP.Outside.L_meta_47425.weval

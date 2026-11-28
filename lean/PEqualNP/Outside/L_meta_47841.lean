import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47841

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

def m_0 : Nat := 0xf000f0000000000
def s_0 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_0 : Nat := 0x100070000000000
def ep_0 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
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

def m_1 : Nat := 0x3300330000000000
def s_1 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_1 : Nat := 0x100130000000000
def ep_1 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
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

def m_2 : Nat := 0x5500550000000000
def s_2 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_2 : Nat := 0x100150000000000
def ep_2 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
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

def m_3 : Nat := 0x4444444400000000
def s_3 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_3 : Nat := 0x4044400000000
def ep_3 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_4 : Nat := 0xff00
def s_4 : List Nat := [0x5500, 0x3300, 0xf00]
def g_4 : Nat := 0x1700
def ep_4 : Nat := 0x60000000000000012000000000000001400
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

def m_5 : Nat := 0x5050505000000000
def s_5 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_5 : Nat := 0x10105000000000
def ep_5 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
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

def m_6 : Nat := 0x3333000000000000
def s_6 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_6 : Nat := 0x113000000000000
def ep_6 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
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

def m_7 : Nat := 0x5555000000000000
def s_7 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_7 : Nat := 0x115000000000000
def ep_7 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
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

def m_8 : Nat := 0xff000000000000
def s_8 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_8 : Nat := 0x17000000000000
def ep_8 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_9 : Nat := 0xf0f000000000000
def s_9 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_9 : Nat := 0x107000000000000
def ep_9 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_10 : Nat := 0x3300000033000000
def s_10 : List Nat := [0x1100000011000000, 0x300000003000000, 0x33000000]
def g_10 : Nat := 0x100000013000000
def ep_10 : Nat := 0x1200000000000000000000000000000000000000010000000200000000000000000000000100000010000000
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

def m_11 : Nat := 0x44444444
def s_11 : List Nat := [0x4040404, 0x440044, 0x4444]
def g_11 : Nat := 0x40444
def ep_11 : Nat := 0x4400000000000040040000000000004040000000000000000000000000000000000
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

def m_12 : Nat := 0xc0c0c0c
def s_12 : List Nat := [0x4040404, 0xc000c, 0xc0c]
def g_12 : Nat := 0x4040c
def ep_12 : Nat := 0x4080000000000040008000000000000000000000000000000000000000000040400
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

def m_13 : Nat := 0xff0000000000
def s_13 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_13 : Nat := 0x170000000000
def ep_13 : Nat := 0x6000000000000001200000000000000140000000000
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

def m_14 : Nat := 0x2222000022220000
def s_14 : List Nat := [0x202000002020000, 0x22000000220000, 0x22220000]
def g_14 : Nat := 0x2000002220000
def ep_14 : Nat := 0x220000000000000000000000002000000200000000200000200000000000000000000000000000000000000
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

def m_15 : Nat := 0x3030000030300000
def s_15 : List Nat := [0x1010000010100000, 0x30000000300000, 0x30300000]
def g_15 : Nat := 0x10000010300000
def ep_15 : Nat := 0x1020000000000000000000000010000000200000000000000000000000000000000000000010000010000000
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

def m_16 : Nat := 0x30c030c030c030c0
def s_16 : List Nat := [0x1040104010401040, 0xc000c000c000c0, 0x30c0000030c0, 0x30c030c0]
def g_16 : Nat := 0x1040100010c0
def ep_16 : Nat := 0x1000008000001040000000c00000000000000000000000000000000000000000000000000000104010001000
def bds_16 : List (Nat × List Nat × Nat × Nat) := []
def cur_16 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xa9610f 4 15 2 3 6 63 8 255
def nh_16 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_16 : Nat → Nat × Nat := unpackForestF 0x1a708f 1 6
def ch_16 : Nat → Bool := dagCheckNodeV5 m_16 g_16 ep_16 1 1 bds_16 3 (dagTraceF m_16 s_16 4 f_16) cur_16 nh_16
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV5 m_16 g_16 ep_16 1 1 3 bds_16 (dagTraceF m_16 s_16 4 f_16) (cur_16 0) (nh_16 0) s_16 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16 : treeBlockF 0 3 ch_16 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 3 → ch_16 i = true := fun _ h1 h2 => treeBlockF_at nb_16 h1 h2
theorem lb_16 : LowerBin m_16 s_16 g_16 5 :=
  lowerDagV5 (kn_nil) rc_16 nc_16 (by decide +kernel)

def m_17 : Nat := 0x33cc33cc
def s_17 : List Nat := [0x11441144, 0xcc00cc, 0x30c030c, 0x33cc]
def g_17 : Nat := 0x130413cc
def ep_17 : Nat := 0xc80000000000000000000000000204020000000000000000000000000010041000
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
def cc_17_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xf41e83d0724e03c0370ee0dc1b0760606c01786e0dc0b43682c0ce59c128a504a08c518230460844d981d001 0x7c4c3c221d0b0e04808203212160d0c2745d362a9514498903c081d240e050b020380c1c04960f1307088343c181a0709020381c34060e040d01848283d121a880b4304a141e040ecd8fe64772e378719be4fdda76e1376e99b24bd7a56b1275691aa0fd4876a0374619a20bd0856802736119a07c983c441b200b8b04c0824000f 11 2047 5 31 10 1023 17 131071
def cc_17_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb4b0a99390907b78787878785c58513b38382320202020202020200400000000 0x214710634801c3f0d0c838f53c789a180b1d098e4402e0e36931ac88d0286612160718a98c1442a162e0f16860501c4e1e260d128589024 8 255 3 7 10 1023 17 131071
def cc_17_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x14284974e18b060c14850000000 0x2546125288a12498d22c692b4490944749230511024 7 127 3 7 10 1023 17 131071
def cur_17 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_17_2 (Nat.sub p 64)) (cc_17_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_17_0 p) (Nat.blt p 32)
def hc_17_0 : Nat → Nat := unpackHintV5 0x8234009f08e4a6c33601a84d026803309904b4a581291930c90446121110047463811c00d846c03601a08d006803020f480b8002 0x0 13 8191 5 31
def hc_17_1 : Nat → Nat := unpackHintV5 0x7c29e087709cc87111bc46b2198a64118085e1170457294c852093884c11284462104a3848c4e2848984231888220106ca12482ce0248004 0x0 14 16383 5 31
def hc_17_2 : Nat → Nat := unpackHintV5 0x4159b2cb144c6241101078438218209182901020420108004 0x0 13 8191 5 31
def nh_17 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_17_2 (Nat.sub p 64)) (hc_17_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_17_0 p) (Nat.blt p 32)
def f_17 : Nat → Nat × Nat := unpackForestF 0xc7e063b031bc4d124c6911288892440a22c6910240319bf8e1fc68fc387e1a014fde278f134029db9131c88005370299b39319c88cc286612014bd8298c1440295ad0f1686005270291810fc08760437481e240d1205890240219810bc0856042738261c110e058702402118107cc848513a289b160d0a2545126020f120700836041718260c110607830340209820f4106a082d0e1a02094103c0c340612020740824000f 7 10
def ch_17 : Nat → Bool := dagCheckNodeV5 m_17 g_17 ep_17 1 1 bds_17 78 (dagTraceF m_17 s_17 5 f_17) cur_17 nh_17
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV5 m_17 g_17 ep_17 1 1 78 bds_17 (dagTraceF m_17 s_17 5 f_17) (cur_17 0) (nh_17 0) s_17 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_0 : treeBlockF 0 32 ch_17 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_1 : treeBlockF 32 64 ch_17 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_2 : treeBlockF 64 78 ch_17 = true := by decide +kernel
theorem nj_17_1 : ∀ i, 0 ≤ i → i < 64 → ch_17 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_17_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_17_1 h1 h2)
theorem nj_17_2 : ∀ i, 0 ≤ i → i < 78 → ch_17 i = true := block_join nj_17_1 (fun _ h1 h2 => treeBlockF_at nb_17_2 h1 h2)
theorem nc_17 : ∀ i, 0 ≤ i → i < 78 → ch_17 i = true := nj_17_2
theorem lb_17 : LowerBin m_17 s_17 g_17 6 :=
  lowerDagV5 (kn_nil) rc_17 nc_17 (by decide +kernel)

def m_18 : Nat := 0x3c3c3c3c
def s_18 : List Nat := [0x14141414, 0xc0c0c0c, 0x3c003c, 0x3c3c]
def g_18 : Nat := 0x1034143c
def ep_18 : Nat := 0x4080000000000240028000000000000000000000000000000000000000010041400
def bds_18 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_18 : Nat → List (Nat × Nat) := fun _ => []
def nh_18 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_18 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 0 bds_18 (dagTraceF m_18 s_18 4 f_18) (cur_18 0) (nh_18 0) s_18 4 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 0 (dagTraceF m_18 s_18 4 f_18) cur_18 nh_18 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0x3030c0c03030c0c
def s_19 : List Nat := [0x101040401010404, 0xc0c00000c0c, 0x3000c0003000c, 0x3030c0c]
def g_19 : Nat := 0x10304040303040c
def ep_19 : Nat := 0x200000800000000000000000002000000000008000000000000000000000000000000000100040400000400
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
def cur_19 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1d283091e3420d0d2420a263a88d993a54d903a10d800f 7 127 3 7 10 1023 14 16383
def nh_19 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_19 : Nat → Nat × Nat := unpackForestF 0xc74636f1a14e8a6c43a49220a086c00f 3 10
def ch_19 : Nat → Bool := dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 10 (dagTraceF m_19 s_19 4 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 10 bds_19 (dagTraceF m_19 s_19 4 f_19) (cur_19 0) (nh_19 0) s_19 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19 : treeBlockF 0 10 ch_19 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 10 → ch_19 i = true := fun _ h1 h2 => treeBlockF_at nb_19 h1 h2
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagV5 (kn_nil) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0xaa00aa00aa00aa0
def s_20 : List Nat := [0x220022002200220, 0xa000a000a000a0, 0xaa000000aa0, 0xaa00aa0]
def g_20 : Nat := 0x200022002a0
def ep_20 : Nat := 0x22000a000000200000000800000000000000000000000000000000000000200022002000000000000000000
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
def cur_20 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x14a59080f 4 15 2 3 9 511 11 2047
def nh_20 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_20 : Nat → Nat × Nat := unpackForestF 0x329c840f 1 9
def ch_20 : Nat → Bool := dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 3 (dagTraceF m_20 s_20 4 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 3 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) (nh_20 0) s_20 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20 : treeBlockF 0 3 ch_20 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 3 → ch_20 i = true := fun _ h1 h2 => treeBlockF_at nb_20 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV5 (kn_nil) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xff0000ff00
def s_21 : List Nat := [0x5500005500, 0x3300003300, 0xf00000f00, 0xff00]
def g_21 : Nat := 0x5700001700
def ep_21 : Nat := 0x20000060000000002000012000000005400001400
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_21 : Nat → List (Nat × Nat) := fun _ => []
def nh_21 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_21 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 0 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) (nh_21 0) s_21 4 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 0 (dagTraceF m_21 s_21 4 f_21) cur_21 nh_21 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xff00ff0000000000
def s_22 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_22 : Nat := 0x100170000000000
def ep_22 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_13, s_13, 4, g_13), (m_2, s_2, 4, g_2), (m_1, s_1, 4, g_1)]
def cc_22_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_22_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_22 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_22_1 (Nat.sub p 32)) (cc_22_0 p) (Nat.blt p 32)
def hc_22_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_22_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_22 : Nat → Nat := fun p => Bool.rec (hc_22_1 (Nat.sub p 32)) (hc_22_0 p) (Nat.blt p 32)
def f_22 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_22 : Nat → Bool := dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 43 (dagTraceF m_22 s_22 6 f_22) cur_22 nh_22
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 43 bds_22 (dagTraceF m_22 s_22 6 f_22) (cur_22 0) (nh_22 0) s_22 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22_0 : treeBlockF 0 32 ch_22 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22_1 : treeBlockF 32 43 ch_22 = true := by decide +kernel
theorem nj_22_1 : ∀ i, 0 ≤ i → i < 43 → ch_22 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_22_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_22_1 h1 h2)
theorem nc_22 : ∀ i, 0 ≤ i → i < 43 → ch_22 i = true := nj_22_1
theorem lb_22 : LowerBin m_22 s_22 g_22 7 :=
  lowerDagV5 (kn_cons lb_0 (kn_cons lb_13 (kn_cons lb_2 (kn_cons lb_1 (kn_nil))))) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0xffff000000000000
def s_23 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_23 : Nat := 0x117000000000000
def ep_23 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9), (m_8, s_8, 4, g_8), (m_7, s_7, 4, g_7), (m_6, s_6, 4, g_6)]
def cc_23_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_23_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_23 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_23_1 (Nat.sub p 32)) (cc_23_0 p) (Nat.blt p 32)
def hc_23_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_23_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_23 : Nat → Nat := fun p => Bool.rec (hc_23_1 (Nat.sub p 32)) (hc_23_0 p) (Nat.blt p 32)
def f_23 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_23 : Nat → Bool := dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 43 (dagTraceF m_23 s_23 6 f_23) cur_23 nh_23
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 43 bds_23 (dagTraceF m_23 s_23 6 f_23) (cur_23 0) (nh_23 0) s_23 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23_0 : treeBlockF 0 32 ch_23 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23_1 : treeBlockF 32 43 ch_23 = true := by decide +kernel
theorem nj_23_1 : ∀ i, 0 ≤ i → i < 43 → ch_23 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_23_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_23_1 h1 h2)
theorem nc_23 : ∀ i, 0 ≤ i → i < 43 → ch_23 i = true := nj_23_1
theorem lb_23 : LowerBin m_23 s_23 g_23 7 :=
  lowerDagV5 (kn_cons lb_9 (kn_cons lb_8 (kn_cons lb_7 (kn_cons lb_6 (kn_nil))))) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0xffff00000000
def s_24 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_24 : Nat := 0x175700000000
def ep_24 : Nat := 0x4000000000000006020000000000001202000000000000145400000000
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def nh_24 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0xf0f0f0f000000000
def s_25 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_25 : Nat := 0x10105000000000
def ep_25 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000010105000000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def nh_25 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) (nh_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 nh_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0xf0f0f0f00000000
def s_26 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_26 : Nat := 0x107070700000000
def ep_26 : Nat := 0x600000000000006000000000000000000000000000001020202000000000104040400000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def nh_26 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) (nh_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 nh_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0xaa00aa00aa00aa
def s_27 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_27 : Nat := 0x20002002200aa
def ep_27 : Nat := 0x2000a800000000000000880000000000000000000200020000000000020002002200000000000000000000
def bds_27 : List (Nat × List Nat × Nat × Nat) := []
def cur_27 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_27 : Nat → Nat := fun _ => 0
def f_27 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_27 : Nat → Bool := dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 1 (dagTraceF m_27 s_27 3 f_27) cur_27 nh_27
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 1 bds_27 (dagTraceF m_27 s_27 3 f_27) (cur_27 0) (nh_27 0) s_27 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27 : treeBlockF 0 1 ch_27 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 1 → ch_27 i = true := fun _ h1 h2 => treeBlockF_at nb_27 h1 h2
theorem lb_27 : LowerBin m_27 s_27 g_27 4 :=
  lowerDagV5 (kn_nil) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0x5555555500000000
def s_28 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_28 : Nat := 0x115155500000000
def ep_28 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_7, s_7, 4, g_7), (m_5, s_5, 4, g_5), (m_3, s_3, 4, g_3)]
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
  lowerDagV5 (kn_cons lb_2 (kn_cons lb_7 (kn_cons lb_5 (kn_cons lb_3 (kn_nil))))) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0x3030303030303030
def s_29 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_29 : Nat := 0x10101010301030
def ep_29 : Nat := 0x1020002000001000000000000010000000200020000000000000000000000000000000000010101010001000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_29 : Nat → List (Nat × Nat) := fun _ => []
def nh_29 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 0 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) (nh_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 0 (dagTraceF m_29 s_29 4 f_29) cur_29 nh_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0xcccc0000cccc
def s_30 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_30 : Nat := 0x444000004cc
def ep_30 : Nat := 0x88000000000000000000000040000000c8000004000000040000000000000000000000044400000400
def bds_30 : List (Nat × List Nat × Nat × Nat) := []
def cur_30 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_30 : Nat → Nat := fun _ => 0
def f_30 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_30 : Nat → Bool := dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 1 (dagTraceF m_30 s_30 3 f_30) cur_30 nh_30
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 1 bds_30 (dagTraceF m_30 s_30 3 f_30) (cur_30 0) (nh_30 0) s_30 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30 : treeBlockF 0 1 ch_30 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 1 → ch_30 i = true := fun _ h1 h2 => treeBlockF_at nb_30 h1 h2
theorem lb_30 : LowerBin m_30 s_30 g_30 4 :=
  lowerDagV5 (kn_nil) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0x3333000033330000
def s_31 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_31 : Nat := 0x113000013330000
def ep_31 : Nat := 0x1220000000000000000000000012000000200000010200000200000000000000000000000110000010000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_10, s_10, 4, g_10), (m_15, s_15, 4, g_15), (m_14, s_14, 4, g_14)]
def cc_31_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_31_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_31 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_31_1 (Nat.sub p 32)) (cc_31_0 p) (Nat.blt p 32)
def hc_31_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_31_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_31 : Nat → Nat := fun p => Bool.rec (hc_31_1 (Nat.sub p 32)) (hc_31_0 p) (Nat.blt p 32)
def f_31 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_31 : Nat → Bool := dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 43 (dagTraceF m_31 s_31 6 f_31) cur_31 nh_31
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 43 bds_31 (dagTraceF m_31 s_31 6 f_31) (cur_31 0) (nh_31 0) s_31 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_0 : treeBlockF 0 32 ch_31 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_1 : treeBlockF 32 43 ch_31 = true := by decide +kernel
theorem nj_31_1 : ∀ i, 0 ≤ i → i < 43 → ch_31 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_31_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_31_1 h1 h2)
theorem nc_31 : ∀ i, 0 ≤ i → i < 43 → ch_31 i = true := nj_31_1
theorem lb_31 : LowerBin m_31 s_31 g_31 7 :=
  lowerDagV5 (kn_cons lb_6 (kn_cons lb_10 (kn_cons lb_15 (kn_cons lb_14 (kn_nil))))) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0xaaaa0000aaaa0000
def s_32 : List Nat := [0x2222000022220000, 0xa0a00000a0a0000, 0xaa000000aa0000, 0xaaaa0000]
def g_32 : Nat := 0x2000002220000
def ep_32 : Nat := 0x220000000000000000000000002000000200000000200000200000000020000022200000000000000000000
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_32 : Nat → List (Nat × Nat) := fun _ => []
def nh_32 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 0 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) (nh_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 0 (dagTraceF m_32 s_32 4 f_32) cur_32 nh_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0x5555000055550000
def s_33 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_33 : Nat := 0x115000011150000
def ep_33 : Nat := 0x1000000000000000000000000014000000040000010400000004000001100000111000000000000000000000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def nh_33 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) (nh_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 nh_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0x5500550055005500
def s_34 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_34 : Nat := 0x100150011001500
def ep_34 : Nat := 0x1000000000001400000004000000000000000000010004000000040001001000110010000000000000000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def nh_34 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) (nh_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 nh_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0xf0f00000f0f0
def s_35 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_35 : Nat := 0x1050000010f0
def ep_35 : Nat := 0xa0000000000000000000000040000000e0000000000000000000001000000010000000105000001000
def bds_35 : List (Nat × List Nat × Nat × Nat) := []
def cur_35 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_35 : Nat → Nat := fun _ => 0
def f_35 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_35 : Nat → Bool := dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 1 (dagTraceF m_35 s_35 3 f_35) cur_35 nh_35
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 1 bds_35 (dagTraceF m_35 s_35 3 f_35) (cur_35 0) (nh_35 0) s_35 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35 : treeBlockF 0 1 ch_35 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 1 → ch_35 i = true := fun _ h1 h2 => treeBlockF_at nb_35 h1 h2
theorem lb_35 : LowerBin m_35 s_35 g_35 4 :=
  lowerDagV5 (kn_nil) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0xf000f000f000f00
def s_36 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_36 : Nat := 0x100070003000700
def ep_36 : Nat := 0x200000000000600000004000000000000000000000000000000000001000200030002000100040000000400
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def nh_36 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) (nh_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 nh_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0xcc00cc00cc00cc
def s_37 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_37 : Nat := 0x40044000400cc
def ep_37 : Nat := 0x8800000040000000c80000000000000000000400000004000000000000000000000004004400040000
def bds_37 : List (Nat × List Nat × Nat × Nat) := []
def cur_37 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_37 : Nat → Nat := fun _ => 0
def f_37 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_37 : Nat → Bool := dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 1 (dagTraceF m_37 s_37 3 f_37) cur_37 nh_37
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 1 bds_37 (dagTraceF m_37 s_37 3 f_37) (cur_37 0) (nh_37 0) s_37 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37 : treeBlockF 0 1 ch_37 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 1 → ch_37 i = true := fun _ h1 h2 => treeBlockF_at nb_37 h1 h2
theorem lb_37 : LowerBin m_37 s_37 g_37 4 :=
  lowerDagV5 (kn_nil) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0xffff0000
def s_38 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_38 : Nat := 0x13370000
def ep_38 : Nat := 0x240000000000000204000000000000133200000000000010040000
def bds_38 : List (Nat × List Nat × Nat × Nat) := []
def cc_38_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0x793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_38_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014 8 255 3 7 10 1023 16 65535
def cur_38 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_38_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_38_0 p) (Nat.blt p 32)
def hc_38_0 : Nat → Nat := unpackHintV5 0xa142548910a03a70c952850a142240810203460c1220405080400000 0x0 7 127 2 3
def hc_38_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3870c983054a1120344881020405081020402 0x0 7 127 2 3
def hc_38_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_38 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_38_2 (Nat.sub p 64)) (hc_38_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_38_0 p) (Nat.blt p 32)
def f_38 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def ch_38 : Nat → Bool := dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 64 (dagTraceF m_38 s_38 5 f_38) cur_38 nh_38
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 64 bds_38 (dagTraceF m_38 s_38 5 f_38) (cur_38 0) (nh_38 0) s_38 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_0 : treeBlockF 0 32 ch_38 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_1 : treeBlockF 32 64 ch_38 = true := by decide +kernel
theorem nj_38_1 : ∀ i, 0 ≤ i → i < 64 → ch_38 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_38_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_38_1 h1 h2)
theorem nc_38 : ∀ i, 0 ≤ i → i < 64 → ch_38 i = true := nj_38_1
theorem lb_38 : LowerBin m_38 s_38 g_38 6 :=
  lowerDagV5 (kn_nil) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0xffff
def s_39 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_39 : Nat := 0x17ff
def ep_39 : Nat := 0xe8000000000000060000000000000012000000000000001400
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def nh_39 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) (nh_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 nh_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xff00ff00
def s_40 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_40 : Nat := 0x13001700
def ep_40 : Nat := 0x4000000000000000000000000000200060000000000130012000000000010001400
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def nh_40 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0xf0f0f0f0
def s_41 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_41 : Nat := 0x103010f0
def ep_41 : Nat := 0xc000000000002000e0000000000000000000000000103010000000000010001000
def bds_41 : List (Nat × List Nat × Nat × Nat) := []
def cur_41 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_41 : Nat → Nat := fun _ => 0
def f_41 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_41 : Nat → Bool := dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 1 (dagTraceF m_41 s_41 3 f_41) cur_41 nh_41
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 1 bds_41 (dagTraceF m_41 s_41 3 f_41) (cur_41 0) (nh_41 0) s_41 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41 : treeBlockF 0 1 ch_41 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 1 → ch_41 i = true := fun _ h1 h2 => treeBlockF_at nb_41 h1 h2
theorem lb_41 : LowerBin m_41 s_41 g_41 4 :=
  lowerDagV5 (kn_nil) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0xf0f0f0f
def s_42 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_42 : Nat := 0x307070f
def ep_42 : Nat := 0x4080000000000040008000000000000000000000000030202000000000000040400
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def nh_42 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) (nh_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 nh_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xcccccccc
def s_43 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_43 : Nat := 0x404cc
def ep_43 : Nat := 0x4c800000000000400c8000000000004040000000000000000000000000000040400
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def nh_43 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) (nh_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 nh_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xaaaaaaaa
def s_44 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_44 : Nat := 0x22202aa
def ep_44 : Nat := 0x8800000000002000a8000000000200020000000000022202000000000000000000
def bds_44 : List (Nat × List Nat × Nat × Nat) := []
def cur_44 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_44 : Nat → Nat := fun _ => 0
def f_44 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_44 : Nat → Bool := dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 1 (dagTraceF m_44 s_44 3 f_44) cur_44 nh_44
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 1 bds_44 (dagTraceF m_44 s_44 3 f_44) (cur_44 0) (nh_44 0) s_44 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44 : treeBlockF 0 1 ch_44 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 1 → ch_44 i = true := fun _ h1 h2 => treeBlockF_at nb_44 h1 h2
theorem lb_44 : LowerBin m_44 s_44 g_44 4 :=
  lowerDagV5 (kn_nil) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0x55555555
def s_45 : List Nat := [0x11111111, 0x5050505, 0x550055, 0x5555]
def g_45 : Nat := 0x11151555
def ep_45 : Nat := 0x4400000000000040040000000000004040000000000111010000000000000000000
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def nh_45 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) (nh_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 nh_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xff000000ff000000
def s_46 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_46 : Nat := 0x100000013000000
def ep_46 : Nat := 0x1200000000000000000000000000000000000000010000000200000001000000130000000100000010000000
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def nh_46 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) (nh_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 nh_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0xff000000ff0000
def s_47 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_47 : Nat := 0x17000000370000
def ep_47 : Nat := 0x20000000000000000000000000000000000000000600000004000000120000003200000014000000040000
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def nh_47 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) (nh_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 nh_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0xf0f00000f0f00000
def s_48 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_48 : Nat := 0x10000010300000
def ep_48 : Nat := 0x1020000000000000000000000010000000200000000000000000000000100000103000000010000010000000
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def nh_48 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xf0f00000f0f0000
def s_49 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_49 : Nat := 0x107000003070000
def ep_49 : Nat := 0x200000000000000000000000006000000040000000000000000000001020000030200000104000000040000
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def nh_49 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) (nh_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 nh_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0x2222222222222222
def s_50 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_50 : Nat := 0x2020202220222
def ep_50 : Nat := 0x220002000000200000000000002000000200020000202020200020000000000000000000000000000000000
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def nh_50 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) (nh_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 nh_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0xa0a0a0a0a0a0a0a
def s_51 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_51 : Nat := 0x202020202020a
def ep_51 : Nat := 0x200000800000200000000080002000000000008000000000000000000020202020202000000000000000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := []
def cc_51_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_51_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_51 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_51_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_51_0 p) (Nat.blt p 32)
def hc_51_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_51_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_51_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_51 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_51_2 (Nat.sub p 64)) (hc_51_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_51_0 p) (Nat.blt p 32)
def f_51 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_51 : Nat → Bool := dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 64 (dagTraceF m_51 s_51 5 f_51) cur_51 nh_51
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 64 bds_51 (dagTraceF m_51 s_51 5 f_51) (cur_51 0) (nh_51 0) s_51 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_0 : treeBlockF 0 32 ch_51 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_1 : treeBlockF 32 64 ch_51 = true := by decide +kernel
theorem nj_51_1 : ∀ i, 0 ≤ i → i < 64 → ch_51 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_51_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_51_1 h1 h2)
theorem nc_51 : ∀ i, 0 ≤ i → i < 64 → ch_51 i = true := nj_51_1
theorem lb_51 : LowerBin m_51 s_51 g_51 6 :=
  lowerDagV5 (kn_nil) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0xa5a5a5a5
def s_52 : List Nat := [0x5050505, 0x21212121, 0xa500a5, 0xa5a5]
def g_52 : Nat := 0x12505a5
def ep_52 : Nat := 0x48000000000002400a0000000000000000000000000012000000000000000000000
def bds_52 : List (Nat × List Nat × Nat × Nat) := []
def cur_52 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xba5d37b3a7b2d4e80f 7 127 3 7 6 63 9 511
def nh_52 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_52 : Nat → Nat × Nat := unpackForestF 0x1f6e87a3b1d4e80f 3 6
def ch_52 : Nat → Bool := dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 7 (dagTraceF m_52 s_52 4 f_52) cur_52 nh_52
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 7 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) (nh_52 0) s_52 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52 : treeBlockF 0 7 ch_52 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 7 → ch_52 i = true := fun _ h1 h2 => treeBlockF_at nb_52 h1 h2
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV5 (kn_nil) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0xc0c0c0c0c0c0c0c
def s_53 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_53 : Nat := 0x404040004040c
def ep_53 : Nat := 0x800000400000004080004000000040008000000000000000000000000000000000004040400040400
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def nh_53 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 0 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) (nh_53 0) s_53 4 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 0 (dagTraceF m_53 s_53 4 f_53) cur_53 nh_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0x50a050a050a050a0
def s_54 : List Nat := [0xa000a000a000a0, 0x1020102010201020, 0x50a0000050a0, 0x50a050a0]
def g_54 : Nat := 0x1000102010a0
def ep_54 : Nat := 0x102000a000001000000000800000000000000000000000000000000000001000102010000000000000000000
def bds_54 : List (Nat × List Nat × Nat × Nat) := []
def cur_54 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x14a59080f 4 15 2 3 9 511 11 2047
def nh_54 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_54 : Nat → Nat × Nat := unpackForestF 0x329c840f 1 9
def ch_54 : Nat → Bool := dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 3 (dagTraceF m_54 s_54 4 f_54) cur_54 nh_54
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 3 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) (nh_54 0) s_54 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54 : treeBlockF 0 3 ch_54 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 3 → ch_54 i = true := fun _ h1 h2 => treeBlockF_at nb_54 h1 h2
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV5 (kn_nil) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0xff00ff00ff00ff00
def s_55 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_55 : Nat := 0x100170013001700
def ep_55 : Nat := 0x1200000000001600000004000000000000000000010006000200060001001200130012000100140010001400
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 7, g_22)]
def cur_55 : Nat → List (Nat × Nat) := fun _ => []
def nh_55 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_55 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 1 1 0 bds_55 (dagTraceF m_55 s_55 7 f_55) (cur_55 0) (nh_55 0) s_55 7 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_55 g_55 ep_55 1 1 bds_55 0 (dagTraceF m_55 s_55 7 f_55) cur_55 nh_55 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_55 : LowerBin m_55 s_55 g_55 8 :=
  lowerDagV5 (kn_cons lb_22 (kn_nil)) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0xf0f0f0f0f0f0f0f0
def s_56 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_56 : Nat := 0x101050103010f0
def ep_56 : Nat := 0x102000a000001040000000c000100040002000e0000000000000000000101000103010000010105010001000
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_25, s_25, 5, g_25), (m_15, s_15, 4, g_15), (m_48, s_48, 5, g_48), (m_41, s_41, 4, g_41), (m_5, s_5, 4, g_5), (m_35, s_35, 4, g_35), (m_16, s_16, 5, g_16), (m_54, s_54, 5, g_54)]
def cc_56_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x886208821178de0781c26c5b06c1a15cd705c15254141501314c13044910405003c4f03c0d207001 0x38091c682f45175273609196bcc352509228d0968a4aa5e4c9222925048a725e31a9148e4946a3a4e15a1068e824650b437d27b490d747e92333ca79a4bcb24e403f18178809c102e001f 10 1023 4 15 11 2047 17 131071
def cc_56_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x38e15402 0x7a515a41623d8e398a3583496341 6 63 3 7 10 1023 16 65535
def cur_56 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_56_1 (Nat.sub p 32)) (cc_56_0 p) (Nat.blt p 32)
def hc_56_0 : Nat → Nat := unpackHintV5 0xfa867d403e50be796da33ec21f61018f43c3c7e1e030a0b7e8daba7d5c029d2329ca94c040349fa0edb446d80350395b9aad80402d9f21cac9a4f0e27800955000940000 0x2f76e799c19e6739ee79abce75ab4067098c0673af5baf555551832f73dd7aabd5b9cef5eaaaaf51830f718aaab5adce9d55a30601ceb5555aab75ab460c560d673aaaaad5ab718316b738ce3018d54185d10621c671a8c06ad18302e3060356338ce3505a3418c1817b9746719d546355a00c62205d3a73aa75554e1c1010 17 131071 7 127
def hc_56_1 : Nat → Nat := unpackHintV5 0x6a00b53ec54d6c3805b 0x4f7bad189d6ea9cebd5554e70183159e6a73dcf339d6ad39c60c0 15 32767 7 127
def nh_56 : Nat → Nat := fun p => Bool.rec (hc_56_1 (Nat.sub p 32)) (hc_56_0 p) (Nat.blt p 32)
def f_56 : Nat → Nat × Nat := unpackForestF 0x891cc48d4168703490527b7145b49ce3416c120290d86bcc352051fa714934bca3424c92028cd0492824504a79c978125e63520493928e4946a083f1d27020bc56840827091d048c8102e001f 6 11
def ch_56 : Nat → Bool := dagCheckNodeV5 m_56 g_56 ep_56 3 7 bds_56 36 (dagTraceF m_56 s_56 7 f_56) cur_56 nh_56
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 3 7 36 bds_56 (dagTraceF m_56 s_56 7 f_56) (cur_56 0) (nh_56 0) s_56 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_0 : treeBlockF 0 32 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_1 : treeBlockF 32 36 ch_56 = true := by decide +kernel
theorem nj_56_1 : ∀ i, 0 ≤ i → i < 36 → ch_56 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_56_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_56_1 h1 h2)
theorem nc_56 : ∀ i, 0 ≤ i → i < 36 → ch_56 i = true := nj_56_1
theorem lb_56 : LowerBin m_56 s_56 g_56 8 :=
  lowerDagV5 (kn_cons lb_25 (kn_cons lb_15 (kn_cons lb_48 (kn_cons lb_41 (kn_cons lb_5 (kn_cons lb_35 (kn_cons lb_16 (kn_cons lb_54 (kn_nil))))))))) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0x3333333333333333
def s_57 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_57 : Nat := 0x113131313331333
def ep_57 : Nat := 0x1220002000001200000000000012000000200020010202020200020000000000000000000110101010001000
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_31, s_31, 7, g_31)]
def cur_57 : Nat → List (Nat × Nat) := fun _ => []
def nh_57 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_57 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 1 1 0 bds_57 (dagTraceF m_57 s_57 7 f_57) (cur_57 0) (nh_57 0) s_57 7 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_57 g_57 ep_57 1 1 bds_57 0 (dagTraceF m_57 s_57 7 f_57) cur_57 nh_57 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_57 : LowerBin m_57 s_57 g_57 8 :=
  lowerDagV5 (kn_cons lb_31 (kn_nil)) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0xf0f0f0f0f0f0f0f
def s_58 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_58 : Nat := 0x10707070307070f
def ep_58 : Nat := 0x200000800000600000004080006000000040008000000000000000001020202030202000104040400040400
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_51, s_51, 6, g_51), (m_36, s_36, 5, g_36), (m_26, s_26, 5, g_26), (m_49, s_49, 5, g_49), (m_42, s_42, 5, g_42), (m_53, s_53, 5, g_53), (m_19, s_19, 5, g_19), (m_0, s_0, 4, g_0), (m_12, s_12, 4, g_12)]
def cur_58 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x214d3495a4d249934a391894678dd537149c01f 6 63 2 3 10 1023 14 16383
def nh_58 : Nat → Nat := unpackHintV5 0xdf00ac66ac00707870006791620b3658006c0000 0x1416ad5d8de342e73c79d2700018d7a0b1ac631ec60f39e3be8671ec73b6005bd608d01aa3540f1e9a00005a802c63468001e3cc7471e 16 65535 7 127
def f_58 : Nat → Nat × Nat := unpackForestF 0x214d18dda4d14dcb4a2918946149c01f 4 10
def ch_58 : Nat → Bool := dagCheckNodeV5 m_58 g_58 ep_58 3 7 bds_58 9 (dagTraceF m_58 s_58 7 f_58) cur_58 nh_58
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 3 7 9 bds_58 (dagTraceF m_58 s_58 7 f_58) (cur_58 0) (nh_58 0) s_58 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58 : treeBlockF 0 9 ch_58 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 9 → ch_58 i = true := fun _ h1 h2 => treeBlockF_at nb_58 h1 h2
theorem lb_58 : LowerBin m_58 s_58 g_58 8 :=
  lowerDagV5 (kn_cons lb_51 (kn_cons lb_36 (kn_cons lb_26 (kn_cons lb_49 (kn_cons lb_42 (kn_cons lb_53 (kn_cons lb_19 (kn_cons lb_0 (kn_cons lb_12 (kn_nil)))))))))) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0xffffffff
def s_59 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_59 : Nat := 0x133717ff
def ep_59 : Nat := 0x4c800000000002400e8000000000204060000000000133212000000000010041400
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_38, s_38, 6, g_38), (m_40, s_40, 5, g_40), (m_45, s_45, 5, g_45), (m_43, s_43, 5, g_43), (m_42, s_42, 5, g_42), (m_12, s_12, 4, g_12), (m_39, s_39, 5, g_39), (m_4, s_4, 4, g_4), (m_44, s_44, 4, g_44), (m_11, s_11, 4, g_11), (m_41, s_41, 4, g_41), (m_17, s_17, 6, g_17), (m_52, s_52, 5, g_52)]
def cc_59_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x940ca023091418a044062010438203f09f80fc07e03f01e06f007803c01e00e047003801c00d436a03501a80d40641a33c0c4001 0xfa380db500ea6004a5002a300d2380d3540dc640ca380c1340b2480223009d680956008a5007b6c0736406a38061340545904b550414602b560234e0194616c5f15c5b13c57114531035f0f35b0e3570bb530ab4f0a34b0834705b4303a520324a01232b4b4fb334bae347a9b43a8a4fa724ba62479ca439b23f9a23b9523790a338594f8394b811477c1437b13f7813b74137711336292f6092b5a127551235104f500474f83f4683a43837338362f82f2e8271701f008170001f 13 8191 6 63 11 2047 20 1048575
def cc_59_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x94250942508521080600801d3741d0741c1701932bca028082200802005314050140500501000400 0x1f36c7ad91e234764d1ca5070d55bb456c965945066d798b466091ae45fb516eb457a314e7b5f9ad6e5b578cd4e234f86d2dfb4774d0da95e68519793e14981624854db14b605098133484ad112248465110a58 10 1023 4 15 11 2047 18 262143
def cc_59_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xe0d9d8d8d1d0c9c8aca8a8a8a88c887a786a6152504948483330292828212004 0xbcd4ad94472572cb6cb0d82b96c70572ab48a8d129a44a45128154664f1b16c9c4d2524092d42616c945724c64908d239348a511913c855a20d6080571893c 8 255 3 7 11 2047 18 262143
def cc_59_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xaca0b801f17c1f0785b36c1a1681735c1705c17054941501314c13040c8820080188601804210004 0x3f9406f06909145ed214194e78285044d6009a3a85d6e06ad60b5a40ebf0157c468f2051ed293d15e782a4ec4d1d4a8ba14969282e0531bc0a371436c268d6949a8af3495285686fa50ddc99b984f7205ae209db412b401f654d8c69718daab1345668bec915d852f30246 10 1023 4 15 11 2047 19 524287
def cc_59_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x88211751d0741a36819164190641906416358151540d8340d0340b22c08320053104401004001000 0x278164d95d9427b244b67492cda519a49324906609f4a352934bd2494a40af4e2439929f2e50e589dca9379125f1e48e381b45a5c8a4891914a2529c4241842a30c4a5e090c094481482f8489d826b601d 10 1023 4 15 11 2047 19 524287
def cc_59_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x8dc62310a844221108763a17cb85c28d40a045a2102802b140a0422010080320a0401201 0x2fd1ede95db72ab7a982f12c5d360b96a170982dd2860352be4a57657ed8abd593db5079645b2c0ae56944b06ab5ed16401d56b56b38bf6315eb8af56146ab27d1e12a91a354246a58b148962a5a2d3a49a6477468de8528c7034 9 511 3 7 11 2047 19 524287
def cc_59_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41606b0cc5981302604c090520211c20841081c2b80646c8190320602c01802c25802c4500a014010c01000 0x6f2456c069b891b2caee495594094d611b609d6b936d98a5ad1435526e9355d168b905564c1d35036ba24b24129a42365b60c96a190973862fefc57dd6bdb6d4b69a56a346d34bfa097b3d2be7252cd48f9891b28afe3957c628f22129a0236215ec32b984552e4aadd125 11 2047 5 31 11 2047 19 524287
def cc_59_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x9c2709866098233759d06c9b06c1926419055150505404c4f43c0f01e0701c0701c0700942008002 0x7ea357db467d2464c04a80b4b7fb477f15e7e1467c93e4b84a390447b8347aa347a13479b537915e7893e4b04a38044378347725c76a44761243704477c5275a53752417495f6312f4a83a38836368347395c731547293c72134718147026c6925c 10 1023 4 15 11 2047 20 1048575
def cc_59_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xd41a8350662c0780300600bc370692d20a412164048090120221231440881101c3304600919200cc18030003 0x8e92a8e1268fc5d8f2518da508ba563b0348aa466593d5e9354d84a3a84686b46892465e1354d04a3a0468745886a589035d8d3558cb478c3458b2598a25189a4b88a49882476724187a3b86237749376512f5d9274c83a398368513e8493c841345c1355d12582a5d6493d5b93583251822417f15d6392f5b1278185c8015c7e9447d93c 11 2047 5 31 11 2047 20 1048575
def cc_59_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xa009e18e88e08c16546406405c45c04e74a24a046244144040240034634020a1c2182180142140140102100008000000 0x9f0447a94a761464e84a3f0469f82e9e8222401d0c0159dc64a53549aa4aa4a47a42468a15d821557994b759476d93d5f1356712da292ba01279e1254e04a448473e8469d0272301f0b8179c1359b8342201f0a8179aa528795f809536d13d5305f2181f0a0172101f09817991356c92d6c23c6b92c9784c9813b971376b12d968372081f0901799c5898c52964508615f7f9539594d6a12d5185f1f81f080171f01f078171e81f070171e01d060159281f9201794a5c94254939289312591924910241d01f05817 12 4095 5 31 11 2047 20 1048575
def cc_59_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x80d001b5342644c8181300600b89702684c085500a0036a684b21421cc344428800e21482803206008401000 0x8d94db112bb0127af8272c01f14817b2a5cb1a51af250ae95d8d14d6f92f589233202f2b01f138172a81f130172a01f128172981d11815ab82fab027ada38ad234ac938ac135aa934aa0342881f11017a845ea91456e92d2781f100175d125a823e8b15da79252681f0f017a5a40a5240a695d2581f0e017a392aa2126a594da312ba19279d8272481f0d817410448a95d769356e12d4503540034a3a5ca34645d134a215ca103ca1354a1c64a083c 11 2047 4 15 11 2047 20 1048575
def cc_59_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x5f58583c2a281a11100200 0x26b20c815d70a5eb348ccc179701f1682f684d6ce1a1681f1582e5907c540bc795db224b1d97238ae5843c 8 255 3 7 10 1023 19 524287
def cur_59 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_59_11 (Nat.sub p 352)) (cc_59_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_59_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (cc_59_8 (Nat.sub p 256)) (cc_59_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_59_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_59_5 (Nat.sub p 160)) (cc_59_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_59_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_59_2 (Nat.sub p 64)) (cc_59_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_59_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def hc_59_0 : Nat → Nat := unpackHintV5 0xee88bba00e88639012e40039000e20236622d900b382cc50930e06c201b0206b907ade06b304ac20aab8527a349d01a6e0695861e86e5f1b176065c0195c143d99810e6000400000 0xac77e3eacfa87aeb5eb2b3cf5d0facac33c31c3ebacf2cb7ebaebaeb3c71ebac77eb2b077caeb1df0cf0d0facf5cfac77d75d34cf3c35c37c71d74000f4004d35e973cf7c71df4003c3d10005cf973eb7df4d35e970df0cf3d003c1000f3cf8f8f3c33cf3cf0cf3cf1cf1cf4d4d4d4d4d4d000000f00041002b0000 18 262143 8 255
def hc_59_1 : Nat → Nat := unpackHintV5 0xba81ae406b781ad40aad082b400ad002b400ad0025a5a7a9c1ea007a801ea007a80198523fa68da2436008b8202c818ac06298189016228187c0e1c82862100c8c02c06018980006 0xaebac2bad0d43eb55d70c35c77c75d4100003d7a5d477c77d014f000f003c3cf05f7d7a5c37c355040f00055555555950d55551d400f00003c0f0002b1012b3db3d7acae8f83ebaebaeb3eabae5eb2b25caeb970cf0d0faebae5c73c7aeb 18 262143 8 255
def hc_59_2 : Nat → Nat := unpackHintV5 0xca900e6579a01633c0261034bf01976042ec0056838aa0194e03290064f8148f0811e001f4243e8006f070de0019414328005e038ba01168062185c42008660f06c300c00c12030240000024 0xb2c71c71c32cb0e0134d31d353402c00b2cb2c71c787871c31cb1c71c31c71c71c71c70134d34cb2cb2c74c7471c7474c71c71c0000b01c07002b00ad7975b4f2b2b943ebaeaeb663caebaeb0aeb4350faeb1d470faeba50fad93caebab0f579f1d753cacac350faeb7c77d2d3caeb1ebad1d1cf2b 19 524287 9 511
def hc_59_3 : Nat → Nat := unpackHintV5 0x888093fa251fc804fd00a7e8003f4001f7814e94947440339b039cd800d548c5de662902f948000a34065000d20a3b1048048100a408001fe030da12855cba28216140008970484ac06254010ec1f05510800154 0xf0e36c30c07a1cb2c30c71cf3c32c32cb0e9b2cb58fa0c40b1cf2c7acb2e871c300cb3cf4cb4cb4d353471dad4f3cf4cf4db6db0db0c1b1c79ae6934d34cf4cf4c30c30c34c32cb2cb2cb2cb0c30c34d4d4d3d0c34cb4b5ba6d0f1b0db0d4072c72c32cb0d36c30d34c30c3436b2cbacb8db2d8db6e33d33d340f4c2db2cb8cb8cb3cb4d3534db430c34d34f534d2cb2da6b0e302cf2cb2e933cf4c32cb0d534cb4c76b1d1c73db3db0db0c02db2cb3cb0cb2c34db4d33cf4c34c32cb4eb5e5cf6cfacac77e8fab7e3cf5d70c37d7084d34d4d4d30000f3c5e973cb0c02cb4d4d4cb001c00b0f073c2cb1df1df1cb1cb3cf8f8f3cb0cf3cf2c30134d34cb4d32d34c71d34cf3cf4f4cf40000f00ac1c01c0f00 21 2097151 9 511
def hc_59_4 : Nat → Nat := unpackHintV5 0x85e0042e009f78fcfa00e7d0003b8181dc000e58446ce2f32720191014c8800644002ee1a177000b30444ae75216208e6128724063760e196128a61282357e11a00049220200240f0080640a02f018020ac00008 0xc31e872c30c71c32cb0e9b2d40b000076b56db6c36c36c71e6b9a0004c59adb435b51d54c005b0dad52db6434b475430001ba6d472c72db6c30c3436b2cb000c4c26b2cb2e832cb0d476b1d1c72c00051dad90d2d2d52c003cf3cf0c30c300b2cb2cb2cb2c30c30d34d34cf3cf3c30c30d30cb2cb2db0db0cb6cb0cb2c36db0c32cb00000005db3cf806d71df1d74d34d4d08ac3c03c0c3c0eb0bacae5cb1df3cf5c32b3c3c2df2cb5e970c02cf2d34d4d0b01cac02c0c3c3cf3e3e3db0db0c02db2cb1cf3cb1cf0cb2c34d34d33d33d3cf3d0d34d34c34cb2d30f00f00300c000ac3c02c03c03c0fa3eb6db03cfa8036c71d34cf4d34d353473c7032c70e1c32db01e872c36cb6e38cb2b 21 2097151 9 511
def hc_59_5 : Nat → Nat := unpackHintV5 0xaea4457002ab601154c32a9e0454c01aa480d51c04a68134ca35205300fe0247ee013e4099ef018f74027503539e051ac914c588654c702662013280489c7c41e1820e0090580c7d42c2ae9e1211b0571cc0015c 0xb2c7a1e0c31c72cb1cb2c77d4b2c71cf3e6bac971e971ebad30f2bae47a8754c4c2cb2cb3cf3cf2cb2cb2cb1c71c71c71c741c74d4d2d2d3c3d1d1d2cb2cb1c71e1e1c70c72c71c70c71c71c71c72c71c7554b4b2cb471c71d51dad3130b0b2cb071cf01c70701d3071c44caeb5e5d6dab1dfad983adf9575c30df5e7e5d555534cf0f136baeb5e972d432c32cb2d555476b3c3c2cb2d34c77cb1d7a5c32cb0d56b1d1d2cb4c73c3c2cb1df1df1cb1cb555555476b55950d555553130b134c4c1c44504f0803cf5d71df1df4d4d4d3008080f0f3c975df080df0cf3d34d34d35343c000f1f1eb2df2cfac5e5c71cf1ebac05e973cf3c33cf0d7a5cf1cf3c73cf6db4d3a4d33cf3d3d33d4d34d34d34d302b202000f0003c029b6e0036db0e93934d35343c00009baa83aa87aaaa9b6db6e4e6a64ea934d34d34d34c82002b003c00000c30c30db0e0e0c300b2cb2c30c30c30c32c31c30d34d34c30c30d30c30c3434c34b2cb2c000ac0c00c0000 21 2097151 9 511
def hc_59_6 : Nat → Nat := unpackHintV5 0x8da0343c18a19028fe07476a433ad041d6800eb40072e16394019b30b8d54226a403351009900c4c3c225d8232d60b14c0f8a480c4f4182750293881096032468241a5478ab93840ca81824203c428020e000008 0x1df1cb2c72e870c351c71cf2cb1ebab2cb7e9f830c71df96471df6b7d3cfa0cbadf0cb7c71c350d1c72dacb4b2cf2e9bac30e6c71cb2eb1c71c72e870c351c73c72cb7c75f5eadf975d75c30df5e6571d1d03c3c1d7d79fad75c35e30df5d73c3c477c37cbac75e977cb0d0d2cb1d1d2e31c73c3c2cb96b7c75e1e97aeb9aeb077c7a5eaeb4c1df0cb1c30e3aeb1d32cb1df1df1cb1cb7e9f2c37e32c3554b5476b1c751c71d3130b13134c1d3133c133c11314b2cb2cb0cb0c71c71c7879555553130f0f0b2cb2cb2c71c71c71c71d55555553130b0b2cb0707112aaa871c71d5554b55620b0b2cb0707110b2cb2c71c71c71c71d5554b51dad5555954354b547554c4c2c2cb2c1c1c44504f02cb1c71c70cb2c3965d752cb3c3cab 21 2097151 9 511
def hc_59_7 : Nat → Nat := unpackHintV5 0xe723d72f0537610db980cdca016b01ab25199790cca4ebd5270029181141c389864447b241fe9f8ec4987620039e099c9030dbc4663a523010e12a2b4808a43804216e2908c1582f8b406a890160f80a8040002a 0x55e5c36c3971df1d75ae6538f0f1b4eb6bad7a5d75d477c77db59ad554f0f136d34d35eb975df5e970df0d5555534d33c3c5e975e976db5566b55555435555475553213134c4c4c44504f00c30c33cf3cf403032cb2cb0c30c32cb2cb4d4d0d0d3d3c2d2d0c30c30db0e0e0c354b2cb2c30c30c30c32c31c30db5b50dac30d430e32d2d4c4c0c3030c34c0c30300c33c0b0b1130f0b6eb2d5e7c75d5576d79b9b5c77c75d6b9559534cf0f1b4cb7cb2d7a5c32cb0d56b1d551d4b2d32cf0f1b0db0cb6cb0cb2c3556d436b55552d55958d551d554c4c0c4d3130b111413c176d75e59b5c77c75d7a6eb0e570c341b6cf0f2b4badbacb5df0eb972c77d78d70dbacb4b7cb2d7a5c350cb7df1c72eb0c74b0c34b2c0f0f25d7a0c38ebab4e38db9ba36c36c354b6cb2c78e32c78c32cb0d6db6d0c30c30d50dad2cb2d4c4c4cf04cf00d3134c4c2c44c0c30c32cb2cb0c30c35555554c4c0c0c30c2c2c44aaaa0c30c355550d55880c0c30c2c2c440c30c32cb2cb0c30c35555554c4c0c0c30c2c2c440c30c31c71c70c30c355550d554c4c0c0c30c1c1c440c30c32cb2cb0c30c355555553cf3cf0c03032cb2cb450c30c32cb2cb0c30c35555436b555b55954352d5475554c4c0c0c30c2c2c4451053c2b2c77d7976db5ebab1df2e9fab 21 2097151 9 511
def hc_59_8 : Nat → Nat := unpackHintV5 0x9181891800918008f0288ac448882481c6c81a027c8527b41473c7871a22718026be5a69c2265e3e65c02656066243252afa4a684426803a2842c4de2646025c081f468150a4054fc02c2802a020002a 0x1c72eb0c31cba6dba5c30ea1c75a3e6db60d75d7ae995d75d71df1df99a6e33c3c6db830c71db6e9b5ea56db8fac7ab0c31d75c71db6c751d5ea976b5d3cf5d75e47ae5d77da437c35d77e640f0f25f5c75eb6df1eb972df2d7ae5e5c71d76c7aeb557a5d78db0d70d7a5d71c75db6d9ae96a6d5534c93133c133c131313131132a9b6db6ea836db0d555555b4d3130f0f2aaa9b6db6d55555562131b4d31313112aaa871c71d5554b55620b0b2cb0707112aaa9b6db6d9ad5555b55594355b55547555884c6d34c4c4c44504f0a6db960db6c3a7d756db3c3cab831ea9b6e6dba976db5a6db3cf4a3cf3cf6cfaa3cf3cfaa6db6db3c3d994d4d4d4d566eaa0e6eaa1eaaaa9b6db6ea959adb5b6db568f0a2093284c6d36c4c4c44caeb7c77d2da5ebad1d0c7 20 1048575 8 255
def hc_59_9 : Nat → Nat := unpackHintV5 0x911002438068d81b2350088cf02a10d187f9251e0cec6bb6419c0965b55d95a49855f0513c8da4e90493a4004e1041378064703710d8743785f0c40d02bc2a09a8a420c2f082406200048630e81163b0109a80031f800006 0xf1d470e38c3965d77df5d73cf0f0ac0f178b8b2c71ea871db2c72db1c71cb0d72c3a97a5cb2df1c77d7575720b07c1c5cf03c017a5c350c76c30c7475b6c30c30c71c30cf0f030c30cf3cf3c300c0c71c71c30c30c71c7134d34c30c30cf3cf3c71c71c30c30c36c383830c30c31c71c71db0c31eb0c30c30c31db6db6c30c30c30c3430d1c71c76c6c0c0c30c0c30300c33c07070030c7a1cb0c32cb2d72d75db7cb5d8d2cb3c3c2c32c31cb6c72cb0c31eb1c70c32cb2e2e2c71c70c30db6c32cb0cb1c72cb2e32d2cb2d1b030b2cb0b070b3c0b2c02a831c70ea832cb0ea871c71c30b2cb2207070075cf0b0cb0c71e2cb87876e1c71c30c3a1c30e5db6d75d475c6c2cb3c3cadb1e1d72b0cb2c30c31c70c30c76c71c70cb2c35d71c71c71c30b2cb1701c1c05e972d2d0d0d1c72cb1c73c3c2cb01c71e1c7871cb0cb0c71cb1c76c71c70c30c30c71c30c7adb6c71d1c71d0cb2c31c71c71c6c1cf01c700c2cb2c1c1c00c30c31cb1cb0c30c35db6d70c30c32c71cb5c6c0c0c30c2c1c0aaaaa0c30c30c3aa0c30c32c71cb880c0c30c2c1c00c30c31cb1cb0c30c35555554c4c0c0c30c2c1c442db0c35e970d432d4b6db6db0c30c32c71cb0c30c33c3c0ac77eb0c30c31cb2c72db0c30c30c36db6db0c30c32c71cb6c6c0c0c30c2c1c00c30c31cb1cb0c30c33cf3cf0c03032c1cb4d34d30c30c32c71cb3cf3cf0c30c31cb2c72db0c30c30c31eb0db0c383830c30c30c32c36db6db0c30c32c71cb0c30c3430c35b1b03030c30b07030c0c030cf000d43570eb5c3a1c76d7a5dad74f3db6eb 22 4194303 9 511
def hc_59_10 : Nat → Nat := unpackHintV5 0xf284c762193771d1a58b0c64645ea242c816963406b0c075223225e198ff1807604c2fd5995e9009f4803f8811bc2009e200488341a0520b20f0209c41040006e0a025090128000681602e030170000085800002 0xaa838baa0db6c3aa836db0df7e2031b6db1f00995d6d1df1dfaa6db3c3c6db0aa9baaa0eba1eaaa2ea832cb0e9a9aa836db0cb2e3c2822031b6db02c00e832e8b0c30e5e970c30c32cb2cb5c80c0c30c2c2c00c3a0c31e1e1c7830c35e970c30c31c71c75c80c0c30c1c1c00e832e8b0c30c35555554c80c0c30c2c2c440c35d57962cb1cb1cb5e970c30c30c32cb2cb0c33c3c0ae5eb0c3a0c35e97830c32e2e2cb0c30c32cb2cb5c80c0c30c02c2c0e833c8f803032e8b0c30c32cb2cb4e930c30c33cf3cf2cb2cb0c3aa0eb0db0ea2e2e2cb0c30c30c30c32c30c70c35e970c30c30c30c3430c34b2cb2d7203030c3030c0c030cf02c2c05d572cb2c32c31c7995d71c72cb1c73c3c2cb01c72cba2cb1c71c31cb1c3a1eba1c7a871c71c72d7a5c71c7471d2cb2cb1c71c71d72071c073c0b0b2cb0707022c7aa1cb870cb2c3a5e7c75d4b2cf0f29b6da436db0d757e9b6df7e9b6cf0f02aa2e87aea872db1db2ea83a9baaaa8b6db2df1c77ea69882c6db6c7c1ca08f00992c32c32e1d1da872c7aa1c73c3c2cbaa2eaa0e2eaa87aaa1c71cb1c71e9a9aa2cb2cb1c71c78f0a0882c2cb2c1c1c00c39e72cba2cbaa83a9eb2cb2cb2cbaa8b2cb2d75e20b0b2cb1700872cb0e6c70d72e1e0e1cb1d70cb0eb5cb1e872c30e0dba0cb0cbadb8d8d2cb3c3c2cb2ebae7977d747a1e7ab5cac7a1d5df5d70 21 2097151 9 511
def hc_59_11 : Nat → Nat := unpackHintV5 0x75d4e6647c504b0305001d4981b410048b602c0e02c0000c1000006 0xc30e83ae830ea2cba2d72c76db2c75c32cb0d7a6d75e36d6db5d0db6c32cb5c85cf06cf00c6db6c0b0039a4350e2c72c72e830e8b2c30cf0f2aaa0300c0ea830c30cb2cb2ea830c30cf3cf3cb2cb2e83aeaaa83aaa2c30c30ea2e1eaa830c30ea692cb2cb880c0c30ca20a3c0b0b02a870c70ea871c71ea832cb0c70722030b2cb027cf20e1cbaa832cb0e1eaa0cb2c3a9f2cb7df52cb7c2c3c3cacb879f2b 20 1048575 9 511
def nh_59 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_59_11 (Nat.sub p 352)) (hc_59_10 (Nat.sub p 320)) (Nat.blt p 352)) (hc_59_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (hc_59_8 (Nat.sub p 256)) (hc_59_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_59_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_59_5 (Nat.sub p 160)) (hc_59_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_59_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_59_2 (Nat.sub p 64)) (hc_59_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_59_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_59 : Nat → Nat × Nat := unpackForestF 0xb4fb3935b383400b4baea5cb2125aea51af92bb083caf927af827aea50ae95d00b47aa238aa234aa138aa135ab02fab027aa134aa03400b43a914500a4fa7a3ea792500a4ba695d00a47a594d9d3549d2479d246a3a5ca34649d12ba215ca0c64a1354a083c9d1279e82e9f0449e8229d1259dc649d02700a439b9359b83400a3f9aa5200a3b95c589913595c529693b9784c969379683795c509594d00a379125c9125491128911259201f92017911249102400a338635d8dc5d8da518e12a8e1268da508635586347863458ba56862598aa46862518624b8924686249862478623b86c5886a58862370094f8413e8413c841340094b81a5182a5d81a418185c009477cb4b8015c7cb477c95e7ea357c9467d3467d2467c93e009437b8340093f7a2347a13478b537895e7893e0093b74c527625c762447612474a5374a417495f009377195c719547193c7193471814009336345f7026c634576f2456335e6e246633526334a6ac526b93a6b9366ac506aa4d633466325f68b5568b456325e6325763252632476324665b606315f643506425c63157631470092f6115e6115c611540092b5ab525fa3d5aa525e2605e2585a95f5bb605bb505ba605ba505a9575a83c0092755c5f5916c55c5757b5557b455595e56b56559465593e0092351b455424651a4951a3b524585225851a370084f50a51008470083f4f02c4e925472434d2514d2494714f4c13e471434713b47137493524925e492524712f4815e47123470360083a444524525c4524444253442410083743129343433f4513f14e3f13540a413f1343f9403f015341433e2343c2523c15e3c8143c152341333b1343a1513a1493404f3402d340273794c3781437143340253613434a523495e349523401f008363045f32a6c3045731355313453025e302460082f2f3520082717c5f2d94417c5b2bb6c2bb602b96c17c572934829344292442914417c532815417b5f2713417b5b2616c17b572515c23c6423a342393417b532294417b4f17b4b20568205602015c17b471db6c1db641da341d93417b431ca501b3551b3451b2591795e179461835e1945018346182461793e0081f0145f162480145b1436c14360142600145711b4811b4411a48119440145310a580135f0fa380135b0ea60013570c4640d3540c2380c134013530b2480134f0134b08d6808d6008a50013470636c06364062380613401343044590435504146012520124a01b5601b4e0194601232008170001f 9 11
def ch_59 : Nat → Bool := dagCheckNodeV5 m_59 g_59 ep_59 4 15 bds_59 362 (dagTraceF m_59 s_59 8 f_59) cur_59 nh_59
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 4 15 362 bds_59 (dagTraceF m_59 s_59 8 f_59) (cur_59 0) (nh_59 0) s_59 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_0 : treeBlockF 0 32 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_1 : treeBlockF 32 64 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_2 : treeBlockF 64 96 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_3 : treeBlockF 96 128 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_4 : treeBlockF 128 160 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_5 : treeBlockF 160 192 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_6 : treeBlockF 192 224 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_7 : treeBlockF 224 256 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_8 : treeBlockF 256 288 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_9 : treeBlockF 288 320 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_10 : treeBlockF 320 352 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_11 : treeBlockF 352 362 ch_59 = true := by decide +kernel
theorem nj_59_1 : ∀ i, 0 ≤ i → i < 64 → ch_59 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_59_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_59_1 h1 h2)
theorem nj_59_2 : ∀ i, 0 ≤ i → i < 96 → ch_59 i = true := block_join nj_59_1 (fun _ h1 h2 => treeBlockF_at nb_59_2 h1 h2)
theorem nj_59_3 : ∀ i, 0 ≤ i → i < 128 → ch_59 i = true := block_join nj_59_2 (fun _ h1 h2 => treeBlockF_at nb_59_3 h1 h2)
theorem nj_59_4 : ∀ i, 0 ≤ i → i < 160 → ch_59 i = true := block_join nj_59_3 (fun _ h1 h2 => treeBlockF_at nb_59_4 h1 h2)
theorem nj_59_5 : ∀ i, 0 ≤ i → i < 192 → ch_59 i = true := block_join nj_59_4 (fun _ h1 h2 => treeBlockF_at nb_59_5 h1 h2)
theorem nj_59_6 : ∀ i, 0 ≤ i → i < 224 → ch_59 i = true := block_join nj_59_5 (fun _ h1 h2 => treeBlockF_at nb_59_6 h1 h2)
theorem nj_59_7 : ∀ i, 0 ≤ i → i < 256 → ch_59 i = true := block_join nj_59_6 (fun _ h1 h2 => treeBlockF_at nb_59_7 h1 h2)
theorem nj_59_8 : ∀ i, 0 ≤ i → i < 288 → ch_59 i = true := block_join nj_59_7 (fun _ h1 h2 => treeBlockF_at nb_59_8 h1 h2)
theorem nj_59_9 : ∀ i, 0 ≤ i → i < 320 → ch_59 i = true := block_join nj_59_8 (fun _ h1 h2 => treeBlockF_at nb_59_9 h1 h2)
theorem nj_59_10 : ∀ i, 0 ≤ i → i < 352 → ch_59 i = true := block_join nj_59_9 (fun _ h1 h2 => treeBlockF_at nb_59_10 h1 h2)
theorem nj_59_11 : ∀ i, 0 ≤ i → i < 362 → ch_59 i = true := block_join nj_59_10 (fun _ h1 h2 => treeBlockF_at nb_59_11 h1 h2)
theorem nc_59 : ∀ i, 0 ≤ i → i < 362 → ch_59 i = true := nj_59_11
theorem lb_59 : LowerBin m_59 s_59 g_59 9 :=
  lowerDagV5 (kn_cons lb_38 (kn_cons lb_40 (kn_cons lb_45 (kn_cons lb_43 (kn_cons lb_42 (kn_cons lb_12 (kn_cons lb_39 (kn_cons lb_4 (kn_cons lb_44 (kn_cons lb_11 (kn_cons lb_41 (kn_cons lb_17 (kn_cons lb_52 (kn_nil)))))))))))))) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0xffff0000ffff0000
def s_60 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_60 : Nat := 0x117000013370000
def ep_60 : Nat := 0x1220000000000000000000000016000000240000010600000204000001120000133200000114000010040000
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 7, g_23), (m_31, s_31, 7, g_31), (m_48, s_48, 5, g_48), (m_33, s_33, 5, g_33), (m_49, s_49, 5, g_49), (m_32, s_32, 5, g_32), (m_46, s_46, 5, g_46), (m_47, s_47, 5, g_47), (m_38, s_38, 6, g_38)]
def cur_60 : Nat → List (Nat × Nat) := unpackCursorV5 0x13098486411188442030078bc1e0e1703443801 0x3240cd51d40795092028d3e4fe92f647b90e94f952e147650d52f44acd27148c01f 9 511 4 15 10 1023 14 16383
def nh_60 : Nat → Nat := unpackHintV5 0xacedba17b7945d28d76e816c1726f0636f054fe74cc833cffd318b723ddb16bd20fd6e03cc10003c00000 0x152aaaaac3b631d0c6355558c6b39cef3cce7558e7800000040000015561dbaa55872aaad4318c6ab5553e9d000800000000054aaaaaa319c63a872a8e6318c6378c631aac73c0000002000000aab0edaa8c631aad500080004002aad54395563caaab52c635aad554fa74002000000045c0016b5aaaaaaac635aceb9675caa31bf631ad6318d5566f9bc00000040000015546318d54637ec6318d55ef7bc631aaaa8e18c671c358c0040000000000631aaaaaa8ce38631c318c6aa31ac6318c637aacdf3780000008000002aa8c631aa8c6bdaaad6b58008000002c55558c6b555ac6318deaaaf7bdeb5ad555572ceb3ae18c60020000000002cb82ad52acba874aaab54df37aaad3f755470010000000000553c79555ef7bd569fb39e8eb38ce339d5554e73d40020000000000aa739c6719d6aaaa78f2a9ce79be6f55aa8e7a780080000000002a9ce73aaad52ac7b60020000010ab54aaaf7bdeaab554f9750e95556a8f0008000000001170555555001000000 20 1048575 8 255
def f_60 : Nat → Nat × Nat := unpackForestF 0x193c64b191f354190c54f152c547795054314bc52b149ca34148c01f 4 10
def ch_60 : Nat → Bool := dagCheckNodeV5 m_60 g_60 ep_60 3 7 bds_60 16 (dagTraceF m_60 s_60 8 f_60) cur_60 nh_60
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 3 7 16 bds_60 (dagTraceF m_60 s_60 8 f_60) (cur_60 0) (nh_60 0) s_60 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60 : treeBlockF 0 16 ch_60 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 16 → ch_60 i = true := fun _ h1 h2 => treeBlockF_at nb_60 h1 h2
theorem lb_60 : LowerBin m_60 s_60 g_60 9 :=
  lowerDagV5 (kn_cons lb_23 (kn_cons lb_31 (kn_cons lb_48 (kn_cons lb_33 (kn_cons lb_49 (kn_cons lb_32 (kn_cons lb_46 (kn_cons lb_47 (kn_cons lb_38 (kn_nil)))))))))) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0xffff0000ffff
def s_61 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_61 : Nat := 0x1757000017ff
def ep_61 : Nat := 0xa8000000000000000000000040000000e8000006020000060000001202000012000000145400001400
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_39, s_39, 5, g_39), (m_13, s_13, 4, g_13), (m_35, s_35, 4, g_35), (m_30, s_30, 4, g_30)]
def cur_61 : Nat → List (Nat × Nat) := unpackCursorV5 0x4080e5c3862c0681 0xd2e3d73e9f747927a91cc6e01f 7 127 3 7 10 1023 13 8191
def nh_61 : Nat → Nat := unpackHintV5 0x3287ca03005b21ec80a61a8820144000 0xe9ee8fcdd3a5555550400000001 14 16383 7 127
def f_61 : Nat → Nat × Nat := unpackForestF 0x3a7e970e8e64f7ae191cc6e01f 3 10
def ch_61 : Nat → Bool := dagCheckNodeV5 m_61 g_61 ep_61 1 1 bds_61 8 (dagTraceF m_61 s_61 6 f_61) cur_61 nh_61
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 1 1 8 bds_61 (dagTraceF m_61 s_61 6 f_61) (cur_61 0) (nh_61 0) s_61 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61 : treeBlockF 0 8 ch_61 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 8 → ch_61 i = true := fun _ h1 h2 => treeBlockF_at nb_61 h1 h2
theorem lb_61 : LowerBin m_61 s_61 g_61 7 :=
  lowerDagV5 (kn_cons lb_39 (kn_cons lb_13 (kn_cons lb_35 (kn_cons lb_30 (kn_nil))))) rc_61 nc_61 (by decide +kernel)

def g_62 : Nat := 0x1171757133717ff
def ep_62 : Nat := 0x122000a800001640000004c800160040002400e8010606020204060001121202133212000114145410041400
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_60, s_60, 9, g_60), (m_55, s_55, 8, g_55), (m_58, s_58, 8, g_58), (m_59, s_59, 9, g_59), (m_22, s_22, 7, g_22), (m_56, s_56, 8, g_56), (m_57, s_57, 8, g_57), (m_28, s_28, 7, g_28), (m_51, s_51, 6, g_51), (m_31, s_31, 7, g_31), (m_61, s_61, 7, g_61), (m_53, s_53, 5, g_53), (m_47, s_47, 5, g_47), (m_37, s_37, 4, g_37), (m_10, s_10, 4, g_10), (m_23, s_23, 7, g_23), (m_3, s_3, 4, g_3), (m_50, s_50, 5, g_50), (m_13, s_13, 4, g_13), (m_36, s_36, 5, g_36), (m_34, s_34, 5, g_34), (m_14, s_14, 4, g_14), (m_33, s_33, 5, g_33), (m_49, s_49, 5, g_49), (m_27, s_27, 4, g_27), (m_29, s_29, 5, g_29), (m_19, s_19, 5, g_19), (m_38, s_38, 6, g_38), (m_20, s_20, 5, g_20), (m_54, s_54, 5, g_54)]
def cc_62_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x881410e0810018003f05f80f817c03d05e80f017803b05d80d856c03505a80d016803305980c816402d15680b405a02a0c0d2001 0x2069e0fb4308a2f84314c1e0480e05e0682f030150160880a06c0482202f17c158b609c57046298201780e0a806044028360101100d8be05c5b0262b80f14c060bc0245f00e2980417b088bf81c5bbfe2bde514eea6bf7135bb55abd92d4ebe69f5d34bad9a3d4cd0e994bf43a5b9bd2bcc294e2949f0e24b82923bb490dbd47ed923b6711bb108cd6e2bea61574d4a79f251cd327e5a1372449786849c2a0b61205308c2583a10c1b0760c83303c1580a08c010360003f 13 8191 6 63 11 2047 21 2097151
def cc_62_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xd41a0711e20c4180700600bc33a10ba003c2780e09c0342680c09801ca380608c01422802184004200400000 0x1f250406d87ed70f49a1d570378c088dbd0db5a0b673c6c6765bce4b39c13f3626f1f5ae1ab1c1c6f818d6fd19dea31bb45f718a6dcdb9b5b5b6363696c4ced7979a9ad35258696acd0d4d37a82674c4be9093d15239a956330a862110bc3616844328be6116cba2b964532b0bc521109c221445b268a64a17880120f824 11 2047 5 31 11 2047 19 524287
def cc_62_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xcdc8c1c09d9891908988887370705b585858434040402420200b080808010000 0xcb5ff257bc55df0573be9faea44b918ea36f9ad764b4fb649aca7eae9faad69a8d49d956a55c68b607255a7c7b9d1de6b60971fa546e92d89c1668f5ca35626c59a1470 8 255 3 7 11 2047 18 262143
def cc_62_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xd2e47218184402010069b41a0d0682512090391c0e0703810c8031180844020088400200 0x1015c5fdb8313534e4be82558fcb21e95678adcfb1b9a1b7303635c6c4f8d21ed221e16679afcf11c9ddac3ad7e748fce6d21c922384596f4aad75a545b2b525e686c6cc9d18d4630a54 9 511 4 15 11 2047 19 524287
def cc_62_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xa0280a0253942509425085210806007c55a541324c1304c130485204811129ca0280551401400400 0x9eafd3b1ca712a4d57e998fd30d125d224ac59936c7655aeb6b1d546fa88d74719e7e31cdc5f968a7289ba492f35b70906b11051220a24735a8d6b118d5a2d2d45256894a90e55a16b4bac52846d0cad4d10ab4146e646c69e9bd0cb321164 10 1023 4 15 11 2047 19 524287
def cc_62_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x8c221881f37c1f07c1f07c1a54a1204451044110440d4340d028ca024490240721c0521405014005 0x17c912f6b95b35cbc4b9755aee5af5c352b74bd6c94b42b5e6462c88a58c9af0933dfa5fbb4a76a936cd2a58b56b06a95e95ab92a565699a8a556992a63753b56a64ad4b5c6913e4ed6ea28dd42d124d3750244 10 1023 4 15 11 2047 19 524287
def cc_62_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xa82739c2619824290240902408115b541504511044110314c0300c0210801c4701c0521044010004 0x37dbf6b35cde6a9b89936e3f6d244d8ad7af58f5a2f6ac52f6ad7e758fc1b77735eea4dfce9af9133f0263dd4bfb294f511ae7c70d28b1a2956e926e7d69ce6bd8297ef529e6a35b847b968ef291be4a35c74b98ad7f11a9e1c70c18e581162e2285ba4c 10 1023 4 15 11 2047 19 524287
def cc_62_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xa85502a0502a00c4180300546a8150243480900e21c0288500a01401c6380700a2140280310600c018001800 0x7fc601b1267eb6c7e26c99d629836f9736b93367903638f26f8da6b8926787a6383a5d8223f80a3b7f2377da331a9267d0507c3547ba556c2357ab547a2556ba357945978a556fa4f6da4375a6f71a636b24d77a4576d697636475b5e74a6e742447357172b7c71c6e7126e70a44 11 2047 5 31 11 2047 20 1048575
def cc_62_8 : Nat → List (Nat × Nat) := unpackCursorV5 0x88e20882027c5e1745c1701b1685554c9304c10340100401003c4f03c0781c07010c401002208002 0x8fd6884a5c1d9268ee708e26c8cb588b3448cc5c8ab408b34c8ac548d34f8c34b8bb478a3431d12689d701c9268436c88a6c8825c85b6c8736f86b6b863678536384a6e8426282a3e7ea328336c82a6c1c12681a6c8125c8036b1b926 10 1023 4 15 11 2047 20 1048575
def cc_62_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xbc2f0bc2e1b82e0b46d0b41fe7c1d2741d06519058d60581425014044d10314b1248901c85201400 0x9e26c9ca6ca5462a436fa336ba1b67a03639fa6f9f26b9ea679da6333a4d9d23f9c23b9ba379b2338ea699a2459956898a658725d2212686a6d97a352192696a4f962439524b94a472112695d709447093a7d8625d209262012685a5d1f926919361f124913601e92492b6c9235c8526d90a351e126 10 1023 4 15 11 2047 20 1048575
def cc_62_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xf0783c1b3d86c32590c85cae161b0546a141a04891480389c0c26028940a032180c00600 0xaf47caec70ae27cad37caca7cabd71ab37caa27ca9470a8254a7d71a727cb5461b3b4fb1b43afa6dada4fac243aaa3fa9a3ba8a37a6a33a5a45a4a65a3a35a2d70a227da136c3425da0a35 9 511 4 15 11 2047 20 1048575
def cc_62_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xac2b0a0e80a026298251942509422388220881f34f1304c130358d0340a3280a0280641806018006 0xbdc69bf461beb43bdc68bd464bc264bb569bab64ba35eb9569b8a64b825ec3c5bc2c59a5451c13433725dc025bbfa57be255bca4fbba43b9a3fb7a33aea4db6a4bb6247b5a45aba3fa7a33b4c7cb0a7db4245b337cb2b6cb027db2235b1459aec51b0b4fb0343ae24ead242 10 1023 4 15 11 2047 20 1048575
def cc_62_12 : Nat → List (Nat × Nat) := unpackCursorV5 0xd03229b2609465088e207cdf0785c2701c0689a0681735c1705c14326c90240541405008c2000800 0xcfd6bcf45ed7d6bd6d67d5462d3c52d2a67d125fd0257a89679b95f7f157ce94d22927cda64c7a6ccca54c6125cba7cc926cc725cca947ca254c5925c9465c8c59c7d6ac7566b816fc656bc5d63c5252cd56fcc56bcb567c9d63c826ec6a5eb796fa69679b15f7d957c4925bda4dc3245bb23fb9233c2364bea65c1a3537a64c0a5e 10 1023 4 15 11 2047 20 1048575
def cc_62_13 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc71c230422841006003e1744e81d03624d0981301e43c0704e01c024a480900851001843006004408000800 0xe0d6be0563dfb52ec56fead6be9d67e8563e736ee6b5ee526fe3a67e225fe1257b996faa9679d15f82157df13524127de254da925dd27cdc4599c95d81155dad6bda252ddd6bdcd67dba6edb25ea99679c15f80957d9925d6470d8c58d8155cf94dd7470d6569d5b5ed3265d225f23927d1a5dd0a55d4a37d413723127d3460d2472d1c60d0c50 11 2047 5 31 11 2047 20 1048575
def cc_62_14 : Nat → List (Nat × Nat) := unpackCursorV5 0xd83b0350d0d620c0170ae05c0a0d402614c098101a00308394700e0144280500620c01801102000200000000 0x3be5b9dd2dcf645b7aa29bd2d7de86b6f3357795a9bc8d3de2686f095b780a98b650dde276ee133822b5c0d58e048df01c6b80233bf918dfa8befc4537d5373e6979772deac167364a797651ded24aed924765b23aed51d62aae0935751be3a4d51d12aae013573e2cb90995c649e2592772d37b8a975c34aaba16f12893b995a5cb6bce4d71721b638cdf9c56d8e1b5c 11 2047 5 31 11 2047 21 2097151
def cc_62_15 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0a2848072695a58584a484140404039381c1818111010100908080801000000 0xff93fff137fa26efea44f7125f2924fdb54f2124f1924fcb44f1124fbc69fb459fa363f8570f946ff8c6bf7c67f7463f5a44f3c60f1a34 8 255 3 7 11 2047 20 1048575
def cc_62_16 : Nat → List (Nat × Nat) := unpackCursorV5 0xb8ae0a56729c26198260946509425085210806008020074dd04ad20390d12c8b020c621084001000 0x881a243e912278df1346b88a33c3d18e1d4dd0726583d22c355a217ae10ab6c851ae3e89b61346908c6883eb841d5820d8e10dd62865b7c30dae166cf0936384137c1899df34bae123f6811bc16142096a8fba7c7d92a3d8491eb24903b547a89240a991f224af49247c492bd0491f024af392480ab84029f1ef24af3124 10 1023 4 15 11 2047 21 2097151
def cc_62_17 : Nat → List (Nat × Nat) := unpackCursorV5 0xd03a0321640c43882e1dc0b43682d0562a8350290d20a41482905019082fc500811002003086004408000800 0x11fc5c8f739474d023b6b91d454715b64728d237ad11ad708d23609b1b2316e71636c8bdb7c5cdae2d6cf15b63982b5cbf58e5e8df2e46e96635cb119e548c729c6293db7c9adae496cf2236390dafc84d4e4069f1f34b8f1a3c70d0e364df19a677111fb448dd792dead9678c8a78ce5363028f151453749f97e4dc4c24f142648952b4495c2234f910a3e 11 2047 5 31 11 2047 21 2097151
def cc_62_18 : Nat → List (Nat × Nat) := unpackCursorV5 0x9cce255219042e03007cbe1c6d268341a0b45826d30984c1d4d268341a06e29108801601 0x96e3c4bb1a6344cb2bc6496ebe46b1b25a4892b46095e364ad5d2378d92aa447da2f41e916528d128c64940b2c5e5162e2ab2713513c93c991f24b8e12517d8b4a289c49e2c2ab2436c91dae48cd50682bb189578acaac8a4d6414891ca3468e3647ed62414891db44 9 511 3 7 11 2047 21 2097151
def cc_62_19 : Nat → List (Nat × Nat) := unpackCursorV5 0xdc5b8360ec0d81a87506a0d0371ae05c0b81686a1b50680c09802e150698501a00400708e01c03041a411001 0x1405709fdbe4fb5c2722db3bb709eeb84f4df2796d93c2349c4becec4d6726d93a4699cda7ce2d0e848c340b4f9f9a5cf8d1e7568734a6d8cd27c1891dc747ed2a379c0b6a7a53d1228e7213f3089b8a049e6e489320289b09bcd69126724b318287da2ca78575102aa7113f99e29ccc94a6469731b439b62dcd514e694dd3425e4ecafa1e55ce029f32925988144bb5f25a4892aa44 11 2047 5 31 11 2047 21 2097151
def cc_62_20 : Nat → List (Nat × Nat) := unpackCursorV5 0xe07c0380700d853426048290118630460845081f13e0706d85b0360682d01719aa340680350600c000c00000 0x540d929b2cb4f935a7228d36d0ea58b752459a8e2bca7146a16974f3438d927c2091dca47e3715da74abd345553f29e8f1473a89f8a649e984a946125a59225299c2934d948a3ea2c92d20d128f489451253a49fd16d128c8bf45453a252952f17e958b749457a3a29d1a9793e2be8d95739ca798c51e8824b403599eda8c6a9760d4ab4324783d22b928fe8528e7313f14893d071f2732fb41145 11 2047 5 31 11 2047 21 2097151
def cc_62_21 : Nat → List (Nat × Nat) := unpackCursorV5 0x9d19c09a19a086a8608228207477406e36e06a26626606605a65a05a05a05a040d4003a30f60e0045021020001000000 0x58f5aec48dd61b62a5d35d0299e434befd253b0522ace59ebf28a4d92f1d8938641ac220a60b82b0341180806ebd4ab5e36ea8537d2a9ae7e4cf36a63aed1a8601ac280c60a82b02c11d289a6b948b5c562a4935cf899eb74ba1706b04c1581208eb06f95aa55ab51ad66956ac46a4d12f1d493d611a6794cb57a55594b29324bc7424f56d6bab2b1d56daeaa6c6d4b53a41354f099a394bcfca5260cb7ac859c9825a39125a7d37cec99ea847b5a56bacab1d631baae6dd4f26fa3935cea99e6a4c72125f7e129d528d5822deb1967a9c9a92c4bc7124e1606b0983184214c110560382300c0dc6e976114aae623f3b49f8aa49df6af951364 12 4095 5 31 11 2047 21 2097151
def cc_62_22 : Nat → List (Nat × Nat) := unpackCursorV5 0xa2144280c5b8a1052084107c6ced982b8560a8548a903f47c0f81c33803f4780c3180300420620c009010002 0x16ea458912cc049464b49b70a4bb7d23dbc915452ba94155b70a394a4bc8024f6d46992e30a8853d2728f6c469b5d32c9493edb8c36ca6d92527c4492e1648f00243b58b6a8653d2628e5192f1f893c90976144ab23a4db5122a84575242aa5112f1f493a468c6d126923b5eb49adda0d4ecf6a51025a84d2b28257d212ae5092d1ec92d9ad4a454bf6623db0e2f5a6d7a444bf0f25b8492bbf894ece46aa015f480abd964d49f25e3d127b281c58d5f2c24ab64245b1a34d8a9549e25e3c927274978f049ec2ad720a5e7ed292d059e824cf6024d 11 2047 4 15 11 2047 21 2097151
def cc_62_23 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0154ea0d409cd3823446088504e083f261ec01622c0508a0140253338640b19602664c0981030b610420004 0x83d2a1164d6fe24b7b944bf0afdf65748c2ab7b1452c496914496868a759b53be5a1caa97a074a47a13f2c096912496f72bc441242312adec9148724d7a24d7451fd64d4e5f4bf0325394d26dfa92efa48f7c2457411fb268cd4a29b7a947bcca29e64fcad25e4312794926de2914ac25e4292794a2cddf1454929e98947bb628dd89765049f78459ac5a15dc9564f49f13a4b86523c0890eeb2aaa414f4c0a39544bc8324f74a452a49790449ee76a4a395f4bcabdcad4a4e4bf7223dba1af49a97e264b70c25780d29dcc8d5462be97157b8c9a9504bc8124e951654a4b2dc0576dd28a5392d 11 2047 4 15 11 2047 21 2097151
def cc_62_24 : Nat → List (Nat × Nat) := unpackCursorV5 0x982608560165d9058c7f1c0701c007 0x307add852557611fb348cf090b107a457da29590d7eb56a72d25e825291ee4fcd126f82a4d7591fb608df078bd63b5fad1a9cc097e084a7832457551fb768edaf46ecc233c10a29ec4fcd026e5912f23c93e04db3016c18026d74d1fb728edad46ecb233 10 1023 4 15 11 2047 21 2097151
def cur_62 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_62_24 (Nat.sub p 768)) (cc_62_23 (Nat.sub p 736)) (Nat.blt p 768)) (Bool.rec (cc_62_22 (Nat.sub p 704)) (cc_62_21 (Nat.sub p 672)) (Nat.blt p 704)) (Nat.blt p 736)) (Bool.rec (Bool.rec (cc_62_20 (Nat.sub p 640)) (cc_62_19 (Nat.sub p 608)) (Nat.blt p 640)) (cc_62_18 (Nat.sub p 576)) (Nat.blt p 608)) (Nat.blt p 672)) (Bool.rec (Bool.rec (Bool.rec (cc_62_17 (Nat.sub p 544)) (cc_62_16 (Nat.sub p 512)) (Nat.blt p 544)) (cc_62_15 (Nat.sub p 480)) (Nat.blt p 512)) (Bool.rec (Bool.rec (cc_62_14 (Nat.sub p 448)) (cc_62_13 (Nat.sub p 416)) (Nat.blt p 448)) (cc_62_12 (Nat.sub p 384)) (Nat.blt p 416)) (Nat.blt p 480)) (Nat.blt p 576)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_62_11 (Nat.sub p 352)) (cc_62_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_62_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (cc_62_8 (Nat.sub p 256)) (cc_62_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_62_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_62_5 (Nat.sub p 160)) (cc_62_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_62_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_62_2 (Nat.sub p 64)) (cc_62_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_62_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)) (Nat.blt p 384)
def hc_62_0 : Nat → Nat := unpackHintV5 0x8422d8bf7fa49eb7c20ef3da0730526b7558b5acbb7ccc328b61cf12ad89d795dcba0a4de824e1117a380e21090cbe7c0a1f3ac0d11b53834ccab7c5b72b92ab4c1133788c896c143a3e9e18ff080aed64842bd2c13278e05132000538d80000a6000000 0x7931e4c993264c78f0e1c3870e1c3870e1c387264c9930603067d99f661c3870e0c187060c183060c183060c183060c1830e00c1830e3c98f264c993263c7870e1c3870e1c3870e1c3930986c1e331981c0e03061c183060c1830e0c183de0c183060c183060c38030601c9870e1c9870e0c1830e2c3c1e0e1c3a1c3870e1d00e070e1d9870060c38f263c993264c993264c9d55555555541c3870e1c3870e1c38743870ed5130986c1e233e0ccf844070380c187060c183060c183060c183060c18307540c18306030613264c9d555070e1c3870e1c3d513098cc6644070380c187060c183060c1d03df540c18306030644ea275543eaa9a83c854cc2070f263c993264c993264c9870e1e170b858b858ba060e81830e1c3870e1c3870e1c3a1c38743d0726130d83c467c199f0164070380c183060c183060c183060e060e81d03060c18301830993264e170b85c2c3870e1c3870e1c3d072613198cc164070380c183060c183060c1d503de0c18306030607261c387261c3870e1c38f0e1c183061d0e1c3870e8070e1d98543c98f264c993264c993262c5870e1c3870f555555541d0e8743b4a0c1acc930986c1e2b3e0ccf8442070183060c183060e96a6a981a03060f263c9c4ea2750baaa270fb7d5541d0e8743b4b0759926130d83ca09984420701830e0c183060c183a81c0eaa941ef060d4060c0e4c3870e4c3870e8c3870e3c387aaa0e1e83d5555503060c03870ecc151e3c78f85c2e070b264c993264c9930e1c3d41c38b17541c38743a1d0e87641835060d4984c1e0f05906cd81b36081c060c383060c183060c1d03060d418306a8306a03060f1e3c7c2e170fb7d0b162c98b162c98b1750b162c3a1d0e8743b21c3a870ea4c260f0782c8162c059b040e03061c183060c183060e8183060c183060c1a83de0c1a80c181c9870e1c9870e1c7870e1c7870e1c5d5070e1c587161c3870e1c5870e1c387060c18070e1cd82a4c993264c993263c78f1e2c5870e1c3870f555555541d0e8306b4a1d0ecc930986cd81b3603c1e4420701830e0c183a9a5060c183aa581a80c19513a898f1e3c7d0baaaaaa1f6f0e8760eb4a1d0ecc930991b0a01e0f2210380c187060c1c0eaa060c1830754a0f78306a030607261c387261c3d07aaaaa0e1c38f0e1c38f0e1eaaa81830601c387360a8f263c9c2e170b8193264c993264c9d070e1c387858baa0e1c3a1d0e8743b20c1a8306a4c261b0782c8567c199f040e03061c183060c183060e818306a0c1835060c1834060c1e4c793898b858ba162e1f6f164c58b164c58ba858b161d0e8743a1d90e1d4387526130d83c1640b1602d9820701830e0c183060c1830740c183061c187060c183060d41ef060d4060c0e4c3870e4c3870e8c3870e3c3870e2ea83870e2c38b0e1c3870e2c3870e1c383060c03870ecc151e4c793264c993264c9930e1c393264c9a31e3d1a3918b4723161d0e870e870e8306a0c1a8743a4c261b0788cf8333e0cc4620701830e0c183060c183060c183068306a0c18306a0c1a80c184c993264c993261d0e8743a1d0e93098cc663319881c060c383060c183060c183060d41ef060d4060c0e4c3870e4c3870e1c3871e1c387161e0f070e0c18300e1c3b30547931e4c993264c993264c58b555aa89b0fa956955555555554984c360f199f0667c22110183060c183060c187a060eaaa954060c1e4c79389d44ea175544e1f6faaa95555555554984c360f28266110880c183060c183060c3d40e07554aaa0f780c3830624d526aa3547ab32ab2aacacaa82acc1068f1e3c7c2e1730b264c993264c99355a5162d5555555555554984c1e0f05906cd81b360880c183060c183060e8183060c183060c1aa80c183c78f1f0b85c3edf42c58b262c58b262c5d42c58b555555555526130783c1640b1602cd82203060c183060c1830e0e8183060c3830e0c183060c1aaa83de030e0c1893549aa3d51ea8b45ab32a2d16aa8b5555054d820d264c993264c9931e3c78f162d556aa9556995555555554984c366c0d9b01e0f22110183060eaa8183060c183aa5501832a275131e3c78fa175555543edeaaaaaaaaaa4c2646c280783c8844060c183a060eaa8187060c183061ea95541ef0187060c49aa4d5955665547aa3d5916accaa82a6c1068f263c9c4c5c2c5c2c5c3d264c993264c993a555162d5555555555554984c360f0590ccf8333e0880c183060c183060c383a060c183060c18306aaa0f7a030e0c183c98f2713170b1742c5c3ede2c98b162c98b1750b162d5555555554984c360f05902c580b660880c183060c183060c383a060c183060c18306aaa0f780c3830624d526aa3547aa2d595168b5545aaaa82acc1068f263c993264c993264c9aa4c993268c78f468e462d1c8c5aaaaaaaaaaa930986d983d988cf82f3e0cc462203060c183060c183060c183060c183060c18306aa030613264c993264c9aaaaaa93098cc6633198880c183060c183060c383060c1aaa83de030e0c1893549aaa8f545ab2aa0ab3041a3c98f2713a89d42eaa89c3edf555070e1c3870e1c3d4c1e6a80000000000001830e0c183060c183a81c0eaa8183060c18703780c03930e1c3930e1c39b0e1c38f0e1eaa8387a0f8eaaaaa83a1c3870e1d00600f263c9c4c5c2c5d0b170fb78b262c58b262c5d42c58b0e1c3870e1c3870f41c3870e870e1d000000000000060c383060c183060c1d03060c187061c183060c183060c183061c0de0300e4c3870e4c3870e6c3870e3c3870e2ea83870e2c38b0e1c3870e2c3e30e1c3870e870e1c387401803c98f264c993264c993261c387264c993363c79b4723168e462c3870e1c3870e1c3870e870e1d0e1c3870000000000000060c383060c060c18306000c1803060c183060c1830e0004c993264c993266cd870e1c3870e1c3870e1c38000000003061c183060c183060c183060c183060c381bc0601c9870e1c9870e1c3870e3c3870e2c3c1e0e1c3a1c3870e1d0060000003060c183060c180c 25 33554431 10 1023
def hc_62_1 : Nat → Nat := unpackHintV5 0x8bde0722d584487e66e216392c84a41d609212e800c479fc90747d24401e3d21876165bdc891f96c36bdd9dca625fbcf6d6f11fc55f8b9943828c48e10010eea933eb0a14e7b262329cea0b5da932638e7c83daa11c4096c5d8270114cc28256bf905907940002c8 0x1b362c580f1e3d3a8f3e03c78f1e10b276f1e2c78ba1e2c58f163c58f162c78b1e2c58b1e8f51e3c79fde2c59f5e2cf9f163d1ea2c5a8b4e80f1e0c5870e2c1830e0c1a8f4e3e38f1e3c78f1e3c7842e167cf81307aa8f1e3cfef5de4d268f550061c1871e1c1830e8133e3c79b364d5de8f4eaaa70060d478f1e3c7931e3c78f1e10b859f0099f1eaa3c78f3fbc9a4d5de3d551ea70061c1871e1c1830762c98b1e2e18b1e2c78b1e2c78b51eaa3c78f3fbcf8b081eaabbe640787061c187060c078f8f9b36a747caef16aa00c18742273b87c3e1f43e1ea3d5478f1e7f78b023ea71eaa8f995de03c383a0e0c187478f1e3c78f1e3c01e3c78f1e3c78f3e7cf9f1e3d478f1ea3c78f1e3c78f3fbcf9f3e7d478f51e8f51e8f540061c187063c3830e3c187061c187061c1830e0c18743834d9b366cf933e4cf9b1e6c79f171f85aa6d50000000010400de0c3830e0c3830e0c3830e0c1870e0c1870e8706800f263c9d5030742c5870e1c3870f555555541c3870e1c3870e1c38743870ed5130986c1e333e0ccf844070380e060c183060c187a8183aaaaaa060c183018307931e4e27513a85d551387dbeaaa0e1c3870e1c387a983cd5130986c1e504cc220381c060c1ef060c187060c183061eaa0703aaaaa060c383060c061c1830183061d1870e1c7870f5541c3d07aaa0e2eaaa83a1c3870e1d00e1c3b30060c38f1e3c7c2e170f070b160c183060c18b161c387a8387162ea83870e1c3870e1c3870f41c3870e870e1d26130783c1641b3606cd8070380c183060c183060e8183060c183060c183060c180c183c78f1f0b85c3edf42c58b262c58b262c5d42c58b0e1c3870e1c3870f41c3870e870e1d26130783c1640b1602cd8070380c183de0c1830e0c183060c383aa060c1830e0c383060c183060c187060c180c3830603060c38f0e1c38f0e1c38baa0e1c38b0e2c3870e1c38b0e1c3870e1d0e1c3870e8070e1cd803061e8183aa1e3c78f162c3870e1c387aaaaaaaa87870e1c3870e1d0e1c3a1c3870f544c261b3606cd80f079101c0e030703060eaa8183060c183aaa060c18301832a275131e3c78fa175555543ede1c3870f079a90e1c387aa26132361403c1e44070380c183de0c1830f40c1d55030e0c183060c3d5503061c18306030e0c180c183a0f555541c3871e1c3871e1c3d5550743870e1c3a01c3873600c1871e4c79385c2e1703060c183060c58ba0e1c3870f0b17541c3870e1c3870e1c387a0e1c38743870e930986c1e0b2199f0667c0381c060c183060c183060c1870740c183060c183060c1830e0c1830187060c1e4c793898b858ba162e1f6f164c58b164c58ba858b161c3870e1c3870e1e83870e1d0e1c3a4c261b0782c8162c05b300e07018307bc183061c183060c18707540c183061c187060c183060c1830e0c1830187060c060c187461c3871e1c387161c5d50783870e2c38b0e1c3870e2c3870e1c38743870e1c3a01c3876600c1871e4c98f260c78f060c183060c3870e4c993268c78f468e462d1c8c5870e1c3870e1c3870e1d0e1c3a1c3870e4c261b0788cf8333e0cc46070380c183060c183060c183060c183060c183060c183060c180c184c993264c993261c3870e1c3870e1c3870e4c2633198cc66070380c183de0c1830e0c183060c383061c183060c187060c180c3830603060c3870e1c7870e1c58783c1c38743870e1c3a01c3876600c1871e3c78f85c2e070b060c58b060c1830e1c3d41c38b17541c3870e1c3870e1c387a0e1c38743870e930983c1e0b20d9b0366c0381c060c383060c183060c1d03060c183060c183060c1830183078f1e3e170b87dbe858b164c58b164c58ba858b161c3870e1c3870e1e83870e1d0e1c3a4c260f0782c8162c059b00e070183061c18307bc183060c1d03060c183060c183060c18301830183061c7870e1c7870e1c58717541e0e1c38b0e2c3870e1c38b0e1c3870e1d0e1c3870e8070e1cd803061c7931e4e262e162e162e1e0c183162c183060e83870e1c3c2c5d5070e1c3870e1c3870e1e83870e1d0e1c3a4c261b0782c8667c199f00e070183061c18307bc183060c183a060c183060c183060c1830603060f263c9c4c5c2c5d0b170fb78b262c58b262c5d42c58b0e1c3870e1c3870f41c3870e870e1d26130d83c1640b1602d98070380c1830e0c183de0c183060e8183060c183060c183060c180c180c1830e8c3870e3c3870e2ea83870e2c38b0e1c3870e2c3870e1c38743870e1c3a01c3876600c1871e4c18f264c183060c78f060c3870e4c993265c78f465e462cbc8c5870e1c3870e1c3870e1d0e1c3a1c3870e4c261b0788cf8333e0cc2e070380c187060c183060c183060c183060c183060c183060c18306030613264c993264c9972e1c3870e1c3870e1c3870e4c2633198cc2e070380c1830e0c183de0c183060c183060c18306030603060c3870e1c7870e1c58783c1c38743870e1c3a01c3876600c1871e3c78f264c9931e3c78f0e1c3870e1c3870e1c38726130783c361b0381c060c183060c1ef060c187060c183060c183018303930e1c3930e1c183061c58783c1c38743870e1c3a01c3873600c1871e3c78f89d44ea175544e1f6faaa83870e1c3870e1ea60f3544c260f079411b0880e0701830e0c183060c187060c1efaa061e8183aaa060c183061c018300e4c3870e4c387060c1d55070f40c1d55071755541d0e1c3870e80703870e6c3803061c78f1e3c793898b858ba162e1f0f164c58b164c58ba858b161c3870e1c3870e1e83870e1d0e1c3a4c260f0782c8162c059b00e0701830e0c183060c187060c1ef0740c183061c187060c183060c183060c1870060c03930e1c3930e1c183061c58717541e060c183060ea81c0e060c1830e870e1c38740381c387361c01830e3c78f1f13a89d42eaa89c3edf555070e1c3870e1c3d4c1e6a8993264c180c1d4ce075541c3870e0c187060c183060ea81c0eaa8183060c1870060c1871e3c78f1e4e262e162e858b87c3c593162c593162ea162c5870e1c3870e1c387a0e1c38743870e93264c98301831742c18316cc183060c3870e1c1830e0c183060c1830740c183061c187060c183060c183060c1870060c187 26 67108863 11 2047
def hc_62_2 : Nat → Nat := unpackHintV5 0xbf6f1abc70bfb64d89ade61aa611f5a0118096d64f90dd7e8522ef7f696e7ab52d6ea3056845976181b1555f0953ac6c524c584c0d904032f73b593635dd5f314d24267eb420817f1a9d7911624f0d84f708dd2a069c9002950201b43800006d 0x3cd8f366c78f367cf9f5e7cf9f5e6cd9f3e3c78f1e6cd9f3e7d19f3e7d7a753a6d3a3cd89d4e80bd5935e4d5af366cfaf16ae5f2b163c78f1ea00000000f0f80020801bc0003e200c3830e0c3830e0c3830e0c1870e0c1870e870683061c383061c38042c9dbcd8b89938d8b162c5d0b466d3a6d01e6f00061c1878593b79b1746c58f162c5a3362d4e97264cb9b3e2e858b162c5a3462d18b162d00079bc00046203161c38b060c3830e0c38f1e3c7a3468d18f1e3c7aaaaa2a9f3e7cf8f3e006f3e7cf9f4046dd1a346dd1a31e3cfa3468d1a3468d1a800000c3830e0c3830e0c3830eaa0c3830e0c1870e0c1870e3cd8f368dba3363c79b5ba6d1e6c51adcba326dc9a32e6cd9f462d1c8e462d400000001e6f0000000040187061c187061c187061d0e0d060c387060c38700a1eac797aaa9797267d7932e5cb972e5cb9f5e4c993162c59f366d1c5172ea5d3a74000b87c0fa206f061c187061c1872ebcd97aaaa97972e7d79f3e5cb9f3e6cd9b367d1d1f3f5545d4ea74db272902a89d4bea1f5542e16a00000007c00010400de00000c3830e0c3830f540c1870e0c1870e8706d41e074002c597363d58f2e2c5c2e165c597267d7932e5cb972e5cb9f5e4c993a8f9b36bc5d05d4e80007d1037830e0c3830e0c39b5e6d7c2e172f170b167cf9f5e7cf9f5e7cf9b366cd9f5e2c58b17547cfa753a9d368b16c9c0058b162c98b162d78b162c78b162c58baa500000003e000082006f0000061c187061c1870741c1830e1c1830e1d0e0d060c387060c387002e5d47a5cbc2e16134e4c9974e5cd8f1e6c993266cd9b366cd9b366c5d0b555007802b0f8881bc187061c187061d479b1e6e170b5de4d26a97264cb80027571c0367c5d0b400001e6f00110187061c3a0c3830ea97264cb971e9cd8f2e9cb93265cbc5c5978b8b2e6cbab0264d393264cb974e5c0000993264c00fa7363cd8f4e7c5978bc9c5abbd26a93555540000001387c0000010400de0c3830e0c1870e0c1870e0c3830e0c3830e0c1870e0c1870ea1d500264c7aa4c99b570b8593264c984d3af363c79b2e5cb9b366cd9b366cd9b1742d47bbd5369b401e00ac3e22000c3830e0c3830e4c993264d793264c9972e5cba4d5536aa9749932e5cb972e5cb972ea001bc000000000000187061c187061c187061d541870e0cb87005498f264c98f264c993264e262c9c4c593264c9ab366d593267cb80000013264c9932604c9a73e9cd8f363d3b73e2d3c7e4e2d26a4d55deaa6d554e80130f800000000002080003061c383061c3830e0c3830e0c3830e0c383061c383061c3aa806f2e2cb8b1e8c0782cb9717bc3e2fa4fbcfd2f1e8c079bc3e23468d1a3468d1a3468d1aaa3d55468d1a3000011a3468d5de00000008cde0000002030e0c3830e0c3830e0c3aa830e0c3800f363cda75e9c9a7269d3ab5eb9b1e3cda7938b4f27167d3a7267c9a75e03c79b1e3c79b369c000078f1e3c00f8b4f1f938b55577a3d51eaa8000003c0001387c00041000061c187061c187060c387060c387061c187060c387060c3875500162c7ab1e5c58b592e4c997a8ba75e5cf9f2e5cba71e3e5942d55400076881bc187061c187061cb93265c58b162d64b93265cd8f1e6ea366cd9b366cd9b3649e858b16aaa00f00561f11037830e0c3830e0c3cb164c59b163c5aaaef992e4c997367c5d0b000168e1808003cde000022030e0c3830e0c39b566d5c2e170b858b162c593162c58b162c78b16a9f2e9c99f269cb9f4e6c79b1e9c293d42c58b1600015400aaaaaef656400000000000161f010400de0c3830e0c3830e0e8383061c383061c383061c383061c3aa802b2f54ac78f2f2a5c9932e8c78f47442c58b2e9d7973e7cb972ea4ddea9745a03b00440de0c3870e5c1830e0c3830e1d2e5e8b93265ea54b93265cd8f1e6ea8938b162c59b366cd9b366cd9b51eef54da2d007802b0f8880030e0c3830e0c397566cbd44eaa87d55554a972e9c99f265cb9f466c79b1e9d1d0b16000001554149c5aaa7554dacb2abbc00000083e00000020800030e0c3830e0c3c0eaa0f540c1870e0c1870ea1d5001743c7d0f1f013b7d543e1f1f3f0f47a8f1e3cfef94e8f47a841c1c3c783063c7813b7c2e878b1e2c78b1e2c58b1e8f51e3c79fde2cf9f163d1ea2d4e80f1e0c3830e0c18f57131e8f53e7d19fde3d1eaad580f1e0c1c2c7d0f878fa8785513b7c7cfd47d78f47a8f1e3cfef4ec8f47a803a0e3c7830607cfbb5da83b763d58f1e7cfa33fbc78f01e3c183 24 16777215 10 1023
def hc_62_3 : Nat → Nat := unpackHintV5 0xc80a39c1919eba01e4b2bdd1a5c33fa0515c9c290a9581aa8bc66f880cee81a59a7a71cd7285fb652f565cc61a55d5bc4e75d8419b37344f532d6db825021b1cba12167d8f0edde80e8c140d28590b6c6f0b001b09407008204806247f000189 0x50b87d544c9932755544edf5547cfd55552f264c993264c9933e8cd8f363d1d55549d6949a4d4db3200000000000020801be075507061c187061c187aa060c387060c3874383400b97878f858b162e170b2e4c997367d18f1e6c79b467cfab56bd59f3e8d5a31742d59b4ea74007800ac3e2206f061c187061c1872e4c99785c4bc5c2c59749abd368b64bc4c993274bd19b1e6c7af462c5d50b16a0000000bc00000000061c187061c1870741d0e0d060c387060c387002e4c99785c42e1724cba7366d38b6165cb93265cb9f363cd8f4e2c5d0b162c5800000000009c0037880c3830e0c3830e0e83830e0c3830e0c38017264cbd0b1713b7c2e162ea162c58b1e2c58b162cb97264c9932e5cf9b1e6c78b17542c58b162c58b16bc58b3e7c58b162cba4dae9b45b22c5a2d458b4ea000000000000b0f8082006f061c187061c1870741c1830e2c387062c1830e1c1830e1c1830e1d0e0d00a365c78b1e2eaa8b93265cb972e5d7af2e7cf972e5cd8f1e6ea8ba9d00007a206f065c3872e0c187061c187898ba858f8597264cb9b1e3cdd50b16bd78b162c58b1600f205a206f162c187061c79b1e5ea8a8baad368f664b975e4d5932e5cd8b1e3c78f162eaaa94000000000000000187061c187061ea90e0d060c387060c387001e6c797aa2750baaa87dbeaaa2e5d7933e4cb97366c78f1e3cd9baaa5f47cfd5555552f165d569b47b4b275990000007800041f00010400de0c3830e0c3830f50781d5503061c383061c3a1c1a002e878b270ba2e4c997a5ebea8d8f1e6c58b162c58b00782d1037830e0c38b166cb8f87c2c5c2e165cb97264cf932e5cb972ebd7973e7cb972e6c78f362e8597565d4e800003d103783060c3830e0c3830e3cd8f370b85c2e15aad368f45b2acbaf26ac9af2e6e1e3c78fa162ea858b5000000000000000061c187061c1870741d0e0d060c387060c387001e6c79b85c2e1709d3a74f23cd8b6167d3933e4d39b363c79b362c5c9e162c58b162c00000001e0009c0037880c3830e0c3830e0e83830e0c383061c1830e003cd8f370b858ba162e1f6f162c58b262c5d42c58b3e5d7933e4d797366c78f1e3cd9b162e97d42c58b162c58b162c5af162cf9f162c58b56ab4da3d16c8b168b5162d3a8000003c000000587c0410037830e0c3830e0c383a0e0c1870e0c1870e0c1870e0c1870e8706800f2e4c7972e5cb931e3c7972e5cb972e4c9972e3c7972f17165e2e2c49a6d1a3cda8d1a9b36a5d2e8000000000000030e0c3830e0c383061c383061c3830e0c3a1c1a00a0006c7a7466c7a7465c9932e5e2e2cbc5c597264cb972e5cb8008aaaaa00000000000000c1870e0c1870e0c3830e0c3830e0c3830eaa005cb972e4c9972e3cb971e5cb97264cb978b8b2f17165cb972e24d2e5d3a6d2e974002e000000030e0c383061c383061c3830e0c3830e0c3a1c1a004c993264d793264c9af366d793267cf93264c993267cf9b366cd9f5e7cf9f5e7cf9f5e4d384c9a9d36a753a013264c9af263c98f264c98b2713898b267c9975000000003e00082006f0000061c187061c187061c187060c387060c387438341830e1c1830e1c00b935e4cbaf2e4c9972e6cbaf2e5cf97264c9933e7cf9f366cd9b3ebcf9f2e5cb973ebcba749a713a6d4e97402e7cfaf5e5c79b1e5d797165e2f17164c99326a000000007c0010400de00000c3830e0c3830e0c3830e0c1870e0c1870e870683061d7870e0d783061c380132e4cb8f1e5c993264cda3d264d269d2e974b8f1e3c797264cb972e5cba000000000000030e0c3830e0c3830e0c3a1c1a0c393065c3800f2e4c7972e5cb931e3c7972e5cb972e4c9972e5c78f2e5cbc5c5978b8b2e930da3d366d4d9b52e974000000000000187061c187061c1830e1c1830e1c187061d0e0d002e4c9972e5c9932e5cb972e5cba4c5e9b4ba5d2e5cb972e3cb8f2e5cb8b2f178b8b50000000000000000061c187061c187061c187438341830e5c387065c1830e1c00b93265cd9f8593b79b170b85d1b168c58f163c59f167c58b167c5af162c58b166cd8b53a0f3e00030e0c383161c38b060c38f363cd9f2e7c99f267cb9b367d1b7466c78f367e3e2cfc7c5a753a23d366cda751a00003c0f800000c3830e0c3830e0c1870e0c1870e0c3830e87068043eb7ef979f8f9b2e4e570f3fbc779f362d79f162e165cb8b1e7f78d43cfef1eaf79fa5e7cdd2b2e4c5c3cfef1de7cd8b1e2c59f0fefde7cd8b5e7c5a9c5ab163cf87f7887065cb9b2e3cd8f2e5cbc2e165c99f5e4cb972e5cb972e6cd93264c78f1e6c78f0b972e5cba9d00007a206f061c187061c187 24 16777215 10 1023
def hc_62_4 : Nat → Nat := unpackHintV5 0xce0d03cb60abc59972beadbbbc389db79928b24d53ac218ba316439c4db29579b58fad7388d9b58441267c1e096e1f80693d38611a095c313a57413c52693649de2347c08742715434a3742f5952288db31f8642198d7e0d6f0806dda40001b7 0x28d971e2c78baaa552e934ba5d52ea754da3d990000de880c3870e5c1830e8706c4c5d42c7c2d165d269b47b322d16806f440e2d0e0d1e6c7972e5d3934e4cb97162d556a8a9569555554001540000000000010187061c187061c1830e1c1830e1ea9540079b1e5ea89d42eaaa1f6faaa955555555552ea9354daa3d5995595565650000000000000de202030e0c3830e0c3d41e07554aaa8741a800ba1e2c9c2e9165d26cc9b47a2d16806f444383458b365c7c3e162e170b5552e9749a4d2e9754ba9d5368f45b200001bd10183061c1874383479b1e6e170b85c274e9d3ca8b55549a9b5545aaa9d00000000010187061c187061c1d07061c1875506800f363cdc2e170b84e5d3934e4d397a555162d55555555540000000000000010187061c187061c1d07060c387060c38755001e6c79b85c2c5d0b170fb78b162c593162ea162c5aaaaaaaaaa2d54baa4d536a8f545ab2a2d16aa8b5540000000000003788080c3830e0c3830e0e8383061c383061c3aaaa1d06a003cba3cb97551e3d4b972e5c9932e5c78f2e5e2e2cbc5c58aaaaaaaaaa800000000000030e0c3830e0c383061c383061c3830e0c3aa802a5c9932e5c7972e3cb972e4c9972f17165e2e2cb972e5c554014155540000000000000187061c1830e1c1830e1c187061c187061d5400b93265d6164ede6c5c2e1746c5a3163c58f168c5a3162c5a316bc58b162c5a822a80000030e0c3830e1c38b060c38f363cdaf2e8c9af268cbaa8dba3363c79b4723168e462d545540141540000000000000187061c187061c1830e1c1830e1c187061d5400d9b366d555555549aaa8f545ab28000000006f1010187061c187061c187061d5550e835001e0f264c993266c78f364d269b47aad5693263c7931e4c99b2e3c78f1e6cbab16be572f16a0000000000000000c3830e0c3830e0c3830e870683061c383061c3800f263f78f1e4c98f1e3c99b264c993266c78f364e262c9c4c593264c993264c99326bcd9b1e3c78f366c993264c9935e4c99f3e4c993267c5af8fcbc59349a6d1e9326a4d3aab55a000000f0000261f00010400de0c3830e0c3830e0c1870e0c1870e0c3830e0c1870e0c1870e8706800f264c7ef1e3c9932e5cb972e2b4793364c98f1e3c98f1e4cb9f3e2e85a00000030e0c3830e0c38f263c2e4c9972e3c79b2e934da3d56974b8f264c9931e3cd931e3c78f264d58b2f17978b5000000000000000061c187061c187061c187438341830e1c1830e1c00793263f78f267c9931e5c7931e3c98f1e4c99f2ebe170b2e5cb973eacba27c00061c187061c1871e4c98fde3c793265cb972e5cd972e5cd9b2e5cb87cb972f45d4ead0780171f8881bc187061c1831e4c98fde3c79326a972e5cb97565cb97366cb80172e5d585cb97a07ab037801704061c187060c7931e0f4997268f365c9932e5c78f365d3974e5cb934e4cb974e5cd9b1e3cd9b2e5c0003e5e2f2700001e09c003780080c3830e0c3830e0c3830e0c3830e0c187060c3801326081bcb9f2e5cb9b365c00ba5d681831e4c98fde03c793260172e5cb973e5cb97366cba5d4b972e7cf972e5e8fa7dde5cbafcbab40187061c1831e3c9931e4c7ef1e3c793264cb93265cb8f1e6cbc5c5978b8b2e5c9935e4c9932e5d797366c78f1e3cd9b2e5cf9756bcf9f3e5cbaf2e7c5978bcbc59749a6d1e974eaab4eaad2e8000003c00003e00020801bc187061c187061c1830e1c1830e1c187061c1830e1c1830e1d0e0d002e5c58f1e2eaaa8b93265cd8f1e6d19f3ead5af567cfa3568ea93a9d007802b0f8881bc187061c187061cb93265caaaa5e5d26af4db325c593264c98b16bd19b1e6c7af475554a0000000000000000c3830e0c3830f54870683061c383061c38042e2e4c997aa1f513b7d55555172e4c993265cbd552fa3e7ea8fa3363cd8f4755545d26d2c9d6ba6d9900000000000010400de0c3830f50781d030e0c3d503061c383061c3a1c1a004c98fa1e2c593162c5c2e164c993266c78f365cb972ead7973e7cb972e2e859753a00f002e1f11037830e0c3830e0c393264c9c4edf42c5c2e1750b162c58f162c58b164c993264c993267db9b1e6c7b7162ea858b162c58b162d797162cf97162c58b26935368b6458b5169d4000000000000410037830e0c3830e0c383a0e0c1870e0c1870e0c1870e0c1870e87068013263c58b1f513aaa264c993363cd8f1e6d5a3467cfab56bd59f3e8d5a3aa54ead55a74e800f001587c440de1c3830e0c3830e0c393264c9d1551349abd36cc93262c593164c9af466c79b1ebd1d555280000002f0004000000187061c187061ea90e0d060c387060c38700 24 16777215 10 1023
def hc_62_5 : Nat → Nat := unpackHintV5 0xae347eaa010da40d7d9cddcc97a14f9121a08b05878505807ffd4279b19374e1346e3da964aa65616ccf5ba9715804e95161a947da62443ce73e856e3799bb33610e2a82382a4c0d2a340625ed1220356e191dc614b51a0f8d4a09618b000258 0x1b2f52a6c78f2f54a3ddeaa000c3830e6cbd51b1e3cbc028f77aa9749a6d992e9754baaa8000021f01870e1cb83061d0e0d1e6c797aaaa2e5d193464cb97aaa366d40015551555554000080016000000030e0c3830e0c3d503061c383061c3aa800f363cbd44eaa87d46eaaa80555547bbd95555554baa4d536b2aaccaacacaa8000104006f0000010f8030e0c3830e0c3c0eaa0f54aaa8741a80131fbc7931e3cb93aa264c993363c79b264c9934e9c9ab764c99340366c9a9daa00000061c187061c1871e6c7972e5d193464cb97366d1d55554d29753a6d1a3cdb4b4a32000000023000000187061c187061c1830e1c1830e1ea90e0d001e6c797aaaa2e5d193464cb97366d1d0001753b23d19468d3800000000000030e0c3830e0c3d503061c383061c3a1c1a003cd8f2e5d1a32ead555555174e9cb9b463c78f1e6f7d43c7d5480000000000000c3830e0c3830e0c3830f540c3830e003cd8f2f55545d3bf2f0f1e3c79b40554daab2bf4000000000043e030e0c3830e0c3d5030e0c3aa8017365eaaa8b974e4df932e5df9b1e6c7a750002ea753a6d1a9a80000000000000187061c187061ea81830e1c1830e1d0e0d002e6cbd44eaa87d555540172e6cdd35354000041001bc001b3065c19b06ce075507aa06cc1b3001e0f26aa3c7a9b2eaaa4c993266c78f369e4e2d3c9c5aaaaa8002a8000000000002030e0c3830e0c383061c383061c3830e0c3aa800f263f78f1e4c98f1e3c99b264c993266c78f364e262c9c4c5aaaaaaaaaaa4d526a9b547aa4d26aa9355516aca0000000000001bc404061c187061c187060c387060c387061c18755543a0d400793263f78f1e4c9aa5cb972e5d36cb4ba5d1560004061c187418f263c1ea9354b93265cb8f1e6cba72e9d2eaa9b5553aab20000000002030e0c3830e0c3830e0c3830e0c3aa83400793263f78f549aa3c79326ac2e165cb972e80a2000020c3830e0c3830e3c98f078f555264d554b93265cb8f1e6cbc9c597938b55555000550000000000004061c187061c187060c387060c387061c18755001e3c9931e4c7ef1e3c793264cb93265cb8f1e6cbc5c5978b8b555555555554baa4d536a8f54ba5d5555516aca0000000000001bc404061c187061c187060c387060c387061c18755543a0d400b97163c78baaaa552e934da3d46a355da9d5990000de880c3830e87068b16aaa5c9932e6c7a7466c7a74654ab4b54aaa000aaaa0000000000000c3830e0c1870e0c1870e0c3830f54aa010b8b93265ea87d44edf555554aaaaaaaaaa97549ab32ab2aaa3547ab2b280000000000006f1010187061ea0f03a061c187aa55543a0d4009931f43c58b262c58b85c2d549a4d368f4ba5d52ea7545b20001bd10187061d0e0d264c99389dbe858b85c2ea162c58b1e2c58b162d555555555526a9355baa3d516aca8b45aaa2d2eaa0000000000001bc404061c187061c1870741c1830e1c1830e1d5550e83500546aa4c98f162c7d44eaa95554e9349a6d51eaa351aaa75664000037a2070e0c3830e87068b16aaa6c7a7466c7a7464c993274aab455400a0aaaaaa0000000000000c1870e0c1870e0c3830e0c3830f54aa0142e1f5513264c9d55513b7d52aaaaaaaaab2aaccaa93549aa8d51eacaca0107c00000000000de20240eaa0e0c3830e0c3830f54aaa8741a80172f0f1f0b162c5c2e16aaa5d269b51a3d1ea351aaed4ea8b64000037a2030e0c3a1c1a5c9932f0b885c2e5539b369c5aa9755551ea2d554e800000000080c3830e0c3830e0e83830e0c3aa8017264cbc2e2170ba5554e8cd8f363d3a3162d55555555540000000000000010187061c187061c1d07060c387060c38755002e4c997a162e276f85c2c5d42c58b163c58b162c5aaaaaaaaaa2d54baa4d5547aa2d595168b5545aaa0000000000001bc404061c187061c1870741c1830e1c387062c1830e1d5550e83500 24 16777215 10 1023
def hc_62_6 : Nat → Nat := unpackHintV5 0xbe65cdb24f06b0b067ac790ea5a9b49c6252969d7190698d89adaf8201eb7ae1c873f9ba6d55a96955005fce6259c98152d9bc4c619e4555c34208d33e1cfb37a59e3125a02b6d6e246dc0241815237c271d897d14aa380edd7308c187000230 0x17975e4d7935e5c79b1e6c58b5162c5b0b85d00042e169d4e8b16a3c7a88f45b20000000000000c3830e0c1870e0c1870e0c3830e0e83a1c1a003cd8f36bcba326bc9a32eac2e170b85d0b1742c58b162c593162c59b162c58f162c5a3162c58b162d78b162c58b013a9d47bbc78f51e3c78b6458b5169d4000000000de40400030e0c3830e0c383061c383061c383a0e0c1870e0c1870e8706800b5479b1e5e170b5500061c187162c79b1e5c58b085551eef2e9749a4d2e9754baa9b45b2a0000087c061c1874383479b1e6df977e4df937e5cd9b162c58b162e170b85c2d4001555155555400000008000800061c187061c187060c387060c3870741d540079b1e6e170b85c2c58b162c98b162cd8b162c78b1602aaaa3ddeaaaaaa97549aa6d45ab2a2d16aa8b5555000003790100000021f0061c187061c1870741c1830e1c1830e1d5550e83500263f78f263c797264c993266c78f364c99326add934e9c993270b85a01353a2c58b16004c3e000030e0c3830e0c38f264c7ef1e3c9932e4c997363c79b2e5cb9756fcba74e5cb97858b165e85a0172ea5d3a7458b162c00000187061c187061c79b1e6d197464d193465cd9b470b85c2e1601409d4e8b47a8d1a7168800000000000030e0c3830e0c383061c383061c383a0e8706800f363cdc2e170b85a32e8c9a3268cb9b368c58b59162d3a9d368d1e6d1688b16a2c5a80000000008c000061c187061c1870741c1830e1c1830e1d0e0d00366d3977e4d3937e5d39b1e6c7bf85c2e170b50004ea753a6d162c58b1688b0000000000000061c187061c187060c387060c3870741d0e0d00366e170b85c2c58b162c98b162c58b163c58b00d9b1742c58b168b16800001bc8080006cc1b3066c1b30742c183161c183161c1b306cc00783c9d55550f1f555545cbd00013264c99b1e3cdd5234e8d468d1a00004000000000c983260c78327540c1930e0c1930e0c98326008f1e9752f1389c3e3752793d49e8f5404c99b364c9a764022037830e0c383a0e3c98fde3c793263c78f265c9d44e27513aa1f51baa89d551389d5555555004c993266c78f364c993499369a9aa0000000020800de000c983260c783260c1930e0c1930f03aa83d503260c980132e4eaaaaa1e3c78f2e4c99780363c79b264c993aa2e5cb9700000000000063c193064c193aa064c9832e4c193064c0079787972f543c7d172e5ea2aaaaa8b93265cda31e3cd9b468d1a8d3a36a8000000000000193064c18f064c183261c183261ea8193064c00b93265ea2aa96693a3363cd8f4e8eaaa8b9764ba74d9b36cc972e5c000000000000187061c187061ea81830e1c1830e1d0e0d002e4c9972f551555172e3cb8f2e5e8000b93265cd9baa2e5cba5cba00000000000000c983260c98327540c1932e1c3832e0c1930e0c983260145d1b72f500ab36a351aa9749b23d9946a7500000061c187438368b93265e6aa8ba36e5ea0156eacd9b468d1a346a35180000030e0c3830e0c38f363cbd554172e9c9a7265cbd2cd5555175ba74e9b36c9b99468d1800000000000030e0c3830e0c3d503061c383061c3a1c1a003cd8f2f555505cba326dc9972f55000176edcb9b1e3cdd52351a00000000000000d9832e0c78337540c1b30e0c1a30e0d98366004c99327555544c9d53f466c79b1efd1a80022aaaaaaaa800000000000030e0c3830e0c3d503061c383061c3aa8013264c9d44ea2750fa9bd555009377aaaaaaaaaaa4d51aa3d595566556565540000820037800000030e0c3830e0c3c0eaa0f54aaa8741a801b463d19b1e970593264c9d55552cd23363cd8f4740004d14e9b664b975a50000200000000061c187061c187aa060c387060c38743834015263c993263c9a3264c993aa89c4eaa27544ea2750fa9bd5555555004c997264d526ef4e9b64eb4b320000000041001bc001830e1c1830e1c187061c187061e075507aa4383400d972e4c9975aaaa365d18f1e5c797465d1972e5d1975e5cb97801eef1e8f1e5d4e80000030e0c3832e1c397060c38f363cbd555172e8c9a3265cbcd52d0001753a23d991e3d694000000000000187061c187061ea81830e1c1830e1d0e0d001e6c7972e5d193464cb9756a275543ea375523aaa4755555555005d4ea3dde3c7a8f1e3e93ad32cc80000000104006f00061c187061c187060c387060c38781d541ea90e0d00 24 16777215 10 1023
def hc_62_7 : Nat → Nat := unpackHintV5 0xeb5a69e5b569df5d96d4f69ad00d3ac859edc03609bae155ad9354a55e0d9f0d9491ab5989661181c1e97a3de17299e96b15e16579675e45cd59194b4d0306482537417daa386a4532dd632ba9cd1f2f1f1ac51a15595b0ea1ae052e5d00014b 0xf1e3c98f1e3cb8f1e3c781513a9dd543e1f550faa1f50faaaaaaaa54ba9d1e9d478f51e8f685d2b3bc001e03c00de00000000030e0c3831e0c1870e0c1871e1c3830e0c3c0eaa0f5487068003078f1e3d7a75e9d02170b85c2e4f6f1742c5aed55547aaf51680000000000030e0c3830e0c3830e0c383a0eaa003c78f1ebcbaf26bc9af2ea0010b85c2e1742c5d0b16aaaaaaaaa80000000000000c3830e0c3830e0c1870e0c1870e0e83aa800f1e3c98f1e3cb8f1e3c7810b85c3e858ba162c58b85c2d551eaaaaaaaab3bd76a93547aaa8f47aaa3d51ea8b55000780f003780002000087c0187061c18f060c387060c3870e1c187061c1d0755543a0d400183c78f1e4c993263c78f1e1c3870e1c3870e1c3870e000000001c3870e0c00e1c3870e1c387000e0f1e3c98f1e3c78f1e3c01f0f163e1e2c78f1e3c78f478f1e8f1e3c78003c07801bc000006cc1b3063c1831e1c1831e3c3831e0c783660d983660d980030783c98b162c58f1e2c5972e2c58b162c5c2e170b85d00013264c99b1e3cdbb4eed769dda2e8580000000000003260c9831e0c983064c383064c383a160c98326008f1e9752f0b8593164c59b163c5a7171c58b169c5a7162c5813266cd93262d4e8006f88061c187061c1871e4c7ef1e3c9931e3c7932e4e170b85c2e858ba162c593162c593162c59b162c58f162c593164c58b162c593162c58b16013264c99b1e3cd93264d264d1742c58b168b16800000004c3e006f202000193064c18f064c183261c183261c1d0b060c587060c587064c193001e4c783c78b162c58b164c98b162c58b170b85c2e1740005c9932e6c78f374d3d369a7a68ba1600000000010000c983260c783260c1930e0c1930e0e8583260c9800f51e4d49c2e165c593166c58f169c5d3162c5a7169c58b1605cb9b365cbd0b16a2d3a75387c000df1000c3830e0c3830e0c18f1e4c98f263f78f1e3c993270b85c2e1742c58b1717a162c597162c593162c59b162c58f162c597165c58b162c597162c58b16017264cb9b1e3cd972e5d2e5d1742c58b168b168000000001bc80800064c193063c193060c987060c9870742c183161c183161c193064c00797163cb97162c58b1e3c58b2e5cb82e1742e85d0b1742c597264cb9b1e3cda3468d469d1a2e8580000000000003260c9831e0c983064c383064c383a160c98326002c5a8b458b2e4c997363d3a3363d3a305c2e858ba162e170b2e5d16972e5cba74da2da9000000000000061c187060c387060c387061c1870741d0e0d00162c597264cb971e5cb8f2e5c162e162c0282170b2e4c9972e5cba5cba6cd8ba1600000000000000c983260c1930e0c1930e0c983260e8583260c9800f363cda72e9c9a7269cb8b16a2d162e170b05c2e858ba162d3a9d366d169b468d18b6a4000000000000187061c187061c1830e1c1830e1c1d07438340079b1e6db97464db93465c58b170b8582c5c2c58050376e6c78f368edb6d1a2e85800000000000003660d9831e0cd8306cc383068c383a160d98366005cba3c7a5cbc2e165c593166c58f168c5a3162c5a316ec58b1608cd9349a2d4e80230f81be20187061c187061c58b5162c5a6c7c7466c7c7465c9932f40010b85c2e162c5a9326a24d4e9b45b20000000000000c1870e0c1870e0c3830e0c3830e0e83a1c1a00a3cd8f2e5c9932e5cb972e8d197571cb972e2c5c2e162c58413779349934ea7400000187061c187061d52e4c9972e3cb971e5cbc2e1742c5d0b170b858b2e2c58b262c58b2e2cb8b162c58b2e2c58b162c58b162c78b16024dde4c9a93264d3a6d16c8b16a2d3a8000000001bc80800061c187060c387060c387061c1870741c1830e1c1830e1d0e0d00264c793263d6170b262c98b362c78b462d18b162d18b5e2c58b055555000df100c3830e0c3830e4c993262c58b164c98b16fd19b1e6c7bf470b85c2e16a0008aaaaaaaaa0000000000000c3830e0c3830e0c1870e0c1870e0e83aa8013264c9c2e170b858b262c58b262c58b6e2c58b1e2c5809377aaaaaaaaaaa4d551ea8b56545a2d5516aaaa000006f2020000000187061c187061c1d07060c387060c38755543a0d4009931ea3c993162e170b262c98b362c78b462d18b162d18ba62c58b0466cba5d16a740037c4030e0c3830e0c38b16a2d162c993264cd8fa68cd8fa68e170b00a085c2c9a25cba8b16a9d368b64000000000000187061c1830e1c1830e1c187061c1d0743834015263c993263c993264c9d0b1742c5c2e170b858b262c58b162c593164c58b162c593162c593162c5b7162c58f162c0264cb9326a9377a74da2d9162d45a750987c000000000de4040003061c383061c3830e0c3830e0c383a0e0c1870e0c1870e87068017264cb8b162c58429377aa974da8d1e8f51a8d56edb545b2a000000c3830ea1d9a0c1a5cb971e3cbad42e165c593166c5a3163c58f168c5a3162c5a316bc58b160aaaaa0001be20187061c187061cb93265cb97162c58b162dfa3363cd8f7e8e170b85c2d400151555555540000000002000187061c187061c1830e1c1830e1c1d0755002e4c99785c2e170b165c58b164c58b162c58b1e2c580aa9377aaaaaaaaa5d551ea8b45ab32a2d16aa8b5555000003790100000000c3830e0c3830e0e8383061c383061c3aaaa8766a0c1a800b163cd8f2e5c9932e5cb972e8d1975ebcb972ea2c58442e165d4e8f778f478f00000061c187061c187 24 16777215 10 1023
def hc_62_8 : Nat → Nat := unpackHintV5 0xad1b78a8692ca14dc7967ab5963810961c0795dc1094ac4c94900794740793ec228bea017e4b6876e1da701db1648ee460151e5a1d7e55c91554206a4ce5cf44a6103e299f36b9dc2fb5c1288dca1b9f3c15fd6810b153073a5e06c81c0001b2 0x151e3c7931e3c7971e3c78f1eec78f1e3c78f2e3cb8f1e3c78f1e3c78f1e3c7805c9932e5e2e2cbc5c58f878b1f0f163c78f1e93779326a4c9931e3d3a8f1e8f51e8f53a5d0000000780f0037800000c3830e0c1870e0c1870e0c783061c383061c7870e0c3830e0c3830e8706800307803c78f1e5cb972eaaaaaaaaa3d4ba8b555400000000000187061c187061c187061d55540078f1e3c78f264c78f1e3d4000993264c78f1e3d7cbc5af978b498aaaaaaaaa800000000000030e0c3830e0c383061c383061c3830e0c3aa800f1e3c98f263c78f263c78f1e3c0264c9931f0f163e1e2c78f1e3d26ef555555555549a8f5551e8f5547aa3d516acaa8003c07801bc0001000043e00c3830e0c783061c383061c3870e0c3830e0c3830eaaa8741a800305dbf78bb7931e3c98bb7a74f80c3efde2edea70f8f1e3c78f1ea3d1e3c78f000264c9931e3c78f85c2c9935126ef1e8f539751e3d53a9d0007800000000000c3830e0c3830e0c1870e0c1870e0c3830e87068003151e3c78f1e4c7931e3c78f1e4c78f1e3c98f1e3c98f1e3c78f1e3c78f1e3c7804e262c9c4c593264c98f878b1f0f163c78f1e4c9bb264d526ef1e9d478f51e8f53a9d0000000780f0037800000c1870e0c1870e0c3830e0c783061c383061c7870e0c3830e0c3830e87068003078f1e3c78f1e3c78f2e5d4000b93265c78f1e3cbcbc597978b5455555555000000000000061c187061c18706bc1830e1c1830e1c387061c18755001e3c78f1e5c78f1e5c78f5e5c9932e3e1e3e1e5d19746a8aaaaaaa000f046001bc00010187061c18f0e0c387061c187061c1875500060f1e3c98f263c78f2e3cb8f1e3c7805c9932e3e1e2c7c3c58f1e3c7aaa4dde8f55555555576a3d5547a3d551eaa3d1ea8b56554001e03c00de0000800021f0061c187063c1830e1c1830e1c387061c187061c18755550ecd4183500060ba1e3e2e4c997aa4e9e5ebea40276faa87d5172f4b274e8f1e3c7d0000041c1c0c3830e4c99326804edf0b85c2e878b1e2d38b2e2c58b5e2cb8b162c58b264c78f1e3c58b162d45a74e80000030e0c3830e0c3c2c7d0f97afaaa93a7264c99340aa276faa93a76949931e3c78fa000000741c187061cb9756ac58b2e5c78f56ac58b002e4c997408593b78f170b85d0f162c78b1e2d38b4e2c58b5e2d78b162c58b2e5c78f1e3c58b162c5a9c5a80000b0f800c3830e0c5870e2c1830ea8f1e3c78f1e3c78f1e5d393264c9a7de3c78f264c78f1e3c7a017264cb972e2cb97163c78f1e5d3974e000000000000c3830e0c3830e0c3830e0c3830e0c3830e003c78f1e3c9934fbc9932e9d00b93265c78f1e3cbaf2e9d4eaa8f55ea2d5400000000000187061c187061c187061c187061d5540078f1e3d7974e4d7934e5d400078f1e3d3cbc5af938b4ea74478f1e8f1e3d3a9d0000000000000061c187061c187060c387060c387061c187438340078f1e3e197864e193865c58b00085c2e170ba16d2a753a3d1ed28f94594000000000002180c3830e0c3830e0c1870e0c1870e0e83a1c1a003c78f1e9d3a74e810b85c2e1742c5c9ede2c5bb162c58b162c58b1e2e858b163e85aa000000000000c3830e0c3830e0c3830e0e83830e0c3800f1e3c98f1e3cb8f1e3c7810b85d0b1742c5c2e162dd8b162c98b162c78b162c58b163c58f162c58b163c58b163c58b553a9d1e3d3a8f1e8f51e8f59df4b50003c07801bc00000000061c187063c1830e1c1830e3c387061c1870741c1830e1c1830e1d0e0d00060f1e3c7972ebc9af265cba800555555552aaaaaaab0a800000000000030e0c3830e0c383061c383061c3d52a800f1e3c79746bcb8f1ebeaaaaaa9555555514001e08c003780002030e0c3831e1c1870e0c3830f54aa000c1e3c7931e3c7971e3c78f02aaaaaa1f0baa55555555677aaaed526a8f5551e8f5547aa8f47ab2a8003c07801bc0001000043e00c3830e0c783061c383061c3870e0c3830f54aaa8741a80030b932fbc78f1e3eaaa8b97277c9972f40014b345d4e8f47b4a33bc58b51e2d4001e0000000000030e0c3830e0c3d503061c383061c3a1c1a000c 24 16777215 10 1023
def hc_62_9 : Nat → Nat := unpackHintV5 0xe17e71d4175acdc993c3928eb7630cb28d35aa1a1da0c256979e499069cd8792367eda2e77d1c271e17c676a9e61019a530f7d52b017520c294afdc44a502b49583e425dbf3bed9c31829b294a0e21b9e421800e1e48ce176db707f7de0001fd 0x1e4c793264c993264c99300993264cd8f1e6cdc6c59b8d8b49bbd555555555526a6d51ea9b4faaa6d36aa8b56554000de0f0078000000000c3830e0c3830e0c1870e0c1870e0c3830eaaa8741a802a3c793263c793363c98f264c99b364c993264c993264c99b3e4c993264c99326013898b2713164c993266c78f366e362cdc6c593272c993549bbcda3d369d4d9b54ea74261f00000003783c01e000003061c383061c3830e0c3830e0c383061c383061c3830e0c3a1c1a005cb93265cb97263cba80005c9932e5e365e365d19746a8aaaaaaa000f003788c00000187061c187061c187061c187061d54007931e5cb97264c9932e5c02e4c9972e3c79b2f1b165e362d5526ef5555555565a9b551e8f54da7d55369b5545ab2aa0006f07803c00000000061c187061c187060c387060c387061c18755550ecd41835001e6c79b365cd93364cd9702170b85c2e858ba162c5cb162c593162c59b162c58f162c59b167c58b162c59b166c58b162d54ea74da3d369d4d9b5677d2d40006f07803c00000000061c187061c187060c387060c3870741c1830e1c1830e1d0e0d002e6cd972e8d19750002aaaaaa9555555514001e006f1180000030e0c3830e0c3830e0c3d52a800f363cb972e6c99b265cb8155555554aaaaaaaacef5565aa4d536aa3d1ea9b4faaa6d36aacaa0006f07803c00000000061c187061c187060c387060c387aa55543a0d40079b1e5cb97364cd932e5c0a89d52ea1f51baa8dc6eaa371faaaaaaaa54ba9d368f4da35366d685d2b3bc000de0f007841f00000000061c187061c187060c387060c38781d541ea90e0d001e6c79b365cd93364cd9702170b85c2e858ba162d55555555559decb549aa6d51ea9b4faaa6d36aa8b550003783c01e00000000030e0c3830e0c383061c383061c383a0eaaa8741a800f363cd9b366c99b266c0363c79b371b166e362cd8f1e6cd9b4d9b368001bc1e00f000001b306cc18f066c183361c183361c1b306cc1b306cc0078f1e0f1ea8f478f1e3c78f1e3c78f1e3cb93265c78f1e3cbc5c5978b8b2e5d47a5dde3d1e972e5cba5cb974000000000000187061c187061c1830e1c1830e1c187061d0e0d001e3c78f1e0f1e3c78f0002e4cb932e5c78f1e3cbc5c5978b8b2e4c9972e3c78f1e5cb974b974b972e5c0000000000000193064c18f063c183261c183261c193064c193064c0078f1e3c78b1e3c78f162e8000aaaaaaaa8b93265c78f1e3dda776bb4eedaa000000000000064c193063c18f060c987060c987aa064c1930016a2c7931e5c78f1e9c7a71e3c7a71f0c78f1e3c266a8b97a1e9d3a3c7ad000f0781bc4e0c3830e3c1830e0c7870e0385c3c78f263c78f2f5543e878faa1e3c78fa87c3e8089dbeaaaaaaa87c2eaa1e5c9932f5348f1e8f1e3d1e3c78faa0000000780f0037800000c9832750781d031e0c18f0e0c18f1e1c9831e0c7d503260c9800307931e4c2170b691e5cb8f1e3c78f1e3cbc71e3c78f16a2c9931e9d3a3c7a8b162c58f0781bc004e3c1830e0c7870e0c3830e031e3c7931e4c78f1e4c7971e3c78f02276fa162e858ba162e170ba858f165c58b162c58f163c58b162c58f162c58f162c58b164c993263c7a3c78f478f1e3c5d0b162c5a2c5a000f01e006f000000000193064c18f060c787060c78f0e4c18f063c1d0b060c587060c587064c19300063befa7dedf4e2e0f8f1e3c78f1e2c58f163c7d00055113b7d5555513264c98f1e3c7a7bedf4ed500000000000003260c9831e0c783064c383064c3d503260c9803bd77ab0f8761bbcf9bd587064c78f263c78f1e2c78f1e3e7d444eaaaa8993264c78f478f51a3aa0007823000de000003260c9831e3c3831e3c393064c193aa064c19300060b45a3c78f4e3e18f1e3d38f4e3c98f263c78f1e1335544c98f4e9d1e3d69387c001e0f03789c187061c783061c18f0e1c99301d0ba1e3eaaaa878f1e3c98f1e3c9d0f1f5543c78f1e3c0aaaa276faaaaaaa6a4993264c78f478f1e8f1e3c7d5107c0000001e03c00de000040eaa0e0c983260c783063c383063c787260c7831f540c98326000c1e3c78f1f0f1e3c7d0b160010b885c2e858ba162cb93265c78f1e3dda776bb4eed1742c000000000000064c193063c18f06ec183261c18326ec3870742c193064c0078f1e3c7971e3c7c3c7bb85c42c5c2c5c2e165c9932e3c78f1e3d1bb768c5d0b0007823000de000003260c9831e3c18f1e0c983260e8583260c98003078b2ea5c7802d45972e3c78b162c7a2c58b478007c04e030e0c380c7931e5c2170b961e9d38f1e3c78f1e3d38f1e3c78b5165cba71ea3c78f478f162c58b1e0f03780270f809c1e0c187063c387061c187018f1e3c98f263c78f2e3cb8f1e3c78142c5c4edf0fa162e858b162e1e2e162ea163c58b162c58b1e2c78b162c58b1e2c58b163c58f162c58b165c9932e3c7a3c78f478f1e3c5d0b162c5a2c5a000f01e006f000000587c000064c193063c1831e1c1831e3c393063c18f0742c183162c3b3062c183161c193064c00183c78f1e3d1e3c78f51e3c000b93265c78f1e3cbcec5979d8b149a8f47a4c9a8f1ea9d2e800000000000470187061c187061c1830e1c1830e1c187061d0e0d00 24 16777215 10 1023
def hc_62_10 : Nat → Nat := unpackHintV5 0xf551f0ee1dcde61602d8ef4ad2cd88cb85d2c17e82bc8d3cb5bdb4a9c6fea435649c0a0b958d9f8c86428aa07986f8ea80a1967782486fdde9672e2c5f39fd5a5d375092734b3d553e3b413791aa327d4528aa752145d91b05900d2379000348 0x264c0007931e4c78f268f1ea4c99326be5e2d7cbc59b1e3cd9349a3c7a931ea23d4ea74000000000000187061c1830e1c1830e1c187061c187061d0e0d001e4c793264c000d9b464c993266c78f368e462d1c8c59349a23d468d3a351a0000000000000c3830e0c3830e0c1870e0c1870e0c3830e870680200f263c98f1e6d38f363f793264c993264c78f264c9931e3c9aa4c993269d3a74e6c78f369d3a74e000000000000c3830e0c3830e0c3830e0c3830e0c3830e0000f1e4c98f1e4cd8f263c99326bc993264c993264c993464c993264c99326a93898b2713164c993266c78f369e5e2d7c9c593269d499349a9349a8f778f1ea3c78f4ea742604c00de00000000000c1870e0c1870e0c3830e0c3830e0c1870e0c1870e0c3830e870680200f263c98f1e4c78f364c993269dfbf4e6c78f36aa4d5fa9b554000000000043e030e0c3830e0c3830e0c3830e0c3aa8028000f263c98f1e4c98f1e6cd93264c9b79b8b6f37166c78f36aaaaaaa8aa13001b800000000000c3830e0c1870e0c1870e0c3830e0c3830eaa0000f1e4c98f1e4cd8f263c993898b2713164c993266c78f36935555555551eef5549aaa9349aaa4d526a9b516acaa84c09801bc00000000043e00c1870e0c1870e0c3830e0c3830e0c3830eaaa8741a8013263c0264e170b262c98b362c78b462d18b162d18b862c58b546a7677cd00000030e0c3830e0c38b160004c993266c7c3466c7c3470b85d0b696170b26936949ca9d368c800000000000030e0c383061c383061c3830e0c383a0e870680004c793264c793264c993a162e858b85c2e170b164c58b162c58b262c98b162c58b262c58b262c58b6e2c58b1e2c5aa4d3a9326a4d26a74dacefa5a82604c00de00000000000c1870e0c1870e0c3830e0c3830e0e8383061c383061c3a1c1a00a0004c993266c7bf466c7bf4755555554aaaaaaaa8a0000000000000c3830e0c1870e0c1870e0c3830f54aa000131e4c9931e4d193264c9d55555552aaaaaaab3bd5526aaa4d26aa93549aadd51eacaa13026006f0000000000060c387060c387061c187061c187aa55543a0d400993264eaaaa80025a3363cd8f968e96689a4d4e9b64458b5262d4260000000000000c3830e0c3830f540c1870e0c1870e870680004c793264c793464c99327551389d544ea89d44ea1f537aaaaaaaa549a75264d49a4d4e9b685d2b3bc2604c00de00000000000c1870e0c1870e0c3830e0c3830f03aa83d521c1a004c98f264c79356170b55600061c187264c7804c9c2e16aab3bc9a4d368f51a8d546aa2d500000061c187438354000993264cd8f7e8cd8f7e8e170ba162e858b85c2d5555555550000000000000187061c1830e1c1830e1c187061c1d0755000098f264c98f264c9932742c5d0b170b85c2e16aaaaaaaaaacef49aaa9349aaa4d526ab7547aa2d542604c00de00000000021f0060c387060c387061c187061c1870741d5550e835000098f264c98f264c993264e262c9c4c593264c99b364c9a4c9934993264cd9b09813003780000003064c383064c383260c983260c983260c983260c9800f263c2e5d49a5cb9b36a3d366cb93265cb8f1e5cbc5c5978b8b2e5d2697366d1e9b2e5cb974b972e8000000000000030e0c3830e0c383061c383061c3830e0c3a0c38306800f263c2e5cb97365cb93265cb8f1e5cbc5c5978b8b2e4c997363c79b2e5cba5cba5cb972e00001700000193064c18f064c183261c183261c193064c193064c005a8b1e6c79b2e4c997366cda3367cd9b368cd9f099aa2e5e91a6da000de3c1e030e0c3830e0c3c2e1e4c797a8dc3e8b97264c9932e5eaa8d9fa366ea8089dbeaaaaa8dd55517264cbd4d26c78f366d19b4d9b36d500000001bc1e00f00000193064ea0f03a063c193060c987060c987aa064c19300264c993085c2da4b8f1e6cb972e6cb9b2e5cb9b2e7c5a8b264d3a6d162c58b0de3c1e00030e0c3830e0c38f263c993264c993264c98113b7d0b170b85d0b1742c5d42cd8b162c78b162cd8b2e2c58b162cd8b2e2c58b162c58b264c993363c79b36dcda6cd9b45d0b162c5a2c5a0006f07803c00000000064c193063c193060c987060c9870742c183161c183161c193064c00993264c9931e2c993a0002a227555544c993266cda6cda8d1a34754000f003788c00000193064c1930e0c987064c193aa064c19300168b479b1e6cd9b368cd9f366cda3367c993264c266aa8993469b6800378f0780c3830e0c3830e4c9d0ba1e3eaa8d8f263c9d1b37555546cf93264c993264c98155544edf5555554d493264c99b1e3cd9b466d366cdb5400000006f07803c000081d541c193064c18f064c183261c183261ea8193064c00b97264cb972e4c7c2c580010b8858b858b85c2cb93265cda3366cd9b468d1a31742c001e006f118000003260c983260c983260c983a160c98326005c9932e10b85cb1b1e3cd9b4e7cd9b366cd9b369cf8b5165cb8f1e9cda9b366d162c58b0de3c1e270f80000c3830e0c3830e3c98f2e5cb93264c9972e050b1713b7c6c5c2c5d0b1742c5d42cd8b162c58f163c58b166c59f162c58b166c59b162c58b162c597264cb9b1e3cd9b369b366d1742c58b168b168001bc1e00f000000000193064c18f064c183261c183261c1d0b060c58b0ecc18b060c587064c19300547931e5c78f366c78f2e6cb97264c9932e5cb97365cdc7367cd9b366cb97365c02e4c9972f17165e2e2cb8f1e6cbc6c5978d8b49bbc9935264c99b47a6d3a9b36a9d2e80000001bc1e00f00000187061c1830e1c1830e1c187061c1830e1c1830e1c187061d0e0d00 24 16777215 10 1023
def hc_62_11 : Nat → Nat := unpackHintV5 0xe42e04ddfd8cd671e3cf3dcdc77df0ba973ab34dd2a97277a4813c9db1b4983d5d8c62f788550381d99f7c55617386346c19db6840f6638d2d5b221b5349f64c2dc74751373d767735b5f02e35e028058c1a0b7f11fa040dc50d0771950001dc 0xf263cb972ea4d2e5cd9b465c9932e5c78f365e462cbc8c59744da3479b4b975365d51a5d0000000118000000c3830e0c3830e0c1870e0c1870e0c3830e870680200f363cdc2e165c5c2c7dbd58b7e2c58b4e2d38b162cb8b2e2c98b262e858b2e5cb97162d45a74e80000030e0c3830e0c3a8001b1e9cd8f7e5c9932e5e4e2cbcfc597264cb97365cb972e5cba25d3a6d4e97400000000000001830e1c1830e1c187061c187061c187061d0e0d001e4c79700264c0d9b465c9932e5c78f365e462cbc8c59749a23d468d3a34ba0000000000000c3830e0c3830e0c1870e0c1870e0c3830e87068013260003c7a8f1e6d1e4c7972f2f165e5e2cb93265cb8f1e6cd8f51e3d4ba4d11ea74ba0000000000000c1870e0c1870e0c3830e0c3830e0c3830e870680003c98f2e3c79b363c797365cb93264c9972e5cbaf2e9e7a35f3d7972e8cbaa5c9932e5e2e2cbc5c5971e3cd97978b2f27165d26974ea9d3aa3dde3c7a8f1e3d3a5d03784c0260000000000030e0c383061c383061c3830e0c383061c383061c3830e0c3a1c1a00a0003c79b363c79b363c98f2e5e7e2cbcfc597264cb971e3cdaaaaaaaa2a80004c0002600000003061c383061c3830e0c3830e0c3830e0c3aa80003c98f2e3c79b363c797365c9932e5e2e2cbc5c5971e3cdaaaaaaaaa3ddeaa97549aa5d2eaabf55536a2d595503784c026000000000087c0187061c1830e1c1830e1c187061c187061d5550e835002e5c0785cbc2e165c593166c58f168c5a3162c5a316ec58b16a8d4ecef9a00000061c187061c187162c000d8f868cd8f868cb93265e9685b0b85c2e165e5a52e9353a6d19000000000000060c387060c387061c187061c1870741d0e0d0001e6c7972e4c9972e5cb97468cbb79e5cb97162e170b162e64ba9d4e6e64379309800dc3e030e0c3830e0c3805c9932e5c7972e3cb9785c2e858ba162e170b165c58b164c58b165c597162c58b165c58b162c58b162c58f162d52e934b9752e9d53a6d677d2d406f09804c0000000000061c187060c387060c387061c1870741c1830e1c1830e1d0e0d002e5c0785cbc2e16aab3bcba4d36a347a3d46a3551aed516a80000030e0c3a1c1aa0006c7bf466c7bf465c9932f42c5d0b170b85c2e16aaaaaaaaa80000004c000000060c387060c387061c187061c1870741d540009931e5cda32e3c7972e4c9972e5cb97468cbaf5e5cb97585c2c58b85c2d555543793098000c3830e0c3830e017264cb971e5cb8f2e5e170ba162e858b85c2d55555555559de97549aa5d2eaa97555547aa2d540de13009800000000000c3830e0c1870e0c1870e0c3830e0e83aaaa1d06a00017264cb971e6c7972e4c9972f17165e2e2cb9b2e5c9932e5d2e9b365cb81bc260130000000193064c183261c183261c193064c193064c193064c009931e013268d1a3466d46a355518f49a4d1ea3538b65400000187061d0e0d264c793263c9a3c98f0099356170b468d1a3366d1a3468d1a8d468d180000030e0c3830e0c38f263c1e3c993264c98f264d47a4c993264c99b1e3cda3938b4727164d269b368f4da3468d3a8d1a34000000000000187061c187061c1830e1c1830e1c187061d0e0d001e4c98f260f1e0004c993264c993363c79b4723168e462c993264cd8f1e6d1a8d468c0000000000000193064c18f064c183261c183261c193064c193064c0280007931e4c78f262c78f162eaaaaa8a8993264dba76eb74edd363c79baa0980000000000003260c983064c383064c3831e0c9d503260c98000f263cd934e9c993264c993269e193264c98b51755329d269b37544c2606f00061c187061c1870078f264c78f266c7931e4e275544e275513a89d42eaaaa89c2eaa270fb7d5544c9a4c9934993264cd8f1e6ea69aa098130037800000000003064c383064c383260c9831e0c9d41e075540c98326002c58000f263c98f1e4e1e3ea170ba162e858b85c13264c9b74edd6e9dba6c78f362e8580000000000003260c983064c383064c3831e0c983a160c98326004c9971e4c98f266c7931f42c5c2c5c2e170b8272c993264cb972e5cd8f1e6c5d0b09817000de0000000c193060c983260c9831e0c983a160c983260003c98f370b85934e9c993264c993269e593264c9cb0b5169c9a93264d264cd9b162c58b2613037800030e0c3830e0c3830600f1e4c98f1e4cd8f263c9c4e858ba162c58b898b858ba162e1f6f164c58b162c58b262c98b162c58b262c58b164c593162ea162c5932693264d264c993363c79b1742c58b168b1684c09801bc0000000161f000060c987060c987064c193063c1930742c183161c183161c193064c007931e4c9a4c99326a6cda3264c993363c79b4723168e462c49a6d1a3cda4c9a9326a8d46800000008c00000061c187061c187060c387060c387061c18743834010079b1e6c9c4e4f27a95cfea1744ea87dbea8993264cd9b94e80000030e0c3c1c1c803cd8f364c5c2e170b1f6f262e58b262c98b4e2d38b162d58b7e2c58ba162c993264cd9b16a740000587c0061c187061c1875000264c993363df9b1e9c993264d3cfc5bf938b366c49932693264d3a6d4ea740000000000000187061c1830e1c1830e1c187061c187061d0e0d00 24 16777215 10 1023
def hc_62_12 : Nat → Nat := unpackHintV5 0xef2595e815c4e38d22dc85c2d1eaa7cae1c2c0ee7db9cdc8af36a6ae9827a71ddf9d567296a5ac8f31dd87ddd581659e7ab5ac737dce6d2d9466dd946031ab593dbd54992947674d3efa1b36ea042ece0728559e1ae35d156d5d0bf65e0002fd 0x79b1e5cb97464d1932e5cd9b3f555401405d4e9b47a008d38488000000000000030e0c3830e0c383061c383061c3d521c1a005cd972e5cf933e4cb973e6c79b1e7cfd55528001753a9d368b160012217000f8010010007c061c187061c187060c387060c387aa4383400185cbd44eaa87d55554a9755a174acef2e0105044200c3830e0c3830f03aa83d521c1a0706172eaaa8f263c78f551e3d6170ba162e858b85c2d5555555554b84c366c0d9b01e0f0590880c3830e0c1870e0c1870e0c3830e0e83aa81c183cb8f1e4c7ef1e3c78f1e3c7c2e1742c5d0b170b85aaaaaaaaaab3bd2e97549a4d51e8f5547aaa8f547aa2d54b84c1e3c079b01e0f059088a09b0061c187060c3870e1c18f060c387061c1870741d5550e8350383078f478f26aa3c7a972eaab0b85c2e1742c5d0b16aaaaaaaaaa4c261b078ecf83b3e02c844061c187061c187060c387060c3870741d540e0c1e4c7ef1e3c9931e3c7932e4e170b85c2e858ba162d55555555559de93549aa8d547a3d526935549aaa8b5526130d83c264c09bf01642228200c3830e0c3830e0c1870e0c1870e0e83aaaa1d06a07061326aaa3c7aaa8f1e8f87d0b1742c58b85c2e170b55555555555366c0d9b026130783c1642203061c383061c3830e0c3830e0c383a0eaa07060f1e4c78f1e3c78f1e3c98fdf0fa162e858b162e170b85c2d55555555559de8f5551e8f5549aa9349aa3d547a3d516aa3cd80f1e04c260f0782c844504d803061c383061c3830e0c3830e0c383a0eaaa8741a81c19bc98f379f078f264c7931fbd1e3d55499355585c2e170ba162e858b5555555555677a5c261b0799cf81f016422030e0c3830e0c383061c383061c383a0eaa07060f1e4c98f263f78f1e3c993270b85c2e1742c5d0b16aaaaaaaaaacef4baa4d546a8f54ba5d552eaaa2d54b84c360f0b9702efc059088a08030e0c3830e0c383061c383061c383a0eaaa8741a81c183c7971e3c78f1e3c7a3cb8fdf0f162e162c58b85c2e170b5555555551e0f0b85c1e0f0590880c3830e0c3830e0c3830e0e83aa81c183cb8fde8f1e5cbaaa8f1e3d4b972f0b85c2e1742c5d0b16aaaaaaaaaa5c261b0788cf8233e02c844061c187061c187060c387060c3870741d540e0c54b97264cb971e5cb8f2e5e162e162e858ba162e170b555555555552e130b9702e7c258ec16422030e0c383061c383061c3830e0c383a0eaa070613268f7a4c993263c78f264d55585c2e170b858b858b55555555526131188c26130590880c3830e0c3830e0c3830e0e83aa81c183c7931e3d793264c9a4c9a3df0f162e162c58b85c2e170b5555555551e0f0984c361b0590880c3830e0c3830e0c3830e0e83aa81c183d18f46bcba326bc9a32eac2e170b170b1742c5d0b16aaaaaaaaaaa370d83c467c179f016422030e0c3830e0c383061c383061c383a0eaa0706131fbc7931e3cb9385c2d54993264c9933e5cd8f1e6c993264cfaf267cf93264c58080130780130f82c44061c187061c1870e0f264c7ef1e3c99385c2d54b933e4c9972e5cd8f1e6cb972e5cfaf2e7cf972e5c58080130780170f82c44061c187061c1870e0f363cdc2e170b85aaaaaa232e8c9a3268cb9b367c58b00050000000079bc0000000440187061c187061c1d0755060c387060c38700366e170b85c2d555550f973e4cf933e5cf9f363cd8f3e2c58002800001f000f80b0010010187061c187061c1d0755060c387060c38700e042e170b85aaaaaab3bd549aaa8f545aa800b2111410061c187061c1870741d5550e8350383001e5c1e5cb8f2e3cb8f1e5cb972e003c780f1e3c7972e5cb93265cb972e5cb972e5cb8f1e5cbc5c5978b8b2e4c9972e5cbcf2f3cb97363c79b6f3ddaeddb74b972e5c0de130098000000000000c983260c193260c193260c783260c1930e0c1930e0c983260c98326003c1e5cb97263c78f2e5cb9751e9b2e5c9932e5c78f365e4e2cbc9c5974993269b368f4da3468d3a5d000000000000061c187061c187060c387060c387061c187438340079707972e003c78172e5cb93265cb8f1e6cbc8c597918b2e4c997363c79b46ed768d2e5c0000000000000193064c18f064c183261c183261c193064c193064c0058b0001e3e878f2f0f263cbd0b1742c5c5c5c2c5c2e27a79ecf4f3d2e4c997363c79b1742c000000980000000c1930e0c1930e0c983260c783260e8583260c98000f363cbc2e165c9932e5cb972e9e7974e9cb972f2c2d4593265cba974e9d366c58b162c37930989c3e000030e0c3830e0c3830600f263cb8f1e5cd8f1e5cbc5c5c2c5d0b1742c5d0b170fb78b2e2cb8b162c98b262c58b2e2cb8b162c58b2e2c58b162ea162c597264cb972e5d2e5d363c79b1742c58b168b1681bc2601300000000000193064c183261c183261c18f064c1d0b060c587060c587064c193000264c797368cb8f365cb93265c78f1e5d1a32e6cd972e5d4b972e5e170b455550de4c2600030e0c3830e0c3805c9932e5cb979e5cd972e5c9932e5cb972e5cb972e5cb972e97154ba5d555555401260975547aa2d595503784c02600000000000030e0c383061c383061c3830e0c3830e0c3aaaa1d06a00a000aa01b1e9e79b1efdf97264cb972e5e797365cb978b8b2f17165c9932e5cb972e5cb972e5cb972e5cb972e5d12e5cb972ea974ba74da5d2e800001bc26013000000001830e1c1830e1c187061c1830e1c1830e1c187061c187061d0e0d00 24 16777215 10 1023
def hc_62_13 : Nat → Nat := unpackHintV5 0xd5c1c0cf8d8dc9997dc0c236ba7d91b1424fab198aa4ad9b9e5d949915529309838cf585889d168195c27d4514736e766bc1eb61968b5b55905429cb4cb9dc48312243b51f3cb5c03619a72c4e7326817320a577172a5f1055b505e29d000178 0x366e170b85c2cf973e4cf933e5cf9f363cd8f3ea0009d4ea74da32014000000b00058007c061c187061c1870741c1830e1c1830e1d0e0d0085c2e170b162c58b262c58b162c58f162d555677d2d4002c8162c058200c3830e0c3830e0e8383061c383061c3a1c1a07060f4793551e3d4b97555aaaaaaaa555555555526130d83c467c119f08844061c187061c187060c387060c387aa55038307931fbc78f264c78f1e4cb93aaaaaaaa55555555677aaa4d526aa3547aa4d26aa93555954984c360f0993026fc22111410061c187061c187060c387060c387aa55543a0d40e0c264d55478f5551e3d1f55543e175554aaaaaaaaaaa6cd81b3604c260f07910880c1870e0c1870e0c3830e0c3830f54aa07060f1e4c78f1e3c78f1e3c98fdf55550f85d5552aaaaaaab3bd551eaaa3d1eaa93549aa3d51eacaa3cd80f1e04c260f0791088a09b0060c387060c387061c187061c187aa55543a0d40e0c1e5d1e5cbaa8f1ea5cb97aaaaaaaa555555555552e130d83c467c119f08844061c187061c187060c387060c387aa550383152e4c9972e3cb971e5cbd555555552aaaaaaaaaa970985cb8173e12c76442203061c1830e0c1870e0c1870e0c3830f54aa07060f463cb972e8c9af265cbab555555554aaaaaaaaaaa5c6e1b0788cf82f3e110880c3830e0c3830e0c1870e0c1870f54aa0706131fbc7931e3cb93aa55264c993363c79b264c9933ebc99f3e4c99308400780130f84880c3830e0c3830e3cd8f2f5554aaaa8a5cba3268c9972e6cd9f00a050000000079bc0000000440187061c187061ea9541830e1c1830e1c00b9b2f5554aaaa8a5cb9f267c9972e7cf9b1e6c79f00a0500000003e004080080c3830e0c3830f54aa0c1870e0c1870e005cbd5552aaab3bd55549aaa8f56552e011088a08030e0c3830e0c3d52aaa1d06a07060f270f264eaaaa878faaaaa2e5e96689a4d468f66458b5262d4984c360f22119f0467c11580c3830e0c3830f540c1870e0c1870e870681c1803c2e044e270f8dd47e3f51fa7d52a74fb0b99de13361320f80101f061c1870741c063c98fde3c793263c78f265c9d44e27513aa1f523aa89d551389d55555552a4d26a347a4c9a934eb42e959de4c261b0784c981308282211580c3830e0c3830e0c1870e0c1870f03aa83d521c1a07060f1e3c7c3c98fdf555544c9d550f1f554acd0f164d268f47b2ca2c5a8f16a4c260f079106cd81b36086c061c187061c187aa060c387060c387438340e0c1e3c98f1e3c78f1e3c7931fbeaa1f0faa87d513a89d43ea1f55550f85d5552a3d3a8f1ea4d268f47b42e959de3cd80f1e04c260f0791b0a08843603061c383061c3830e0c3830e0c3c0eaa0f54870681c184cb93aaaaa878f1e3cb93265e691a3d264d269d9916934d83c2613220b85c456030e0c3830e0c3d5030e4c1970e870681c183cbc3cb97aa1e3e8b972f555555545d26a347a8d1aa34eb325c261b460f76233e08cf84422b0187061c187061c1830e1c1830e1ea90e0d03830b93265cbd5555545cb8f2e3cb97a59a2e5d26aed99162d4b8b52e13258ec882e5c0b9f040187061c187061ea81830e5c387065c1830e1d0e0d03830797a2e4c997a95654ba36e5ea555538f51ac8b45a2d54d86c361b1360c3830e0c3830e832e5e8b93265e02a8ba36e5ea680466d3a6d169b46e6c846230f800ac187061c187061c063cba31e5cbd5555172e8c9b7265cbd54b345d6ea347b322c5a8b52e370d83c88467c0f8200c3830e0c3830f540c1870e0c1870e870681c184c993264d1d54d513265cb972e5e5526aef77aef577bbd577bbc984c4e27220b85c778ef0187061c187061ea81870e0cb8755038315263c993263c9a3264c993aa85c2eaa270ba89c4ea27543ea6f55551385d5552a93526aaef554eb2caaa4d38132604c2627139270a088514e03061c383061c3830e0c3830e0c3c0eaa0f54aa0706232e5c9a3264cb972eb55548c78f2e8cba32e5cba32ebc58b172aabbc7a3d5546270b87c061c187061c3872e0c1872e5d1a32e5eaaa4756f4ba3465e9501955547aaaabbd46a5c4e23119108c4622030e0c3830e0c3d5030e0c3aa81c183d18f2e5cba3268c9972ead44eaa87c3ea475543e17550b85d555548e17554aaaabbd1ea8f5965577971386c1e234608d3849c2822110187061c187061c1830e1c1830e1e075507aa550383078f1e3c797aaaa92e8db971e3e1caaef77a8f5deaef77aaef77970d83c1e441b0d8ef1de030e0c3831e1c1870f540c3830eef5de81c183c78f263c78f2e3c78f1ead44ea77550b85d543e1750f87d43eaaaaaa87c2ea95554ea3d47aabbd965577970d83cd80f1e03c1e46c2822144d80c3830e0c783061c383061c3870e0c3830f03aa83d52a8340e0c263f78f263c797264c993266c78f364c993267cf933e9c9932754804d4e8b00986c00261f2083e0c3830e0c3830e03 24 16777215 10 1023
def hc_62_14 : Nat → Nat := unpackHintV5 0x7d98b03e2b285e24bc4eda4e074669b382084da5a6d8ca86136270b4adf6d095ea444a1b7674cad0ba4f25910cceb27de6203b12f81ba07a4d2d28c6455452bc19a94705c096a3383ea32c1cd0a00cc36944c9e601fa5aa0935a783405680deb060001bd 0x1e8c797aaaa5555552e7cf973e0f3f47f7d522d513a9184554a08b0b8187061c187061ea954187061ea0f03a162c78f1e8c797162e170b553e5cb9f27030e0c38f463d1c2e170b85aaaaaa9f3e7cf9f079f162ea8fef45162c58b262c58b4602c162c58b16a08b5030e0c3830e0c383a0eaa0c3830e0c1870e0c1870e3c78f1eaaaaaa7cf9f079f3e8a0c3830e0c3830e0c3830eaa0c3830e3c78f1eaaaa8f77aaaa935545ab2aa06c1e02228828030e0c3830e0c3830e0c3aaaa1d06a0706172e2c58b162c58b1e3c78b162c58f1e2c5c2e174b42d85c2cba4d1f2d28f47a2d92e130d9b0366c0783c16421b0187061c1830e1c1830e1c187061c1d07438340e0c1e5c78f263f78f1e3c78f1e3e170ba162e858b85c2c597162c593162c58f163c58b162c58f162c58b162c78b162c78b16a9749a3c7a8f4ea3d1eb3be96a2e13078f01e6c0783c1640b1602cd821b0187061c1830e3c387063c1830e1c187061c1d07060c387060c387438340e0c1e2c793162c58b1e3c58b2e5c58b162c58b85c2e170ba5a169349a8d1e9396945b24c261b078acf83b3e02c8456030e0c3830e0c383061c383061c383a0e870681c1803c2e042e164c593166c58f167c5c3162c59f167c58b16a9d3ecef9a099b0982c160b0003e0c3830e0c3830e031e4c7ef1e3c9931e3c7932e4e170b85c2e858ba162c593162c593162c5a3162c58f162c593164c58b162c593162c58b16a9349a8d1e9326a4d3ab3be96a26130d83c264c0980b2058b01608ac061c187061c187060c387060c3870741c1830e1c1830e1d0e0d03830993162c58b162c78f162c58b162c78f163e1f42da56170b85c2e947ca4d268f47a2d65366c0d9b026130783c16421b01830e1c1830e1c187061c187061c1d07438340e0c1e3c98f1e3c78f1e3c7931fbe1f42c5d0b162c5c2e170b858b1e2c58b162c58f163c58b162c593162c593162c58f162c58f162d51e9d478f5269347a3d677d2d43cd80f1e04c260f0782c8162c059b043603061c383061c3830e0c3830e0c383a0e0c1870e0c1870e870681c183c98f163c78b162c58b164c98b162c58b170b85c2e174b42d2e9351a3d2f2d28b6a4b84c360f159f0867c05908ac061c187061c187060c387060c3870741d0e0d038307804c085c2cb8b262cd8b1e2cf8b862c58b3e2cf8b162d53a7d9df345c36170800587c0f830e0c3830e0c380c78f264c7931fbc78f1e4c99385c2e170ba162c58b8bd0b162cb8b162c98b162d18b162c78b162cb8b2e2c58b162cb8b162c58b54ba4d468f4b9752e9d59df4b5170986c1e172e05c05902c580b0456030e0c3830e0c383061c383061c383a0e0c1870e0c1870e870681c183cb8b1e5cb8b162c58f1e2c5972e5e170ba1742e858ba162cba4d468f51a35469d45b25c261b0788cf8233e02c8456030e0c3830e0c383061c383061c383a0e870681c182c58b2e4c9972e3cb971e5cbc2c5c2c5d0b696170b2e5d26d29795768b64b84c2e5c0b9f0963b05908030e0c383061c383061c3830e0c383a0e870681c183d18f46dcba326dc9a32e2c58b85c2e162e162e85b4ab751a3da58728b646e1b0788cf85b3e02c840187061c187061c1830e1c1830e1c1d07438340e0c2e5d47a5cbc2e165c593168c58f168c5a3162c5a316ec58b16aaaabbe64f87c16270187061c187061d47a31e5cb93265cb972e5d1a32eae3d42c5c2e162c5acaef26935554b89c3e1f0187061c187061c3aa97264cb971e5cb8f2e5e170ba162c58b8bd0b170b858b2e2cb8b162c98b262c5d50b162c58b2742c58b162c58b163c58b555de93549aaaaef6564b84c2e5c0ba704e2705902c580b4e0880c3830e0c1870e0c1870e0c3830e0e8383061c383061c3a87540e0c264c7aa4c98b170b8593164c5a3162c58f162c5a3168c58b168c5c3162c5aaaaaef993e1f0589c061c187061c187264cb93264c9972e5cba2c5c2c5acc2e16935deabbddeaabbdde930985c2e271382c844061c187061c187061c1870741d540e0c5498f264c98f264c9932713a162e858b162e170b85c2c593a162c58baa162c58b164c58b162c98b262c58b6e2c58b1e2c5aa93526aaef55577b2b24d38132604c26271382c8162c05a7044060c387060c387061c187061c1870741c1830e1c1830e1d540e0c162c7a31e5cb93265cb972e5d1a32e9d7d4a2c5acc2e16aaabbc7a3d2e1f1389c0061c187061c187468d1a3468d1a3162d50185c2d162c5ef918b16b2aa8f5577a8d555389c46231188c16422030e0c3830e0c3830e0c383a0eaa07060f463d1a72e8c9a7268cbab0b85c2e1742c58b1727a162c58b162c98b162d18b162c58f163c58baa162c58b163e858b162d555577a3d51eabbd9594e270d83c469c13a701640b1602d38208030e0c3830e0c383061c383061c383a0e0c1870e0c1870eaa07060f1e3c7b746dd18f1f0e170b458b858b595547aef55deef5deef4d86c1e0f0d86c16422030e0c3831e1c1870e0c3830e0e83aa81c183c78f263c78f2e3c78f1eac2e170fa162e858b162e170b16ec58b164c58b163e858b162ea858b162c58f162c58b1e2c78b16aaaa3d47aabbd5decac9b0d83cd80f1e03c1e0b2058b0166c110187061c18f060c387060c3870e1c187061c1d07060c387060c387550383098fde3c98f1e5c9c2e164c993266c78f364c993267d3933e7c99326804d4e84000b0581f061c187061c1871e4c98fde3c793270b162cbd0b2e4c997363c79b2e5cb973e9cb9f3e5cb97402ea742000b87c160b03e0c3830e0c3830e3cd8f370b85c2e168cba3268c9a32e6cd9f162c0013a9d368f464011a700000000000000061c187061c1870741c1830e1c1830e1d0e0d00 25 33554431 10 1023
def hc_62_15 : Nat → Nat := unpackHintV5 0xd7ac22d001ebc5aa96bff16eb7ae11b0c5baa61aab9ec1d69709ee8eca1088799480a1f67ba93e754599730c8e6e0d406701c35f39f2566e33502193470248412d75394df83545022f697726e222210d751be54a135a230ada2001ea3c00007a 0x1bcdf2d3e0f263cbd0b1713b7b37170b174aaa8d18b162c58b162c5aaaaaaaa3ddeaaaaaa970986c1e0b20f81f044061c187061c1870741c1830e1c1830e1d540e0c1e4c797a162e276f9b8b858ba85a3162c58f162c58b16aaaa8f77aaaaaaa5d526aa8b56545a2d5516aaaa5c261b0782c8162c05bf04451050061c187061c1870741c1830e1c387062c1830e1d5550e8350383078f1e3cbb74e5c5ef55dfbdaa6df5bd65551eb0d5592e1b0783c361b221150187061c187061c187061ea9540e0c1e3c78f9bd44ea17554de1f6faaa955551eef555655552ea93547accaac8b55645ab32aa5c360f079411b0884451053600c3830e0c3830f50781d552aaa1d06a07060fde3c78fdf0b85dbc5dbd4edd3b7b7aaefde8b55549a8f516aadb4d86c1e0f05906c3628a9b0187061c187061c1d07061c187550681c183c78f1e3d1c8c5c2c5d0b170fb78b6e2c58b262c5d42c58b555547bbd5555516aa5d526a8f5168b566545a2d5599555361b0783c1640b1602cd82228829b0061c187061c1870741c1830e1c1830e1d5550e835038307ef1fbd1e3c7ef265c98f1e4cb972e5c78f1e3c9c4c9c4d55debbd555552e170783c26130b85c44061c187061c187060c383061c187061d540e0c1e3d1e3c9aa8f1ea3c797264c9931e3c78f2f17165e2e2d55555555554984c1e0f0d9b0366c0b85c44061c187061c187060c387060c387061c187550383151e4c7972e3c7971e3cb972e5c9932e5cbc5c5978b8b2e3c797555555555552e130b9702e7c0d83c2e171101830e0c187060c387060c387061c187061c1875503830b93265d6164ede3c5c2e1743c5a3163c58f168c5a3162c5a316bc58b162c5aef1e8f554d86c161b0187061c1870e1c583061c78f1e3d797464d793465d546dd18f1e3c7a3918b472316aaaef47aa3d55361b0783c366c0d9b0361b110187061c187061c1830e1c1830e1c187061d540e0c1746c7c4edf551b552e4c997aa3ebe3e7ea36055201709910107c0360f2211120e0e061c187038309dbe1746c58f162c5aa93264c99b005d0b162c58b3e5c59f2e2c58b4026130d83c1640b05802c3e0222030e0c3830e0c381c19135193268cfd2130987c3e44222070e070642e1e3ea37544edeab1f3f5551f5e4c993266c0aa4083e0440130986c1e4422203a0e0c3830e070642c9dbcd8ba362c78b162d54b93265cd802e858b162c59f5e2cf9f162c5a0170986c1e0b20582c0161f011101870e1c583061c187061c0e0c1e6c79b363c79b5554553e5cf933e4cf97366c000f8b3f1f8f8b50000f807c03600f00f807c040404061c187061c187061c18755060c387060c38700380c078f1fbc78f1e4c78f1e3c793264c9931e3c78f2713164e262d55555555554993264c783c793264d7933e4c99f467d1a2830e0c3830e0c383061c383061c3830e0c3aa830e0c38f1fbc7ef47aa3d52e4c9971e3f78f1fbcba32e8cb93265c783c79f0d9b3e5cba3061c187061c187061c187061c187061c1871e3c7931e3c7ef1e3c78f1e4cb93265c78f1e3c7a32f17165e2e2d555555546aaa97264cb8f078f2e7d1af3e7cba33e5cba345061c187061c187060c387060c387061c18755061c18785c3c98f2f52387d44edf5555548d5555555554b93265ea5f1fa3e0f47548a0c3830f50781d030e0c3d52a830e0c38f263c9c4edf42c5c2e1750b462c58b1e2c58b162d5555555554993264cf83d18ba162c58b5e2cf8b168a0c3830e0c3830e0e8383061c383061c3aa830e0c38f164c9d4c4ea955551aaa4c993267d19f47548a0c3830e0c3830f54aa0c3830f42e878faaa463c98f2755544edf54aaaaaaaaab1faa9793264c99f07a3aa4581d541c187061c187061ea954187061c7931e5e858b89dbe6e2e162ea168c58b163c58b162c5aaaaaaaaaa97264cb9f07a31742c58b16bc59f162d14187061c187061c1d07060c3870e1c18b060c38755061c1871e3c78f9bd44ea17554de1f6faaa95555555554baf3e5c783c7d4be3f5548a0c3830e0c3830f50781d552a830e0c38f1e3c7c2e170b94edd3b79516a9f5e7d78f078f1742cf86cd830e0c3830e0c383a0e0c3830e0c3830e3c78f1e3d1c8c5c2c5d0b170fb78b6e2c58b262c5d42c58b555555555545aa7d79f5e3c1e3c5d0b162c5af167c58b45061c187061c1870741c1830e1c1830e1d54187061c7931e4c993264d78f1ebd5555549933fbc993264cf83cf9f3e7cfa293264c9a301e13264c59389c4c5a822933e4c187061c187061c187061d54187061c1830e1c1830e1c7931e5cb93265cb8f1ebd555554b9f264c9933fbcf83cf9f2e5cfa2973e7d7a301e17465c5978bc5c5a82293264c187061c187061c187061d54187061c1830e1c38706bc1830e1e87a31e5eaa954f972e7c98b061c187 24 16777215 10 1023
def hc_62_16 : Nat → Nat := unpackHintV5 0x869b5b414b809feaaecf612517784e13917aadac471ecec9d66245482ef38bd6823deaa8e614d79f3a4ef7350a873e7d1e093a98fd9b47814bcdf58596d4028b101929f6e47eed843801dd16456f098e6503c64041416870758ac822a60800cc22000019 0xf1e3c7d0b1713b7c3c5c2c5d42c78b162c78b162c58b5547bbd555555516aa5d526a8f5168b566545a2d5516aaaa5c260f0782c8162c059b044504d8030e0c3830e0c383a0e0c1870e1c383160c1870eaaa8741a81c18a8f1e3c78f1e3c78f1e3c78f1e5c9932e5e2e2cbc5c58f1e3c7aaaaaaaaaaa970985cb8173603c1e170b8880c3830e0c1870e0c1870e0c3830e0c3830eaa07060f1e3c78f1e3c7aaa3ddeaaaaaa4d51ea2d5955361b0783c361b111413600c3830e0c3830e0c3830eaaa8741a81c183c78f1e3c78f1e3c78f51e8f1e5c997265cb8f1e3c7978b8b2f17165cba4d1e8f4b9752ea5d2e9702603c1e172e05cd8170b886c061c187061c187060c387060c387061c187438340e0c1e3c78f1e2c78f1e3c58ba59aaaaaaaaaa2e9347b28d1ad2cc970983c1e1b3606cd84421b0187061c187061c1830e1c1830e1ea90e0d03832170f1e3c98f1e3cbd550fa1e3ea878f1e3ea1f0fa56276faaaaaaaa1f0baa879749b4b2751e3d18f1ea8f77cc97099411b01e6c078f01e0f2210d80c3830f50781d031e0c1870e0c1871e1c9830e0c3d521c1a07060f1e3c98f263c78f263cb8f1e3c7ab13b7d0b1742c5d0b170b85d42c78b2e2c58b162c78b1e2c58b162c78b162c78b162c58b2693478f6e3c7aa3dde2d9162d45a752613079b01e3c0783c1640b1602cd821b0187061c18f060c387060c38f0e4c187061c1d07060c387060c387438340e0c1e3c78f1e3c58b1e2c78fa59aaaa276faaaaaa269347aca8d1ad2cc930983c1e1b3606cd84421b0187061c187061c1830e1c1830e1ea90e0d0383285d0f1f555543c78f1e4c78f1e4e1f550f1e3c78f56aaa89dbeaaaaaa4eb4a4d268f1e8c78f547bbe66361404c260f3603c780f0791086c81d541c187061c18f060c387060c38f0e4c187061ea90e0d0383078f1e3c7c3c78f1f42c5a8b458b85c2e170ba162e858b2e9347a2d768d458b516c970983c1e1b3606cd80b210d80c3830e0c3830e0dd83061c383061dd870e0e83a1c1a07060f1e3c78f2e3c78f878f770b85c2c5c2c5c2e165d268f1e8d1a3516a3778b64b84c1e6c1e3c361b059086c061c187063c3830e3c187061c1d07438340e0c1e3c78f1e3cb8fde3c78f1eac2e170f162e162c58b85c2e49971e3c58b162c58b163c78f1e2c78f4fbc5b0b2e13079b078f0783c1641b0d80c3830e0c787061c7830e0c383a0e0c3830e07060f1e3c98f263c78f2e3cb8f1e3c7ab42c5c4edf0fa162e858b162e1e2e162ea163c58b162c58b1e2c78b162c58b1e2c58b163c58f162c58b165d268f1e3c7aa3dde2d9162d16a2c5a752e13079b01e3c0783c1640b1602cd821b0187061c18f060c387060c38f0e4c187061c1d07060c38b0e1c18b060c387438340e0c1e3d1e3cba8f478f765c9932e3c78f1e5d19746bbddea3d77aaef77aa970983c1e1b0d86c2e22030e0c3831e1c1870e0c3830e0c3830eaa07062a3c78f263c98f1e3cb8f2e3c78f1e3c98f263c78f1e3cb8f2e3c78f1e3c78f4e3c78f1e3c78f54b93265cbc5c5978b8b1f0f163e1e2c78f1e3d5de93549a8f51eaaef552e130b9b0366c079b01e3c0783c3617110187061c1830e1c1830e1c18f060c387060c3870e1c187061c187061d540e0c1e3c7a3c7aaa8f1eaaa4c993263c78f1e5e2e2cbc5c5a4d551eaa97554ba4c260f0786cd81b3605c2e289b0187061c187061c1830e1c1830e1c187061d541a07060f1e3c78f49932e3d5264c593262c78f1e3cb972e5d26bbd5deef55deef5deef4981301e0f0b85c2e171de3bc061c187061c187061c187061c18777aef40e0c1e3c98f1e8f5478f8e4c993263c78b1e3c5a3468d1bbd5de8f5deabbddebbdde930983c1e1b0d86c363bc7780c3830e0c787061c3830e0c3830e0c3bbd77a07062a3c78f1e3c98f263c78f1e3c98f1e3c7931e4c78f1e4c78f1e3c78f1e3c78f263c78f1e3d52713164e262c993264c7c3c58f878b1e3c78f49a935577a3d47aabbd553a4cd8132604c260f3603c780f0786c36289b01830e1c1830e1c187061c18f060c387060c3870e1c187061c187061d541a07060f1e3c793264c98f1e3c78743a1d0e8743a4c260f0786c3620703870e1c1a1c3870e1c3a1c3a070e0f1e3c98f1e3c78f1e3d51f0f163e1e2c78f1e3d478f1e3d51eef5361b079b01e3c0783c361b10d80c3830e0c783061c383061c787061c187061c187438340e0c1fbd1e3f7a8f47ef55dfbd264c9931e3c78f468d1a35526a3d5daaa4c260f0786c361b0d88a80c3830e0c3830e0c3830e0c3830eaa07060f1e3f78f1e3c98f1e3c78f264c993263c78f1e4e262c9c4c5aaaaa3ddeaaa93555526aa4d26a8f526935549aaa8b56554984c1e0f09930266c0d86c4451053600c3830e0c3830e0c1870e0c1870e0c3830eaaa8741a81c183c7ef1fbd1ea8fdeabbf7a5c9932e3c7ef1e3f797465d1a5d551eaed5592e130783c361b0d85c51536030e0c3830e0c3830e0c3830e0c3aa8340e0c1e3c7931e3c7ef1e3c78f1e4cb93265c78f1e3c7a32f17165e2e2d55551eef55551aaaa974baa4d26a8f52e975549a4d5516acaa970983c1e173606cd81b0b888a20a6c0187061c187061c1830e1c1830e1c187061d5550e8350383058b5551e4c797a468ea989d4ab4b552355555555552e13119f0467c0d83c8844061c187060c387060c387061c187aa5503832170f263cbd48e1f513b7d55555235555555547bbd552e97549a4d5995595551acacaa97099413f0360f2211144140187061ea0f03a061c187aa55543a0d40e0c1e4c79389dbe858b85c2ea168c58b163c58b162c5aaaaa3ddeaaaaaa93549aadd45a2d5995168b5545a5d55526130d83c1640b1602df82228828030e0c3830e0c383a0e0c1870e0c1870eaaa8741a81c183c593275313aa555551bbd555549bbd55665559deaa4c26231191088a2a030e0c3830e0c3d52aa87540e0c162d556aa91a31e4c793a555a6aa5555555555467c119f026130d83c8844060c387060c387061c187061c187aa550383285d0f1f5548c7931e4eaaa89dbea9555555551eef55655599552697549a4d546b22d599559f850130986c1e44222882840eaa0e0c3830e0c3830f54aaa8741a81c19bcde1f 25 33554431 10 1023
def hc_62_17 : Nat → Nat := unpackHintV5 0xd70719d0c590c73a63c1fd4fbbb592b33a1fa7aae4a089c8924b908af1d683bdcd75cf7c69f6f6681c765c36fa58150852c5544e950c4d385746a5a53f11e539a55b339d822ba5fe21ba7b20ac431c0d2815e18b0e15f30d044407097f0001c2 0x7a31e8d1af468d1af468d585c2e462e162e4750b162c58b462c58b262c58b458ba5aa162c5a753a8f778f1ea3c78f162d91a2c5a8b1eabc5e1b0788d18235e02c8162c05a3044e030e0c3830e0c383061c383061c383a0e0c1870e0c1870e870681c185cb97264d1af2eb48cba3162cb8b2e4c993162c5a32ebcb972f523aaaa51eef1e8f1e5d4ea31785c3e03060c3830e0c3830f513a87a31e5e16b525cba3468d7972f42c5ab5555548eaaa471753b0f5a547bbc78f51e3c7c9da4b8bc978501b0788d18235e11089c061c18781d541c187061c1830e1c1830e1ea90e0d03830ba3465c7a31e5ea165d4e8b6677efde3f7bbcb89c46230d83c44e030e0c3830e0c3830e0c3a1c1a0706550f463cbcd0b162c5d0b168c59753b333bf7ef1fbdde2c5a72e27220d83c160b11380c3830f540c3830e0c3830e870681c183d18f468d1a346dd1ab0b85c2e170b162f7c8c58b4e9d3a795de3d468e441e8b162d85a71386c1e2346234e0b21389c061c187061c187060c383061c1d07061c187038307a31e8d1b7468d1b7468d585c2e170ba162c58b91c2db8b162c98b162d18baa162c5a753a8f778f1ea3c78f16c8b169d389c360f11a30469c05902c580b4e089c061c187061c187060c387060c3870741c1830e1c1830e1d0e0d03830b9747bd268cb9751e972ea8097264cb97465d197465d1aaa3d55dea35552e131188c46231185c44061c187061c187061c187061c187550383151e4c7971e3d3a7463d38f1e5d1972e9cb93264c9a7265cb8f1e3c793264c9a7263c7972e8cbaa5c9932e5e2e2cbc5c5971e3d597938b2f2716aef49aa4d577a3d51eaa970985d38274e06c1e274e09d38270b88200c3830e0c1870e0c1870e0c3830e0c1870e0c1870e0c3830ea1d5038309a3264c99327bd1ea9326a8093264c9a3462d1a3168d1a346aa8f5577a8d554984c46231188c4623110187061c187061c187061c187061d540e0c264cba4c98f268d47a4c993265cb972e5c78f2e935deabbddebbddeaa930985c2e1b0785c2e22030e0c3830e1c1970e0c3830e0c3830eaa07062a3c98f1e4c98f1e4c9a31e4c793264c78f264c9931e3c78f264d197264d393264c993264c9aa4e262c9c4c593264c9ab1e3d5a7938b4f271693526aaef577a3d51eaa934e04c98130986c1e274e09d3827138880c1870e0c1870e0c3830e0c3830e0c1870e0c1870e0c3830eaa07060f363cda35e8d1a35e8d1aa8d79f268c99f466cda300468d1a3363c79b468d1a3468d1a33f23168e3e2d3a9d47bbc78f51e3c79b366cda351a00003c001187c0460000030e0c3830e0c383061c383061c383061c383061c3830e0c3a1c1a006f463d38b3e2d18b5e2f79f03e1c18f363cd9f5e9c99f269d3a800275e8d3a75e8d3aa008dba3363c79b471f167e4e2d1a746bd1af469d3a9d47bbc78f5001e3c078f1e9d468006c004608c3e00000009c061c187061c187060c387060c387060c387060c387061c1874383400182e8d8f8b93265ea8fa78f9fa9009dbeaa375529d01e001b0f81f83838187061c064c99326804edf0b85c2e8d8b1e2cf8b2e2c58b3e2cb8b162c58b01e0b53a6c3e0007c187061c187061c070b1f46e3e7eaaa3e9c993264d02a89dbea93b203c83e001b0f81f0741c187061c065cba33e2c583cf87c0f80cb93265d02164ede6c5c2e1746c58b1e2c78b3e2d38b162cf8b3e2c58b162c0782d4e9b0f8002c3e07c187061c18b0e1c583061c063cd8f367cb9f267c99f2ea0006c78f367e3e2cfc7c5a753a23d001e3c13a9d000d8007c00003e030e0c3830e0c383061c383061c3830e0c3a1c1a000c1e3c9935478f85c2d51eef1e3d478f1ea06c1e000200c3830e0c3830e0c1870e0c1870e0c3830e870681c182c5aaa8f1e3c7d50f1f4d4ab4b54aaaaaaaaaa5c261b3606cd80f07910880c3830e0c1870e0c1870e0c3830f54aa070642e1e3c78fa87c3ea276faaaaaa1eaaaaaa8f77aaaaa5d526accaacaaa3d645ab32aa5c265046c0783c8844504d8030e0c3d41e0740c3830f54aaa8741a81c183c78f1f13b7d0b170b85d42c78b162c78b162c58b5547bbd5555555526a93547a8b56545a2d5516975554984c1e0f05902c580b36088a09b0061c187061c1870741c1830e1c1830e1d5550e8350383098f589d2a9b361c38f163c7d4c4ea95555555549aaab2a930986c364422289b0187061c187061ea95543aa07060b16aaa3c7d550f1e3c7d2aad4c4ea95555555554d9b0366c0984c1e0f221101830e1c1830e1c187061c187061ea9540e0ca1743c7d550f1e3c78faaaa276faa55555547bbd5555955665549aa4d51eb2b2ab1b0a026130783c8844504d840eaa0e0c3830e0c3830f54aaa8741a81c182c797458b16a81b363c78f1f0b985c2e5478f163c78f16aa5d551ea2d554b84c1e0f05906c36289b0187061c187061c1d07061c187550383078f1e3e1730b85d2aa8b162c58f1e2c58b16aaaaaaaaaaaaaa5c260f0782c8366c0d9b044061c187061c1870741c1830e1c1830e1d540e0c 24 16777215 10 1023
def hc_62_18 : Nat → Nat := unpackHintV5 0x8717c2c15c8bdf80cb6f41dfa75ad18b7acca9a21ed2cb6d6861def62e9496d5b5654a5aa004f58df25e571d25726e891a6841f6a59db9d08dfbb8468d5c231acaf967e960a473e04a41fe20c3178edb6185b7ed8233ea00ad9b183c76940c1c88000183 0x2e8d18f268c797463c7a3478f5264d193265cba32e4c99326a97264cb978b8b2f17165c78f465cba35e5cba36e5d3a4d3a3c7aa71ea8f778f1ea3c78f4e974b84c2ebc17af0360f11af04ebc1785c44e030e0c383061d7870e0d783061c3830e0c383061c383061c3830e0c3a1c1a07060fde3f78f1e3dde4cb931e3c9972e5cb8fde3c7ef1e4c993263d1e8f778f779326934e974ba5c2e0fde0fde130985c2e21b0187260cb87061c187061c187061c187438340e0c2e5cb8f263cb971e3cba3c7a97264cb978b8b2f17165c78f2e5cba4d1e3d4b8f55e8f4ba5d2e130b9702e7c0d83c2e1711780c3830e0c1872e1c3832e0c1870e0c3830e0c3830e870681c183c98f49af264d1932e5cb972e3c7a3264c9931e9349bbf7ef1fbdde4c9a746974b89c360f0984c461711380c39306bc3830e0c3830e0c3830e0c3a1c1a07060f263c993464c993264f793549931e935778f51a326883d264c993264d18f1e8d1a3468d1a3468c984c360f1188c4e271188c061c187061c187061c187061c187061c187038307931e4c993464c993264c9aa4c993268c993464cb93264c9a31e3d1a3468d1a3468d193898b2713164d26a3dde3c7a8f1e3c9934e8d46930986c1e234608d38132604d382311889c061c187061c187060c387060c387060c387060c387061c187438340e0c264c98f1ea3c7934793263c9a3264d797264c993264c99346a93898b2713164c993268c78f468dba35e8d7a36e4c7a8f1ea4d3a4c9a8f778f1ea3c78f4ea349af0264c0984c360f11af04ebc1788c44e03061c383061c3830e0c3830e0c383061c383061c3830e0c3a1c1a07060f263d197465d1971e3d1a749a4ddfbf78fdeef46975389c360f1185c44e030e0c3830e0c3830e0c3a1c1a07060f4793264d1a3468c993264cb8f1e8cb972e5c9a3d26efdfbc7ef77a3469d1a5d26130d83c2e231185c44e030e0c3830e0c3830e0c3830e0c3a1c1a07060f263cb972e8f793268cb97547a4cb935778f51a326883d2e5cb93265cb8f1e8cb97465cba32e8cba32e130d83c468c469c4e271185c061c187061c187060c383061c187061c187061c0e0c1e4c7972e5d197264c99346a975e8d1a3464c993265c9932e5c78f465cba3465cba3465e2e2cbc5c59749a8f778f1ea3c78f468d3a34ba5c261b0788d18234e05d18234e08c2e2270187061c187061c1830e1c1830e1c1830e1c1830e1c187061d0e0d038307931e5cb972e5cb97264cb971e3cb978b8b2f17165d26a347a5cb974ba5c261b0785cb8173e05c2e2270187061c187061c1830e1c1830e1c187061d0e0d038307931e5cb8b264c993162d1a347555555545d26c8f51a34f325c261b0788cf8233e11089c061c187061c187060c387060c387aa438340e0c264c58b264cb8ba5a91e4c797aaaaaaaa91d28f1ea5d26c8f66519f0467c0b84c360f2211780c1870e0c1870e0c3830e0c3830f54870681c182c01e6c79b2e4c9973e8d79f3e7cf9f3e7d1a3508aa4e9f47bbc7a3c79720008187061c187061e170f263cbd48e1f45cb93264c9972f5548e91d52b13b7d5555523aaaa2e936964ea8f778f1ea3c78f992e132820360f11a304611095c061c187a83c0e8187061c1830e1c1830e1ea90e0d03830993264d6170b082e3c79b2e5cbaf2ebcb972e8cba31600f778f478f4e97426002c16030e0c3830e0c38f263c993264c993264c9ab13b7d0b170b85d0b1742c5d42d18b162c78b162d18b2e2c58b162d78b2e2c58b162c58b269351eef1e3d478f1e2d9162d45a7526130d83c46dc1b80b2058b01608030e0c3830e0c383061c383061c383a0e0c1870e0c1870e870681c184c98b164c593263c98f27534b555555544d268f1eb4b28f5992613119f0467c0d83c8845e030e0c383061c383061c3830e0c3d521c1a07060f263c993262c593164c9a3468eaaaaaaa89a4d947aa3469e64984c360f119f0467c2211380c3830e0c3830e0c1870e0c1870f54870681c182c01e6c79b3e7cf9f468cfa35e7cf9f264c993580aa3ea747bbc7a3c7c04c1e007c3e12030e0c3830e0c387285c3eaa463c98f2748eaaaa9193264c993264c9ab55544edf555555275a5269351eef1e3d478f1f33050130986c1e234608c221081d541c187061c187061c1830e1c1830e1ea90e0d03830b97264cb972e4c7c2c5a8b45a2e170b858b858b85c2cba4d1e3c78b51bbd1a3516c970988d188c462305908ac061c187061c187061c1870741d0e0d038307931e5cbc4c9932748d1a385c2e170ba162e858b2e9345a3c78f51a34e2d92e130d83c467c119f01642270187061c187061c1830e1c1830e1c1d07438340e0ca264c9932f0f263cb8b16a2c58b6170ba162e858b978b858b2e93458b51e3d45a3c78f45b25c262f3e0bcf81b0782c845e030e0c383061c383061c3830e0c383a0e870681c185c9932eb0b85c01b1e3cd9f3e7d79f5e7cf9f467d18b007bbc7a3c79f4e9d3e7d4b80f003e1f0582c0f830e0c3830e0c38f263cb972e4c993265cbab42c5c4edf37170b1742c5d0b1750b462c58b163c58f162c5a3162c58b162d78b162c58b162c59749a8f778f1ea3c78f16c8b16a2d3a970986c1e23001640b1602c12b80c3830e0c3830e0c1870e0c1870e0e8383061c5870e0c583061c3a1c1a07060f1e8c78f1e5cba3268c9972eacdea2750ba170b5599aaaa9bc3edf5552385d55545d56a3dde3c7a8f1e3e99693acc970d83c1e1b3606cd85046c2210d80c3830e0c3830e0c1870e0c1870f50781d5521c1a07060f1e3c7a32e8c9a3268cbab23170b1742c5c3edf42c58b1723a162c5b7162c593162eaaa5516c8b162c58b162d5aad47bbc78f51e3c78b6458b45a8b169d4d86c1e6c1e3c366c0d9b01640b1602cd821b0187061c187061c1830e1c1830e1c1d07060c387060c387438340e0c1e8c7972e8d19754ba74e5e5778f51a39107b55555523ab7d525c4e1b0788c4627139100c3830e0c3830e0c3830e0c3830f5407060f463cb972e8d1a36e5cbab37a89d48e85c2eaaaa47555545d4ea3dde3c7a8f1e3e93cc971386c1e234608d385049c2211380c3830e0c3830e0c1870e0c1870f50781d5521c1a07060f463cbd548e162c58ba9a165d4ecefdfbc7ef77d2716c971386c1e440b05889c061c187061c187aa061c187438340e0c 25 33554431 10 1023
def hc_62_19 : Nat → Nat := unpackHintV5 0xeadf65e385d6d9b674d13221c8e613c145e8b7c261b5449faf8171a0ffa199a5d6951d229354728c8db28495fe7d85c4767dc26c4e8c6bc42263fdf259e686520df649ea0943fd7b3d01bf35c5cf2eadc6275dd423350a1d856c0e9bbb0003a6 0x5478f1e3c78f1e3c7931e3c78f1f42c5d0b170b85c3edf42c58b262c58b162c593164c58b162c593162c593162ea162c593265c993549bbc7a3d16c8b16a2d3a933604c98130983c1e0b2058b0166c10d80c1870e0c1870e0c3830e0c3830e0e8383061c383061c3a1c1a07060f1e3c7d2cd0f1e2c58f163c7d55550fb7d555135947a3d2e5d69664984c1e0f0d9b0366c2210d80c3830e0c3830e0c1870e0c1870f54870681c18ad544e275513aa275131e3c78f1e3c78f1e3c78fa1755555555543ede4c997264d526ef93ad28f47b324cd8132604c2646c280783c8843603061c383061c3830e0c3c0eaa0e0c3830f54870681c183d264e262e162e858b91dbc58b162c58b262f78ba162c593a162c58b268b4ba8d16c8b168b162d3ef4984c462305902c1622b0187061c187061c1d07061c187438340e0c162d45a2c58f263c98f1e4e1e3ea170ba162e858b85c2c9a2d2e5d458b5568f45b24c26373e0acf81b0782c8456030e0c383061c383061c3830e0c383a0e870681c184c9971e4c98f268c7931f42c5c2c5c2e170b8593265cb975169777ab47a2d9261326170b86c1e0b211580c187060c3830e0c3830e0c383a0e870681c18a8f264c98f264d1ef1e4c793898b170b162f7c2e170b8593262c58b162c58b264c993164c9a7df23d38b6164d384c984c261b0782c84e2701830e0c187061c187061c1870741c187061c0e0c26a4cd802c02e974266c16002c1607c187061c06a3c98f370b85933e7c993264c993267c993264e005804cb9349bbd3a7d0026130266c160b03e0c3830e0c3830e03547931e3c9931e3c993463c98f2713a162e858b162e262e162e858b87dbc593162c58b162c98b262c58b162c98b162c593164c58ba858b164c997264d526ef568f45b22c5a2d458b4ea4c0993026130d83c1640b1602c11580c1870e0c1870e0c3830e0c3830e0e8383061c383061c3a1c1a07060f263c980132606cd9f264c993363c79b4723168e462c9a26d1e80234e08d468000000000000030e0c3830e0c383061c383061c3830e0c3a1c1a00803cd8f367e3f51f93d44e270baaa263edf545c094e930266c0083e407c187061e0e0e01970d9b162cb84c0b9b0581f060c06803cd8f370b8593170b1f6f3e2cf8b162cf8b4e2c58b262c593164c5d0b165c0162d45a74e930266c160b058001f061c187061c18701a8001b1e7cd8f3e7c993264cfc7c59f8f8b264c993366cf97000268a74da9d4e84c002607c003e00007c060c387060c387061c187061c187061c187438340018a931e4c9931e4c993264c9c4c593898b264c993264c993549bbd5498132604c2600200c1870e0c1870e0c3830e0c3830e0c3830e870681c183c78f1f0b85d342cb97162c58b162d569458b55555555555552e130783c1641b3606cd822030e0c3830e0c383a0e0c1870e0c1870eaa07060f1e3c7c2e170fb7d0b162cb8b162c98b1750b162d5526ef555555554ba8f547aa2d16acca8b45aaa2d5554b84c1e0f05902c580b36088a09b0061c187061c1870741c1830e1c1830e1d55543a8306a07066f859bcf83c98f2f17170b1742c5c3ede972e2c58b162c5d2aa8b16aaaaa9377aaaaaaaaa5c261b0782c8d67c0f822030e0c3830e0c383a0e0c1870e0c1870eaa07060f263cbc5c5c2c5d0b170fb78b2e2c58b262c5d42c58b5549bbd555555552ea8d51ea8b56545a2d5516aaaa5c261b0782c8162c05bf0445040187061c187061c1d07060c387060c38755550ea0c1a81c18a93264c9971e5cb8f2e5c993264cbc5c5978b8b2e5cb97577a4d526aaaa930985cb8173e12c76170b8880c3830e0c1870e0c1870e0c3830e0c3830eaa07060f2e4c7972e5cb931e3c7972ea97264cb972e3c797465e462cbc8c5aaaaaaaaaaa970986c1e233e0bcf805c44061c187061c187060c387060c387061c1875503830b8b858fb797164c5d0b16aa5c0363c79b1717a162c58b162c59f5e2cf9f162c5a01701e4002c3e22030e0c3830e0c38f263cb97264cb971e3cdaa2aaa972e0006cd9f462cbc5e462d400000001e6f0000000110061c187061c187061c18755060c387060c387002e4c9972e4c9972e6cbaa2aaa972e0007cf9b1e6c79f3e2cbc5e3e2d40002e00007c002e080080c3830e0c3830e0c3830eaa0c1870e0c1870e003c78f1f0b85c3edf42c58b262c58b262c5d42c58b555555555526130783c1640b1602cd822070e0c3870e1c387a0e1c3870e1c3870eaa070e0f263c9c4c5c2c5d0b170fb78b262c58b262c5d42c58b555555555526130d83c1640b1602d9822070e0c3870e1c387a0e1c3870e1c3870eaa070e13264c993264c9972eaaaaaa4c2633198cc2e22070e0c3870e1c3870e1c3aa81c385c9932e5c9932e5cbaaa4ddeaaaaaaa3d516acaa97098017111410061c187061c187061c18755550ea0c1a81c183c78fde3c78f264c9a3264c993264c9935478f1e3c793268c9975526934993264c993264c7a31e3c78f4723168e462c9c4c593898b269351eef1e3d478f1e4c9a4d49934ea8d46930983cd83c786cd81b3604c98133606c3621b0187061c187061c1830e1c1830e1c1830e1c1830e1c187061d0e0d0383078f1e4c78f1fbcb97465c993264d1932e5d51e3c78f1e4c993264d551a4d2e8cb972e4c9971e3c78f2f23165e462cbc5c5978b8b2e9351eef1e3d478f1e5d1a8d51a34ea8d2e970983c1e1b3606cd8173606cd81b0b886c061c187061c187060c387060c387060c387060c387061c187438340e0c 24 16777215 10 1023
def hc_62_20 : Nat → Nat := unpackHintV5 0xd2376cc656f8befdd6b8e187b139eaaa29c4a421829c45f79515cc8b4674869d2a80718b78a5f377345c7131816a29c25fde9357f1fb53b50f5224644c55744559bf3e39c838ed5333c54a2e6d56261a151f11c21981640f7e810885be000221 0xa8f263cb8f1e5d18f1e5cbc5c5c2c5d0b1742c5d0b170fb78b2e2cb8b162c98b262c58b2e2cb8b162c58b2e2c58b162ea162c5a4dde4c9a93264d5a3d16c8b16a2d3a970985cb8170360f05902c580b0456030e0c383061c383061c3830e0c383a0e0c1870e0c1870e870681c18a000a8017264cb9b1e7e39b1e9d3972e5e397365cb97264cb978b8b2f17165cb972e5cb972e5cb972e93779326a004c9813264d3a6d2e9742e001702e170000000004e030e0c383061c383061c383061c383061c3830e0c3830e0c3a1c1a003c98f2e5cb8001b367cb93265cb8f1e6cbc8c597918b1269b47a008d38234ba00000000000000c3830e0c3830e0c1870e0c1870e0c3830e870680200f363cd97170b85c2c7dbcb8b2e2c98b262cf8b4e2c58b3e2cf8b162e858b0260b53a5c2e000b0f81f061c187061c18750002e4c997363cf9f363cf97264cb978f8b2f1f165cd9712680132609d36a74ba17000b80000007c061c187060c387060c387061c187061c187438340152e4c9972e3c7972e4c9972f17165e2e2cb9749bbc9935264c9aa5d2e130b80005c40187061c1830e1c1830e1c187061c187061d0e0d038307931e4ea8993a162d556a9a956955555555554984c360f1b9f06e7c22110187061c187061c1830e1c1830e1ea9540e0c1e4c79389d44ea175544e1f6faaa926ef555555555549aa3547ab32ab2aac8b566554984c360f2827e11088a08030e0c3830e0c3d41e07554aaa8741a81c183c78f1f0b85c3d858b162c58b264c58b55a5162d5555555555554984c1e0f05906cd81b360880c3830e0c3830e0e8383061c383061c3aa81c183c78f1f0b85c3edf42c58b262c58b262c5d42c58b49bbd555555555526a3d51ea8b56545a2d5516aaaa4c260f0782c8162c059b044504d8030e0c3830e0c383a0e0c1870e0c1870eaaa8741a81c183c58f1f530faa5555555551ea5d55954783c2e1722111040187061c187061ea955541a070651327543c78f1e2c5aaad552aad4c3d5555555554984c366c0d9b01e0f22110187061c1830e1c1830e1c187061ea9540e0ca89c4ea270f1e3c7d0baaaaaa1f6f49bbd555555555526b2aaccaa8f547ab2b2aa4c2646c280783c8844504d8030e0c3c0eaa0e0c3830f54aaa8741a81c182c98b168d16a9f3e1c383063c98f270b85c2e4993164c9939516aa4d51aaa2d554984c360f05909c4e2880c3830e0c3830e0e83830e0c3aa8340e0c1e4c79385c2e1722c58b164c98b174aaa2c5aaaaaaaaaaaaaa930986c1e0b21b9f06e7c110187061c187061c1d07060c387060c38755038307931e4e262e162e858b87dbc593162c593162ea162c5a4ddeaaaaaaaaa8b5526a8d51ea8b45ab32a2d16aa8b555526130d83c1640b1602df82228200c3830e0c3830e0e8383061c383061c3aaaa1d06a07060f264c793263c793264c9931ea93264c9a31e3d1a3918b472316aaaaaaaaaaa4c261b0788cf82f3e023110187061c187061c1830e1c1830e1c187061d540e0c271385d131f6faa550261b1e3cdd51f5f1f3f5552004c1e0107c4483838187061c3813366c58b3e04c1e7c4060c384c5c2c7dbc98b262e858b5516a04c363c79b1742c58b162cfaf167cf8b162d00260f00161f110187061c187061c383c98f264c993266c78f368aaaaa004c981b367d18b4723918b50000000079bc0000000440187061c187061c187061d541830e1c1830e1c00993264c993264cd9b45555500264c0f9f363cd8f3e7c59f8fc7c5a8000013000f8002002030e0c3830e0c3830e0c3aa83061c383061c380700993264c993264d26ef55555549aaa3d516acaa930980088a08030e0c3830e0c3830e0c3aaaa1d06a0706131e3d51e4c9aa8f54793547a385c2cba32e8c9a3d46a5d2e97554b9b0d86c3626c187061c187061d064c98f264c793007a4c9932601b470b85a3468d1a3369d36a34da4c36231187c00462b061c187061c187018f264c793263c7a93498f264c993264c9a31e3d1a3918b4723164d26a347a8cbaaa8d26130d83c467c0f808c40187061c187061c1830e1c1830e1c187061d0e0d0383296687931e4c78f262c78f162eaaaaaaaa89b25cbad2ab47b324c26373e0acf81b079108ac061c187060c387060c387061c187aa438340e0c51e4c79b267cf93264c993264cfd3264c9931605504132e4d26ef4e9f4987c00261b2083e0c3830e0c3830e035478f264c78f268c7931e4e275544e275513a89d42eaaaa89c2eaa270fb7d5544c997264d526ef568f6964eb324c0993026130d83ca082211580c1870e0c1870e0c3830e0c3830f50781d5521c1a07060f478f85c2e85d0b162c58b262c5a3162c58b268b4ba3d16c8b168b46930986c360b20582c436030e0c3830e0c383a0e0c3830e870681c182c5a8b458b1e3c78fa1e3c7c3c7c2e1742c5d0b170f170b164d16972ea2c5a8f47a2d926130d9b0366c0783c16421b0187061c1830e1c1830e1c187061c1d07438340e0c 24 16777215 10 1023
def hc_62_21 : Nat → Nat := unpackHintV5 0x862a95c0f0895f4e4a8f1f220751cf738a8799b45c3ad2b5de668ab431b264d70674cb065f35085eba6a766d23c45e895e214015269e616a4e47ba46c158a32bed317707bcad9b7a4ed5fe241ad40e9ddc0639c54242b690def0983a7d400bc45e000178 0x1e3cbd513a85d5543edf555172e3c7d4d3545c0d83ca0822001832e0c783a83c0eaa81830182c5a8b458b1e3c78f1e3c78f1e3c78f85c2e858ba162e170b2e5d16972e5cb8f47a2da92e130d9b0366c0783c16421b0187061c1830e1c1830e1c187061c1d07438340e0c162c58f1e3c78f1f43c78f878f858b858ba162e858b878b858b2e4c9972e5cba5cba3c78f1e2e85970985cb8173603c1e0b20d86c064c193060c987060c987063c18f0742c193064c260c1e3c78f85c2e170b465d793464d7971e8fa9458b59162d3a9d1e8f1e3d162d9162c58b361b0783c1641b3606cd821b0187061c187061c1d07060c387060c387438340e0c1e3c78f85c2e1f6fa162c58b162c98b1750b162c78f1e3c5d0b162c5a2c5a6c360f0782c8162c059b0361b0183063c18f0742c183161c183161c1830d83078f1e3e959aa1e3c78f1e3c78faaaaaaaa2e5d64bbbc7a3d2e5cbcc970983c1e1b3606cd84426c366c061c187061c187060c387060c387aa438340e0c1e3c78f1e3ea1e3c58b1e2c78faaaaa87d55517264cb971e3c78f2e5cba5cbb545c0980f0785cb817361106c3603064c183260c7831e0c1930e0c1930f540c983261306172e9c9af265cb8f1e3c78b16a3c58f6aa96a6a8ba9da87a3c78f66a4b86c366c0d9b01e0f22103600c3830e0c1870e0c1870e0c3830f54870681c19513a878f1e3e85d555550fb7972f4d48f1e3c7d5170d91b0a01e0f220d86c060cbc0eaa0e0c7831f540c186c188f1e8f51e4c5c2c7dbe170b262dd8b262c98ba562e18b162d38b4e2c58b162c9931e3c99316a74d86c161b0187061c187061c78f1fbc78f1e4c78f1e3c793898b858ba162e1f6fa162c58b89d0b162c98b162c593164c58baaa858b162c593a162c58b162c593264c98f1e3c793264d264d1742c58b168b16930983c1e132604cd80b2058b0166c0d86c064c193063c18f060c987060c9870742c183161c183161c193064c260c1ea3c7aa3d1932e2e163edf0b8597165c593164c5d2b170c58b169c5a7162c58b165cb8f47bbcb97a162d45a74e9b1e6c360b0d86cd830e0c3830e0c383063c78f263c78fde3c78f1e3c9c5c5c2c5d0b170fb7d0b162c5c5e858b165c597162c593164c58baaa858b162c593a162c58b162c597264cb8f1e3c78f465cb974b9745d0b162c5a2c5a5c260f360f1e172e05cd80b2058b0166c0d86c064c193063c7831e4c183261c183261c1d0b060c587060c587064c19309832170f263cbd50f858b162c98ba17517264cbd5231e3d18b162c597099106c1e0b05800c98327540c783260c583160c9832613060fde3f78b1e3ede4cb931e3c9c2e176f176f170b170b165cb972e3c78f1e4c99326ec98ba165c2e0f0784c984cd82c8361b0193064c18f063c183260c1930742c193064c260c162d45a2c58f263cb8f1e9d18f1e9d1c2e1742c5d0b170b85972e8b4b972e5d3a3d16c970989cf8273e06c1e0b211380c3830e0c1870e0c1870e0c3830e0e83a1c1a07060b162c7931e5cb8f1e5e1e3ea162e162e858ba162e170b2e5c9932e5cb974b975b8f1edc5d0b2e5c26172e05cf81b0782c80060c983064c183261c183261c18f064c1d0b064c1930983078fde3c98f1e3c9d42e164c993272d51356ec9a74e4c99316a2c9931e3c99326a726a2c58b164c361b0d86cd830e0c3830e0c383063c98f1fbc78f1e4e162c597a165c9932f2b17aa2eae3974e9cb972e2d4593263d1eef2e5d4ba74e8b162c5970d86c361b360c3830e0c3830e0c1934e9c993264e47b716c2c9932ea4c5a8b2e4cba7164c9934edc58b162c58b168b16a9c4e131389d3830e0c3830e0c383065cb97264d3a791e5c5b0b2e5d1a9716a2c993265c9934e9d3b7162c58b164d458b16a71385c4e274e0c3830e0cb870e5c1830e0c18f1f0b85c2e169cb934e4cbd28f6162d6458b4ea753a3d162d9162c58b0360f05909cf8273e089c061c187061c1870741c1830e1c1830e1d061c18340e0c1e6c79b85c2e1709cba7269c9a72e6cd8000b160009d4e9b47a2d93e7cf8000000000000030e0c3830e0c383a0e0c1870e0c1870e8706800f363cdc2e170b83e5cf933e4cf97a000162c001fbf363c79b1742cf9f4f9f3e801f036000b00058007c06cc1b3063c19b0742c1833e1c1833e1c1b306cc00183c7c2e162e858b87dbc58b162c98b1750b162c78f1742c58b168b1681b0782c8162c058003060c7830742c183161c183161c183018a8f2e4c7972e3cb8f2e3c7972e5cb9749931e3d478f1e3cb972e5c9932e5cb972e5cb972e5c78f2e5e2e2cbc5c5a4dde4c9a93264d3a747a7499354e4d4ba5d2e130b9702f1c0d83c571c1dbb02e1711380c3830e0c1870e0c1870e0c3830e0c1870e0c1870e0c3830e870681c183cb931e5cb97498f1e3d4b972e5c9932e5c78f465e462cbc8c59749a8d1e9326aec9aa5d2e130d83c467c1d9f00b88030e0c3830e0c383061c383061c3830e0c3a1c1a07060f26a3c78f478f2ea8f1e3c78f1e3c7971e3c78f1e3c7971e5c7c3c58f878b2e4c9972e5cb972e5cb971e3c78f1e4d478f549bbc9935264c98f4e8f1e974ba3cd80f1e05c26172e05cd80f0785c2e21b01830e1c1830e1c187061c1830e1c1830e1c187061c187061d0e0d0383058b5162c5a3e1e3e878f1e3c78fa162e858b85c2e170b162d49935169347a3d16c9b3606cd8170983c1e0b210d80c1870e0c1870e0c3830e0c3830e0e83a1c1a07062a3c78f1e3c78f1e3c78f1f0b85d0b1742c5c3edf42c58b2e2c58b262c58b2e2cb8b162c58b2e2c58b162ea162c5a4dde4c9a93264c7a3d16c8b16a2d3a970985cb8173603c1e0b2058b0166c10d80c3830e0c1870e0c1870e0c3830e0e8383061c383061c3a1c1a07060b16a2c58b478fa1e3cbc3c98f2f42c5d0b1717170b170b858b16a4c9a8b499326ab47a2d9567c239f02e130d83c16422b01830e1c1830e1c187061c187061c1d07438340e0c51e6c79785c2cb93265cb972e5cfc72e7cf972e5e005804dde4d264d3a7d0980170f86c160b03e0c3830e0c3830e03 25 33554431 10 1023
def hc_62_22 : Nat → Nat := unpackHintV5 0xd4a610d3c438cec93fc729e8bfd9d4b8a9ccb1adbfaa81cba33dd19e0d4c951a3d8c563186657c839cb27d6d8c74364e6c5df66485f65cc5f054f1f54ff14047e6034385183802e13049ee28f5d520ee021a49a914bd630dc5be0761990001d8 0x3c98f263c793264c9931f4acd5555555551349a8d1aca377a3468e64984c360f139f04e7c2214e274e030e0c3830e0c3834e0c1870e0c187261c3d520c3830681c19206f4e9f1583264c98f264c7d4000f164c9d0113aaaaa368d5aad46fd19b118231187c00564c9830e0c383260c980c793263c9931e3c58b262c98faaaa2755555544c993268c78f468d46d5130986c1e233e07c2200193064c18f260c993060c987060c987aa064c193098307931e4c9a4c99326a8d1a3aaaaa9a5269351a347a76969664984c360f119f11823467cf8442270187061c187061c1830e1c1830e1ea90e0d0383058b5262c9a9c7c3863d393264c9d2d4d555544d264c9a9d4ecd4a73e09cf81309811089c060c387060c387061c187061c187aa43930693038307931e4c009930366cfd155005013264c99b1e3cda3468d469d1b5400000f37800110000003260c9831e0c983064c383064c3d503260c98013260006c7a7466c7a7464c99327400145547cf9f269353a6d992200000000f80026f0001a7060c387060c3930e1c187061c187061ea90e0d00162c000d8f3e6c79f3e4c99327400145547cf9f4f9f4993264cd9b7f5440013000f80101f00060c987060c987064c193064c193aa064c193026050b87d544c9932755544edf554d493264c9d541404c26044040eaa0e0c983260c98327540c9832613060f263cb972e4c78f1e5cb8b16a2d162e170b85c2e858ba162cba4d468d16a3468d18b64b84c360f139f04e7c059089c061c187061c187069c1830e1c1830e9c3870741d0e0d03830797263cb972f131e3c7d0b162e170b858b858ba162e858b2e4c997463c7a346ed768d1742cb84c360f119f0767c059000c983260c783260c1930e0c1930e0e8583260c984c1924cb8f4e9c78f1e3c5b0b2ea3c78f16a2d38f465cba7163c78f162c58b162c5a2c5a9b0d83c361b360c3830e0c3830f24cba31e3c58b6163c3e5cb8f1e2c58b163cf830e0c3c932e8d3a31e3d3a716c2cba974e9c5a8b1e3c7972e9c78f4e9c58b162c58f5162c5a9c4e274e0ad389d3830e0c3830e0c38f263cbc2e170b85972ea4d2e5d1a3462c5ac8b165d26a3468f1e3d3ef45b22c5a3d162c58b52e130d83c164233e230468cf9f044e030e0c3830e0c383a0e0c1870e0c1870e870681c185c9932f0b85c2e174a4d2f271e9c78b16b22c5972e934ba753a2c5b22c58b165c2600b2139f04e7c11380c3830e0c3830e0e8383061c383061c3a1c1a07060f263cbc2e2170b2e5c000d9b3e2c580017264cb9b1e3cd8ba168d1a351a746800003cde000000b0580003260c9831e0c983a160c1930e0c1930e0c98326005c9932f0b885c2cb970004e8cd8f363d3a3162c000ba4d4e9d36bf16c9f3e7c0000f80000000000c3830e0c3830e0e8383061d3870e0d383061c3a1c1a005c9932f0b885c2e8000f9f363cd8f3e2c580017264cb9b36fc5d0b3e7d3e7cfa1700003e02c0016001f0193064c193064c1d0b060c987060c987064c19300264c99385c2e170b0e1c3870e1c3870f41c984c663305901c0e070e0e0e1c3870f41c3870e1c0e1c2e4c997a162e276f85c2c5d42c58b163c58b162c597264cb8ba162c58b458b4b84c01640b1602c00193064c193064c1d0b060c58b0e0c583062c383260c984c184e270b91e3d1ea3ea95c793a7aa263edf55544c98f1f29d264e0d86c3641c1c0c3830e3c78fde3c78f2713aa2713a85c3c78f1e3c9d550b1744c5d55544e1f6faaaaa270baaa264c9931e8c78f1e3ea69264c9a4c9b544c260f360f1e5046c09930266c220d86c064c193063c18fa83c0e8183261c183261ea8193064c260c1fbc7ef878f17bc997263c793aaadf5beaa8b972e5c7ef1e3f78f264c993aa2e1707ef07ef0984c88361b0193260cb93063c18f064c193aa064c1930983296687931e5c78f4e8c78f4e8eaaaaaaa8b9764b972e5d3a3c78f664b84c4e7c139f0360f2211380c3830e0c1870e0c1870e0c3830f54870681c1950f263cb971e3cb8b1e3c58baaaaaaaaa2e4c9972e5cba5cbadc78f6f545c26172e05cf81b0791000c983260c1932e1c3832e0c1930e0c78327540c9832613060f263cbd513a17542c58b163c5d0b2e4c9976e3c7b7aa162c58b2e130d83c88160b00193064c18f064ea818b160c58b064c1930983078fde3c993264c98b5163c78f26ac9bb162c5a7269c9932733543c7d1353b46c79b0d84c36030e0c3830e0c38f1e5cb97864d3932e5c58b51ec3175555534a5d4ea747b54d4970360f139f04e7c2211380c3830e0c3830e0c1870e0c1870f54870681c183cd8f2e5cba7269c9972e6cd800551500501753a6d1e9f3e7e9980000000000000187061c187061c1830e1c1830e1ea90e0d001e6c7972e5cf933e4cb97162c002a8a80280bbf2e6c78f367cfa7cf9f6a82e001b002002000f80d9832e0c783360c19f0e0c19f0f540d98366000c 24 16777215 10 1023
def hc_62_23 : Nat → Nat := unpackHintV5 0xd8bd5bcddeb8ccec3cc82d30ba6f70b4bd6cabae44ab5416a5518198573f90fdd6884a2d802e0778d9d57141e66a3dc16345be5ca1a9564d954f75b64a3d4e41aa2538924630261b27fa0b20a1d619adbd1221e30a85e7060121057c2100015f 0x793263f78f1e4c9972e5cba297266c9932e5cb9b1e3cd800173e7c01742d001e005c3e22030e0c3830e0c38f1e4c98f263f78f1e3c993265c9932e5c78f2e5cb972e5cb972e975551aaa5d2eaaaaa5d47aa4d526a8f54ba8b56554b84c360f0b9702efc0b85c511410061c187061c187060c387060c387061c1875506aa1d06a07066f1402e172e1f158f264c7ef2ea5cda9b1e3c99354000085c2cb972e5cb805d13e00170f85c0f830e0c3830e0c38f1e4c98f263f78f1ea4c9971e4c9a8f1e8c98f1e3c99326aa5c9932e5c78f2e5e2e2cbc5c5972e5cb972e5cb972e934ba3468f51972e5cb972e5d52e972e972e5d2e130d83c05605cb81702e1711580c3830e0c3830e0c1870e0c1870e0c1870e0c1870e0c3830e830e0c1a07060f4997268f470b162cbc5cba8b46a2ea162cb97468cb971745cb8b945972ea71382c4e274e0c3830e0c3830e0c18f263cb8f1ea4d2e3c99351e932e4c9972e3c797938b2f0b2e5d26974e8f4b972e9d2e5cba5c261b0789cf8273e01711380c3830e0c3830e0c1870e0c1870e0c3830e830e0c1a070600174e4c98f498f268f263c02602a000042e170b85972e6cd972f2d3a7496a5cb970d81f000b817056030e0c3830e0c38306031e3c9931e4c7ef1e3c0009930001e3c793264c00b93265cb8f1e5cbc5c5978b8b2e5cb972e5cb972e4c997363c79b972cfa7e5a5cb977e5cb972e5cb970b8006c002e05c2e000005c000193064c18f064c183261c183261c183264c183264c193064c193064c00183c98f0b97000366c000b93265cb8f1e6cbc9c597938b2e934da3d3e7cfa74ba00000000000000c3830e0c3830e0c1870e0c1870e0c3830e8706800f263c1e3c0009930002e4c9972e3c79b2f1f165e3e2cb93265cd8f1e6cf9f4f9f3e972efc2e001b000b8005c003e03260c9831e0c983064c383064c383260c983260c98003078f264c7931fbc78f1e4c9932e4c9972e3c7978b8b2f17165c9932e3c7974ba5cb970986c1e17000b800c983260c783260c1930e0c1930e0c983260c9832613060f263cb972e4c78f1e5cbd2cd5555555517499326a346ca3468d1cc970986c1e273e09cf8442270187061c187061c1830e1c1830e1ea90e0d03830797263cb972e2c98f1e3c58baaaaaaaaaa8b93265d18f1e8d1bb5da36a8b84c360f119f0767c2200193064c18f064c183261c183261ea8193064c260c1e4c7972e5d49a5cba3468eaaaaaa694ba4d468d1e9da5a5992e130d83c467c119f08844e030e0c3830e0c383061c383061c3d521c1a07060b16a4d2e2cb93265e18f4e9c7c3aaa9a5aa2e5d2697a93a9d9a92e13139f04e7c02211380c3830e0c1870e0c1870e0c3830f54870681c183c98f2e5cb8001b367caaa80280b93265cd8f1e6d1a346a34e8daa0000000000000064c193063c193060c987060c987aa064c193002e5c000b93265cd8f4e8cd8f4e8ca80282a8ba4d3e7cfa74db3200000000000000c3830e0c1870e0c1870e0c3830f548706800b160005c9932e6c79f3e6c79f2a00a0aa2e4c9973e7d3e7cfa6cdbfaa0b801000010000c983260c1930e0c1930e0c98327540c98326010b8b93265ea87d44edf5555545c9932f534d517099410044003260c9d41e0740c98327540c9832613060f263c98f1e4c993264c78b16a2d162e170b85c2e858ba162c9a4d468d16a32e5cb8b6a4984c360f139f04e7c059089c061c187061c187060c387060c3870741d0e0d03830793263c9931e3e89c4c78b162e262e162e162e162e858ba162c993264d18f1e8cb972e972e8ba164c261b0785cb8173e02c80064c193063c193060c987060c9870742c193064c260c1e4c98f264e170b85c2c9a4c99326a5cb97162d6458b269351a347a745b22c5a8b16a4c261b0782c8467c119f044e030e0c3830e0c383a0e0c1870e0c1870e870681c184c993270b85c2e164d2752972e5c7971e5c58b59162c9a4c99353a9d162d9162c58b2613005905cf8172e089c061c187061c1870741c1830e1c1830e1d0e0d038307931e4e2170b8580132605cb97162c000993264cd8f1e6c5d0b468d1a8d3a340000000000000193064c18f064c1d0b060c987060c987064c19300264c993885c2e16004c9827466c79b1e9d18b160004d26a74da2d92e5cb8000000000000030e0c3830e0c383a0e0c1870e0c1870e87068013264c9c42e170b00a02e5cb8f2e3cb8b160004c993266cdbf1742cb974b972e801300016000b000193064c193064c1d0b060c987060c987064c19300264c99389dbe858b85c2ea162c58b1e2c58b162c993264c5d0b162c5a2c5a4c2600b2058b016000c983260c983260e8583062c383062c383260c984c184c98f164c9d44eaa91aaa351aa8f49b2a3d546a7995468c7e2ad1581c3830e0c3a0d0e0d4fa01f0f93263c9931f2b543c593274ac4eaaaa91a8d468d1a3468d46a3462b1182b0e1d583061c1930e4c187061c183 24 16777215 10 1023
def hc_62_24 : Nat → Nat := unpackHintV5 0xadfca544d5ca3c934bdee696ad442b767912a1131d2607318a304bf5c84b73200025b 0x5cba934b971e3c78f1e3c7a3c7a97264cb97938b2f2f163c78f1e5cba4d2e3c78f1e8f1e3d4e974b84c366c0d9b01e0f0d85c436030e0c383061c383061c3830e0c3830e0c3a1c1a07060f1e3c793264c98f1e3c7870e1c3870e1c3870e1c3930983c1e1b0b81c0e070e0c3830e1c3870e1c3870e1c381c383c78f263f78f1e3c78f1e3cb93265c7c3c58f878b1e3c78f2e4c9971e3c7a3c7a3c78f1e5cb970983c780f3603c1e1b0b86c3603260c983063c787063c1831e1c18f063c193064c193064c260c1e3c7931e3c7ef1e3c78f1e4c993264c78f1e3cbc5c5978b8b264c9931e3c78f2e5cba5cba5cb972e4c260f0785cb8173605c2e1b0d80c983260c7831e0c1930e0c1930e0c983260c9832613060f263c993498f1e3d539751ebb264c9931e3e3c9c5a7a38b2693264d4e8f4993269d4e930986c1e273e09cf802270187061c187061c1830e1c1830e1c187061d0e0d03830783c980132606cd80013264c99b1e3cda7938b4f27164c9a4d266d1e9f3e7d3a9d0000000000000061c187061c187060c387060c387061c1874383400783c9800f1e06cb80013264c99b1e3cd9f8f8b3f1f164c993266c78f367cfa7cf9f5fbf002606c002607c0000f80c983260c783260c1930e0c1930e0c983260c98326000c1e4c7ef1e3c9931e3c793264c993263c793898b2713164c993263c793264d264d26130d83c264c0980003260c9831e0c983064c383064c383260c983260c984c1955543c78f1f544c993263c78f1f104c260f0786c365503260c9831e0c783260c984c183c78f1e2c58b162c58b164c993263c78f1e2c58b164c260f0782c161b0d80c983260c7831e0c583160c9832613061326a4c993478f51e3c7a3c78f1e9e5e2d7c9c593264c98f1e3c78f1e3c9a4c99347a3c78f53a9d366c0d9b026130783c361b103600c1870e0c1870e0c3830e0c3830e0c3830e87260d2607060f1e4c78f1e3c78f1e3c98fde3c7c3c58f878f164c993263c78f1e3c7a3c78f4993264c78f1e3c79b01e3c0984c1e0f0d86c361b01831e1c1831e1c193064c18f063c193064c193064c260c 23 8388607 10 1023
def nh_62 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_62_24 (Nat.sub p 768)) (hc_62_23 (Nat.sub p 736)) (Nat.blt p 768)) (Bool.rec (hc_62_22 (Nat.sub p 704)) (hc_62_21 (Nat.sub p 672)) (Nat.blt p 704)) (Nat.blt p 736)) (Bool.rec (Bool.rec (hc_62_20 (Nat.sub p 640)) (hc_62_19 (Nat.sub p 608)) (Nat.blt p 640)) (hc_62_18 (Nat.sub p 576)) (Nat.blt p 608)) (Nat.blt p 672)) (Bool.rec (Bool.rec (Bool.rec (hc_62_17 (Nat.sub p 544)) (hc_62_16 (Nat.sub p 512)) (Nat.blt p 544)) (hc_62_15 (Nat.sub p 480)) (Nat.blt p 512)) (Bool.rec (Bool.rec (hc_62_14 (Nat.sub p 448)) (hc_62_13 (Nat.sub p 416)) (Nat.blt p 448)) (hc_62_12 (Nat.sub p 384)) (Nat.blt p 416)) (Nat.blt p 480)) (Nat.blt p 576)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_62_11 (Nat.sub p 352)) (hc_62_10 (Nat.sub p 320)) (Nat.blt p 352)) (hc_62_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (hc_62_8 (Nat.sub p 256)) (hc_62_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_62_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_62_5 (Nat.sub p 160)) (hc_62_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_62_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_62_2 (Nat.sub p 64)) (hc_62_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_62_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)) (Nat.blt p 384)
def f_62 : Nat → Nat × Nat := unpackForestF 0x612957090b000c5fc122f6089170549b821450062de00db3006c18026d0062bdfc496f34977d95fbecaede691ef968779a45bdcaf5ec916f328f7a24dbcca280314ef148b75c59bbe28dd6956ec8a37625dbacaa802d7ee948b71b5eb9da95c68d6e46a57223db8c9a802d6edc4977015db7123db8916dd48b6e147b5a30db51a6d64db6bc69b5d32dac5b4016af6a245b29af59ed6ed126967b53b3da95948d6cc6a56623db289ad940e0016a764245afeb5d8b1a6c54ab5fc6eafdb15855aebf48b6024dafca2802d3ebd4ab5db6eaed1a802d2eb948b5bd62add2e802d1eb54ab53d6bacd2ad4f58ea78dd57c69abd2ad4edbaaaad755563aa9b5d54d8ea746b5423da9c9a802d0e9a8b74d459a6a2bd44d929a6974fb64a7c9ad34d0e9a2af4dc51a6da1d34554014bf4c254a222fd2c912888b749e70a4d3651115e9147d47b44a3d2251114e884bd44c5fa2da251314e894a5441250052dd0a91e8528f38461a0a3e5045167069f3fd709fdbe4e0d2e7dae1383479dab84ecdf2766d93b2349ddb84ec4d67068738c699c5a7ce4db2716873816d0052bcdc912628b7361379ad224c514e624dd3125e99a29ccc94a6224b31b4b98da1cc40a0014a71556b8aab1c551be5d8d31546e96abe4b49122a8d71546795e364ab5d255489154638aa314a11a2508c9281658a9b7c9c4d62a6d72547c92a384945f62a6cf22b6c915ae48ad524526b153638a9afc54d4e414891534f8fe2e454d2e3dce5153478edae47315239469153438deb44549be34ae11a46c8a933c5453e316e7151478adb7c56dae2b6cf1636c8adb1c545140149f1426487637c3b1ae254ad11d7088d3e43b19e2147d0fb4487d2243b18e1d4dc00a4b82eb14355a20b6df05b6b85eb8416d9e136d909b5c84d1a416d8e118d105a6f836b841b5820d8e105a6782c2800291e096a8edd6b81daa3b758e054c8edc6f76e35c035c2014f8edc677f89fbfc4ddfd488edc637edaa3b717df9688edc537da34bed165db4dcfa36376d2f3dd1bdee8d6f85707ba33bdd18ddb24aee45b7ad223b914ddc6beee35b79e303b8d5ddc6a6ee34f78d1a3b8d0ddc2b6ee15377cb73b84eddd2dcee13376c9200290dd96c8df56f759aa3ac555bead6ea37c6fab3ba2d51d12aadf56373e2cb7cdb9be6bce5d6972daf37c9bdc8ae2e436c6f933b8adf9c56d8df25f70dae37c95dbfad6dfd636fda937c4d40147ede2546ceb5b749f1b3acedc4596cd37366979b4ad6da2526cc928028edb08b0d8155676b5b5d1c19daced5d696adaf33b189a846ed41376762934d1819d4ced1c7268e3033a97da18a0cea5767ab5b3d1799d29a00a3766d323135bd994a8c4d6b65d3e31359d9528eca254626b1b23195918b2c4a6e63ab531d599894bcc556b62ab1b149498924a00a335be2db0c9156f8b2c1b6460d1aaded0d814bcb7a5b5bd2bafb1857d686b7a555ea342f51916f49ebc2645bd21ae95a5746c8ba35e5bd1fae15a5704c8b825e5bd1980257d6b496b5a475ad22a9b185688f8b4245535a7ac8df1646d8b2235535a1ac11656069eb034353536ab91f15c8e0ae27c53527ab2df1594f8a6a4355ab8aacdf14d47eaa27c5351daa51c14d46ea825453ab8a9c9f14d4660095752d22a6d189494ca9b36f51d1aa6cdad44ae0a227d4d9b3a82db14146a9b3634d937a6c9ad364ce9e26c4d931a6c8fd394d89b23b4d91ba6c8cc0129e9a2453eab12635a1314ca7d36f4bd1a9f4dad2c49e9624349eb825292d2948e93c7049d3e9f4d9d216d890b5c48c9b244d812146a7d36347eb41f49bd1cce08e26c3e935a28d3d198b88a34b451a3a2cd31158a88a34344eb81f499d104d88825c3e931a10dbd086d68436742db6210d8d084dc842623e92ea0adb1054d87d23f40936204970fa4768036b3fe301f48dcfc6d87e26c3e9199f41400128e7bb543dd2a9a95acf46a87a255352b19e3164f14aa6a36e3bd229a8d78ebad275b643adaf1a89bce84dc74244351359cb5c4e56f86a267386371c29b8e14886a263379bf1bcd50d44be6e26436a3f1b4910d44a66ad6b356b19ab178d58a46a2350049f9a3160d14aa5ad6b336b499ad78cd46a5ac623251d9928dcc946a5ac5231d2e16a9acc46be6235330e3816a99cc08e4604582d52f97c910bcae45e25c2d52996d5acb66bc5b3522d92f16c948b549a009372cd2a1255acae6ac573542b92b15c95092ac655d692ad321251bca98dc4946b299ab14c958a4ae25227c24a339411b8a06885024424a319395f89c8e44e25424a2f92f5f8978fc4bb4425d2212514c958b24926e24db19249780125e483580d6b590ed68876b043b5621d2d10e958874a84414421cab06b58c84ad2423680d6379051b8358d63fd711fdb806b19c7b8dc3db481ed2206b18c77afc3bc721ddac06b17c72afc3947e1c9a40e4910358a637c591bd2a86adb8356d61ab631aab48d4978356c4343630d5af0cc9d05fafe2fd7b18d460bf5dc614a82fd7317d3f06ad4c5d4882dc6316c9306ad48594fc1ab4b15d3f06ad0c54ad22a3520d5378a35c4516c01aa671363d89b1dc4d6c01aa5f1263f0931b8496c41aa4f11ab908d5883548e1b36f0d9b58851c0366ce1eb6c0f5ae07c9403d2681b3630d8b78755c0362ce1b13f0de3006c4dc352ac009270cc2a05717c3108815c5b0bc3605715c2d08815c530ac2f00216c2908812c5b09c2204b14c250bc008530042583d17c1e8a60fb4f07da183c090010860e05e0041d834178010660c0540422f82c110108b60a06c0422b824110108a60805e0041581c150068be0604401a2d8141b0068ae0404401a2980c178010460145f00a29804178010360003f 10 11
def ch_62 : Nat → Bool := dagCheckNodeV5 fullMask g_62 ep_62 5 31 bds_62 779 (dagTraceF fullMask rootStock 11 f_62) cur_62 nh_62
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 fullMask g_62 ep_62 5 31 779 bds_62 (dagTraceF fullMask rootStock 11 f_62) (cur_62 0) (nh_62 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_0 : treeBlockF 0 32 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_1 : treeBlockF 32 64 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_2 : treeBlockF 64 96 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_3 : treeBlockF 96 128 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_4 : treeBlockF 128 160 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_5 : treeBlockF 160 192 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_6 : treeBlockF 192 224 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_7 : treeBlockF 224 256 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_8 : treeBlockF 256 288 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_9 : treeBlockF 288 320 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_10 : treeBlockF 320 352 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_11 : treeBlockF 352 384 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_12 : treeBlockF 384 416 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_13 : treeBlockF 416 448 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_14 : treeBlockF 448 480 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_15 : treeBlockF 480 512 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_16 : treeBlockF 512 544 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_17 : treeBlockF 544 576 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_18 : treeBlockF 576 608 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_19 : treeBlockF 608 640 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_20 : treeBlockF 640 672 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_21 : treeBlockF 672 704 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_22 : treeBlockF 704 736 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_23 : treeBlockF 736 768 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_24 : treeBlockF 768 779 ch_62 = true := by decide +kernel
theorem nj_62_1 : ∀ i, 0 ≤ i → i < 64 → ch_62 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_62_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_62_1 h1 h2)
theorem nj_62_2 : ∀ i, 0 ≤ i → i < 96 → ch_62 i = true := block_join nj_62_1 (fun _ h1 h2 => treeBlockF_at nb_62_2 h1 h2)
theorem nj_62_3 : ∀ i, 0 ≤ i → i < 128 → ch_62 i = true := block_join nj_62_2 (fun _ h1 h2 => treeBlockF_at nb_62_3 h1 h2)
theorem nj_62_4 : ∀ i, 0 ≤ i → i < 160 → ch_62 i = true := block_join nj_62_3 (fun _ h1 h2 => treeBlockF_at nb_62_4 h1 h2)
theorem nj_62_5 : ∀ i, 0 ≤ i → i < 192 → ch_62 i = true := block_join nj_62_4 (fun _ h1 h2 => treeBlockF_at nb_62_5 h1 h2)
theorem nj_62_6 : ∀ i, 0 ≤ i → i < 224 → ch_62 i = true := block_join nj_62_5 (fun _ h1 h2 => treeBlockF_at nb_62_6 h1 h2)
theorem nj_62_7 : ∀ i, 0 ≤ i → i < 256 → ch_62 i = true := block_join nj_62_6 (fun _ h1 h2 => treeBlockF_at nb_62_7 h1 h2)
theorem nj_62_8 : ∀ i, 0 ≤ i → i < 288 → ch_62 i = true := block_join nj_62_7 (fun _ h1 h2 => treeBlockF_at nb_62_8 h1 h2)
theorem nj_62_9 : ∀ i, 0 ≤ i → i < 320 → ch_62 i = true := block_join nj_62_8 (fun _ h1 h2 => treeBlockF_at nb_62_9 h1 h2)
theorem nj_62_10 : ∀ i, 0 ≤ i → i < 352 → ch_62 i = true := block_join nj_62_9 (fun _ h1 h2 => treeBlockF_at nb_62_10 h1 h2)
theorem nj_62_11 : ∀ i, 0 ≤ i → i < 384 → ch_62 i = true := block_join nj_62_10 (fun _ h1 h2 => treeBlockF_at nb_62_11 h1 h2)
theorem nj_62_12 : ∀ i, 0 ≤ i → i < 416 → ch_62 i = true := block_join nj_62_11 (fun _ h1 h2 => treeBlockF_at nb_62_12 h1 h2)
theorem nj_62_13 : ∀ i, 0 ≤ i → i < 448 → ch_62 i = true := block_join nj_62_12 (fun _ h1 h2 => treeBlockF_at nb_62_13 h1 h2)
theorem nj_62_14 : ∀ i, 0 ≤ i → i < 480 → ch_62 i = true := block_join nj_62_13 (fun _ h1 h2 => treeBlockF_at nb_62_14 h1 h2)
theorem nj_62_15 : ∀ i, 0 ≤ i → i < 512 → ch_62 i = true := block_join nj_62_14 (fun _ h1 h2 => treeBlockF_at nb_62_15 h1 h2)
theorem nj_62_16 : ∀ i, 0 ≤ i → i < 544 → ch_62 i = true := block_join nj_62_15 (fun _ h1 h2 => treeBlockF_at nb_62_16 h1 h2)
theorem nj_62_17 : ∀ i, 0 ≤ i → i < 576 → ch_62 i = true := block_join nj_62_16 (fun _ h1 h2 => treeBlockF_at nb_62_17 h1 h2)
theorem nj_62_18 : ∀ i, 0 ≤ i → i < 608 → ch_62 i = true := block_join nj_62_17 (fun _ h1 h2 => treeBlockF_at nb_62_18 h1 h2)
theorem nj_62_19 : ∀ i, 0 ≤ i → i < 640 → ch_62 i = true := block_join nj_62_18 (fun _ h1 h2 => treeBlockF_at nb_62_19 h1 h2)
theorem nj_62_20 : ∀ i, 0 ≤ i → i < 672 → ch_62 i = true := block_join nj_62_19 (fun _ h1 h2 => treeBlockF_at nb_62_20 h1 h2)
theorem nj_62_21 : ∀ i, 0 ≤ i → i < 704 → ch_62 i = true := block_join nj_62_20 (fun _ h1 h2 => treeBlockF_at nb_62_21 h1 h2)
theorem nj_62_22 : ∀ i, 0 ≤ i → i < 736 → ch_62 i = true := block_join nj_62_21 (fun _ h1 h2 => treeBlockF_at nb_62_22 h1 h2)
theorem nj_62_23 : ∀ i, 0 ≤ i → i < 768 → ch_62 i = true := block_join nj_62_22 (fun _ h1 h2 => treeBlockF_at nb_62_23 h1 h2)
theorem nj_62_24 : ∀ i, 0 ≤ i → i < 779 → ch_62 i = true := block_join nj_62_23 (fun _ h1 h2 => treeBlockF_at nb_62_24 h1 h2)
theorem nc_62 : ∀ i, 0 ≤ i → i < 779 → ch_62 i = true := nj_62_24
theorem lb_62 : LowerBin fullMask rootStock g_62 12 :=
  lowerDagV5 (kn_cons lb_60 (kn_cons lb_55 (kn_cons lb_58 (kn_cons lb_59 (kn_cons lb_22 (kn_cons lb_56 (kn_cons lb_57 (kn_cons lb_28 (kn_cons lb_51 (kn_cons lb_31 (kn_cons lb_61 (kn_cons lb_53 (kn_cons lb_47 (kn_cons lb_37 (kn_cons lb_10 (kn_cons lb_23 (kn_cons lb_3 (kn_cons lb_50 (kn_cons lb_13 (kn_cons lb_36 (kn_cons lb_34 (kn_cons lb_14 (kn_cons lb_33 (kn_cons lb_49 (kn_cons lb_27 (kn_cons lb_29 (kn_cons lb_19 (kn_cons lb_38 (kn_cons lb_20 (kn_cons lb_54 (kn_nil))))))))))))))))))))))))))))))) rc_62 nc_62 (by decide +kernel)

def wg : List Gate := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.and, [3, 7]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.and, [9, 14]⟩, ⟨GateOp.and, [13, 15]⟩, ⟨GateOp.or, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 3972589568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676776 * 2 ^ 32 + 3972589568)) (13 - 1) := by
  rw [show canon fullMask (4276676776 * 2 ^ 32 + 3972589568) = g_62 by decide]
  exact lb_62

end PEqualNP.Outside.L_meta_47841

theorem PEqualNP.Outside.L_meta_47841 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 3972589568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 3972589568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_47841.table2_from_lowerBin (4276676776 * 2 ^ 32 + 3972589568) 13 PEqualNP.Outside.L_meta_47841.root_lb PEqualNP.Outside.L_meta_47841.wg 18 rfl PEqualNP.Outside.L_meta_47841.wfits PEqualNP.Outside.L_meta_47841.weval

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48721

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

def m_0 : Nat := 0xff000000000000
def s_0 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_0 : Nat := 0x17000000000000
def ep_0 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_1 : Nat := 0xff0000000000
def s_1 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_1 : Nat := 0x170000000000
def ep_1 : Nat := 0x6000000000000001200000000000000140000000000
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

def m_2 : Nat := 0xc000c000c000c0
def s_2 : List Nat := [0x40004000400040, 0xc0000000c0, 0xc000c0]
def g_2 : Nat := 0x40004000c0
def ep_2 : Nat := 0x40008000000040000000800000000000000000000000000000000000000000000000000000004000400000
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

def m_3 : Nat := 0xf0f0000
def s_3 : List Nat := [0x5050000, 0x3030000, 0xf0000]
def g_3 : Nat := 0x1070000
def ep_3 : Nat := 0x60000000000000000000000000000010200000000000001040000
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

def m_4 : Nat := 0x5500550000000000
def s_4 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_4 : Nat := 0x100150000000000
def ep_4 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
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

def m_5 : Nat := 0x3300330000000000
def s_5 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_5 : Nat := 0x100130000000000
def ep_5 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
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

def m_6 : Nat := 0xf000f0000000000
def s_6 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_6 : Nat := 0x100070000000000
def ep_6 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
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

def m_7 : Nat := 0x4444444400000000
def s_7 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_7 : Nat := 0x4044400000000
def ep_7 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_8 : Nat := 0x4040404040404040
def s_8 : List Nat := [0x40004000400040, 0x404000004040, 0x40404040]
def g_8 : Nat := 0x4000404040
def ep_8 : Nat := 0x40400000000040000040000000004000400000000000000000000000000000000000000000000000000000
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

def m_9 : Nat := 0x5050505000000000
def s_9 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_9 : Nat := 0x10105000000000
def ep_9 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
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

def m_10 : Nat := 0xc0c0c0c
def s_10 : List Nat := [0x4040404, 0xc000c, 0xc0c]
def g_10 : Nat := 0x4040c
def ep_10 : Nat := 0x4080000000000040008000000000000000000000000000000000000000000040400
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

def m_11 : Nat := 0x22222222
def s_11 : List Nat := [0x2020202, 0x220022, 0x2222]
def g_11 : Nat := 0x20222
def ep_11 : Nat := 0x2200000000000020020000000000002020000000000000000000000000000000000
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

def m_12 : Nat := 0xa0a0a0a
def s_12 : List Nat := [0x2020202, 0xa000a, 0xa0a]
def g_12 : Nat := 0x2020a
def ep_12 : Nat := 0x2080000000000020008000000000000000000000000000202000000000000000000
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

def m_13 : Nat := 0xc0c0c0c0
def s_13 : List Nat := [0x40404040, 0xc000c0, 0xc0c0]
def g_13 : Nat := 0x4040c0
def ep_13 : Nat := 0x40800000000000400080000000000000000000000000000000000000000000404000
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

def m_14 : Nat := 0xc0c00000c0c0
def s_14 : List Nat := [0x404000004040, 0xc0000000c0, 0xc0c0]
def g_14 : Nat := 0x40000040c0
def ep_14 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000
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

def m_15 : Nat := 0x5050000050500000
def s_15 : List Nat := [0x1010000010100000, 0x50000000500000, 0x50500000]
def g_15 : Nat := 0x10000010500000
def ep_15 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000000000000000000
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

def m_16 : Nat := 0xf000f00
def s_16 : List Nat := [0x5000500, 0x3000300, 0xf00]
def g_16 : Nat := 0x1000700
def ep_16 : Nat := 0x6000000000000000000000000000000000000000000010002000000000001000400
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

def m_17 : Nat := 0xf0f000000000000
def s_17 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_17 : Nat := 0x107000000000000
def ep_17 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_18 : Nat := 0x5555000000000000
def s_18 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_18 : Nat := 0x115000000000000
def ep_18 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
def cur_18 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_18 : Nat → Nat := fun _ => 0
def f_18 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_18 : Nat → Bool := dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 1 (dagTraceF m_18 s_18 3 f_18) cur_18 nh_18
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 1 bds_18 (dagTraceF m_18 s_18 3 f_18) (cur_18 0) (nh_18 0) s_18 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18 : treeBlockF 0 1 ch_18 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 1 → ch_18 i = true := fun _ h1 h2 => treeBlockF_at nb_18 h1 h2
theorem lb_18 : LowerBin m_18 s_18 g_18 4 :=
  lowerDagV5 (kn_nil) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0x3333000000000000
def s_19 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_19 : Nat := 0x113000000000000
def ep_19 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
def cur_19 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_19 : Nat → Nat := fun _ => 0
def f_19 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_19 : Nat → Bool := dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 1 (dagTraceF m_19 s_19 3 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 1 bds_19 (dagTraceF m_19 s_19 3 f_19) (cur_19 0) (nh_19 0) s_19 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19 : treeBlockF 0 1 ch_19 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 1 → ch_19 i = true := fun _ h1 h2 => treeBlockF_at nb_19 h1 h2
theorem lb_19 : LowerBin m_19 s_19 g_19 4 :=
  lowerDagV5 (kn_nil) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0x5000500050005000
def s_20 : List Nat := [0x1000100010001000, 0x500000005000, 0x50005000]
def g_20 : Nat := 0x100010005000
def ep_20 : Nat := 0x1000400000001000000040000000000000000000000000000000000000001000100000000000000000000000
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
def cur_20 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_20 : Nat → Nat := fun _ => 0
def f_20 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_20 : Nat → Bool := dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 1 (dagTraceF m_20 s_20 3 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 1 bds_20 (dagTraceF m_20 s_20 3 f_20) (cur_20 0) (nh_20 0) s_20 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20 : treeBlockF 0 1 ch_20 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 1 → ch_20 i = true := fun _ h1 h2 => treeBlockF_at nb_20 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 4 :=
  lowerDagV5 (kn_nil) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xff00ff0000000000
def s_21 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_21 : Nat := 0x100170000000000
def ep_21 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_1, s_1, 4, g_1), (m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5)]
def cc_21_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_21_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_21 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_21_1 (Nat.sub p 32)) (cc_21_0 p) (Nat.blt p 32)
def hc_21_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_21_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_21 : Nat → Nat := fun p => Bool.rec (hc_21_1 (Nat.sub p 32)) (hc_21_0 p) (Nat.blt p 32)
def f_21 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_21 : Nat → Bool := dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 43 (dagTraceF m_21 s_21 6 f_21) cur_21 nh_21
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 43 bds_21 (dagTraceF m_21 s_21 6 f_21) (cur_21 0) (nh_21 0) s_21 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_0 : treeBlockF 0 32 ch_21 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_1 : treeBlockF 32 43 ch_21 = true := by decide +kernel
theorem nj_21_1 : ∀ i, 0 ≤ i → i < 43 → ch_21 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_21_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_21_1 h1 h2)
theorem nc_21 : ∀ i, 0 ≤ i → i < 43 → ch_21 i = true := nj_21_1
theorem lb_21 : LowerBin m_21 s_21 g_21 7 :=
  lowerDagV5 (kn_cons lb_6 (kn_cons lb_1 (kn_cons lb_4 (kn_cons lb_5 (kn_nil))))) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xffff000000000000
def s_22 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_22 : Nat := 0x117000000000000
def ep_22 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17), (m_0, s_0, 4, g_0), (m_18, s_18, 4, g_18), (m_19, s_19, 4, g_19)]
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
  lowerDagV5 (kn_cons lb_17 (kn_cons lb_0 (kn_cons lb_18 (kn_cons lb_19 (kn_nil))))) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0xffff00000000
def s_23 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_23 : Nat := 0x175700000000
def ep_23 : Nat := 0x4000000000000006020000000000001202000000000000145400000000
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_23 : Nat → List (Nat × Nat) := fun _ => []
def nh_23 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 0 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) (nh_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 0 (dagTraceF m_23 s_23 4 f_23) cur_23 nh_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0xf0f0f0f000000000
def s_24 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_24 : Nat := 0x10105000000000
def ep_24 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000010105000000000
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def nh_24 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0x3333333300000000
def s_25 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_25 : Nat := 0x113131300000000
def ep_25 : Nat := 0x1200000000000012000000000000010202020000000000000000000000000110101000000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def nh_25 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) (nh_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 nh_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0x5050505050505050
def s_26 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_26 : Nat := 0x10105010505050
def ep_26 : Nat := 0x1040400000001040000040000010004000400000000000000000000000101000100000000000000000000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9), (m_15, s_15, 4, g_15), (m_20, s_20, 4, g_20), (m_8, s_8, 4, g_8)]
def cc_26_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_26_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_26 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_26_1 (Nat.sub p 32)) (cc_26_0 p) (Nat.blt p 32)
def hc_26_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_26_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_26 : Nat → Nat := fun p => Bool.rec (hc_26_1 (Nat.sub p 32)) (hc_26_0 p) (Nat.blt p 32)
def f_26 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_26 : Nat → Bool := dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 43 (dagTraceF m_26 s_26 6 f_26) cur_26 nh_26
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 43 bds_26 (dagTraceF m_26 s_26 6 f_26) (cur_26 0) (nh_26 0) s_26 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_0 : treeBlockF 0 32 ch_26 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_1 : treeBlockF 32 43 ch_26 = true := by decide +kernel
theorem nj_26_1 : ∀ i, 0 ≤ i → i < 43 → ch_26 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_26_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_26_1 h1 h2)
theorem nc_26 : ∀ i, 0 ≤ i → i < 43 → ch_26 i = true := nj_26_1
theorem lb_26 : LowerBin m_26 s_26 g_26 7 :=
  lowerDagV5 (kn_cons lb_9 (kn_cons lb_15 (kn_cons lb_20 (kn_cons lb_8 (kn_nil))))) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0x5555555500000000
def s_27 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_27 : Nat := 0x115155500000000
def ep_27 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_18, s_18, 4, g_18), (m_9, s_9, 4, g_9), (m_7, s_7, 4, g_7)]
def cc_27_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_27_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_27 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_27_1 (Nat.sub p 32)) (cc_27_0 p) (Nat.blt p 32)
def hc_27_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_27_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_27 : Nat → Nat := fun p => Bool.rec (hc_27_1 (Nat.sub p 32)) (hc_27_0 p) (Nat.blt p 32)
def f_27 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_27 : Nat → Bool := dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 43 (dagTraceF m_27 s_27 6 f_27) cur_27 nh_27
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 43 bds_27 (dagTraceF m_27 s_27 6 f_27) (cur_27 0) (nh_27 0) s_27 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_0 : treeBlockF 0 32 ch_27 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_1 : treeBlockF 32 43 ch_27 = true := by decide +kernel
theorem nj_27_1 : ∀ i, 0 ≤ i → i < 43 → ch_27 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_27_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_27_1 h1 h2)
theorem nc_27 : ∀ i, 0 ≤ i → i < 43 → ch_27 i = true := nj_27_1
theorem lb_27 : LowerBin m_27 s_27 g_27 7 :=
  lowerDagV5 (kn_cons lb_4 (kn_cons lb_18 (kn_cons lb_9 (kn_cons lb_7 (kn_nil))))) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0x666600006666
def s_28 : List Nat := [0x222200002222, 0x60600000606, 0x6600000066, 0x6666]
def g_28 : Nat := 0x64600004666
def ep_28 : Nat := 0x402000000000000000000000004000000020000006020000020000000000000000000000000000000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := []
def cur_28 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x1924309193c2050d3c205263d88d5d2a549902a109800f 7 127 3 7 10 1023 14 16383
def nh_28 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_28 : Nat → Nat × Nat := unpackForestF 0xc7a63529564f0a4c42a49e205084c00f 3 10
def ch_28 : Nat → Bool := dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 10 (dagTraceF m_28 s_28 4 f_28) cur_28 nh_28
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 10 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) (nh_28 0) s_28 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28 : treeBlockF 0 10 ch_28 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 10 → ch_28 i = true := fun _ h1 h2 => treeBlockF_at nb_28 h1 h2
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV5 (kn_nil) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0x66006600660066
def s_29 : List Nat := [0x22002200220022, 0x6000600060006, 0x6600000066, 0x660066]
def g_29 : Nat := 0x6004600460066
def ep_29 : Nat := 0x40002000000040000000200000000000000000000600020002000000000000000000000000000000000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := []
def cur_29 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x1924309193c2050d3c205263d88d5d2a549902a109800f 7 127 3 7 10 1023 14 16383
def nh_29 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_29 : Nat → Nat × Nat := unpackForestF 0xc7a63529564f0a4c42a49e205084c00f 3 10
def ch_29 : Nat → Bool := dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 10 (dagTraceF m_29 s_29 4 f_29) cur_29 nh_29
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 10 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) (nh_29 0) s_29 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29 : treeBlockF 0 10 ch_29 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 10 → ch_29 i = true := fun _ h1 h2 => treeBlockF_at nb_29 h1 h2
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV5 (kn_nil) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0x3030303030303030
def s_30 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_30 : Nat := 0x10101010101030
def ep_30 : Nat := 0x1000002000001000000000200010000000000020000000000000000000000000000000000010101010101000
def bds_30 : List (Nat × List Nat × Nat × Nat) := []
def cc_30_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_30_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_30 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_30_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_30_0 p) (Nat.blt p 32)
def hc_30_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_30_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_30_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_30 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_30_2 (Nat.sub p 64)) (hc_30_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_30_0 p) (Nat.blt p 32)
def f_30 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_30 : Nat → Bool := dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 64 (dagTraceF m_30 s_30 5 f_30) cur_30 nh_30
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 64 bds_30 (dagTraceF m_30 s_30 5 f_30) (cur_30 0) (nh_30 0) s_30 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_0 : treeBlockF 0 32 ch_30 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_1 : treeBlockF 32 64 ch_30 = true := by decide +kernel
theorem nj_30_1 : ∀ i, 0 ≤ i → i < 64 → ch_30 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_30_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_30_1 h1 h2)
theorem nc_30 : ∀ i, 0 ≤ i → i < 64 → ch_30 i = true := nj_30_1
theorem lb_30 : LowerBin m_30 s_30 g_30 6 :=
  lowerDagV5 (kn_nil) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0xc0c0c0c0c0c0c0c0
def s_31 : List Nat := [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0]
def g_31 : Nat := 0x40004040c0
def ep_31 : Nat := 0x40408000000040000040800000004000400080000000000000000000000000000000000000004000404000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14), (m_13, s_13, 4, g_13), (m_8, s_8, 4, g_8), (m_2, s_2, 4, g_2)]
def cc_31_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_31_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_31 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_31_1 (Nat.sub p 32)) (cc_31_0 p) (Nat.blt p 32)
def hc_31_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_31_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_31 : Nat → Nat := fun p => Bool.rec (hc_31_1 (Nat.sub p 32)) (hc_31_0 p) (Nat.blt p 32)
def f_31 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
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
  lowerDagV5 (kn_cons lb_14 (kn_cons lb_13 (kn_cons lb_8 (kn_cons lb_2 (kn_nil))))) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0x3333000033330000
def s_32 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_32 : Nat := 0x113000011130000
def ep_32 : Nat := 0x1000000000000000000000000012000000020000010200000002000000000000000000000110000011100000
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 4, g_19)]
def cur_32 : Nat → List (Nat × Nat) := fun _ => []
def nh_32 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 0 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) (nh_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 0 (dagTraceF m_32 s_32 4 f_32) cur_32 nh_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV5 (kn_cons lb_19 (kn_nil)) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0x5555000055550000
def s_33 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_33 : Nat := 0x115000011550000
def ep_33 : Nat := 0x1040000000000000000000000014000000440000010400000000000001100000110000000000000000000000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def nh_33 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) (nh_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 nh_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0x5500550055005500
def s_34 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_34 : Nat := 0x100150011005500
def ep_34 : Nat := 0x1000400000001400000044000000000000000000010004000000000001001000110000000000000000000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def nh_34 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) (nh_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 nh_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0xff000000ff00
def s_35 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_35 : Nat := 0x170000005700
def ep_35 : Nat := 0x400000000000000000000000000000000000000006000000020000001200000002000000140000005400
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def nh_35 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) (nh_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 nh_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0xf0f00000f0f0
def s_36 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_36 : Nat := 0x1050000050f0
def ep_36 : Nat := 0x40a0000000000000000000000040000000a0000000000000000000001000000000000000105000005000
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def nh_36 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) (nh_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 nh_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0x3300330033003300
def s_37 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_37 : Nat := 0x100130011001300
def ep_37 : Nat := 0x1000000000001200000002000000000000000000010002000000020000000000000000000100100011001000
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def nh_37 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) (nh_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 nh_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0xf000f000f000f000
def s_38 : List Nat := [0x5000500050005000, 0x3000300030003000, 0xf0000000f000, 0xf000f000]
def g_38 : Nat := 0x100010005000
def ep_38 : Nat := 0x1000400000001000000040000000000000000000000000000000000000001000100000000000100010005000
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 4, g_20)]
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def nh_38 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_cons lb_20 (kn_nil)) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0x33333333
def s_39 : List Nat := [0x11111111, 0x3030303, 0x330033, 0x3333]
def g_39 : Nat := 0x11131333
def ep_39 : Nat := 0x2200000000000020020000000000002020000000000000000000000000011101000
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def nh_39 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) (nh_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 nh_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xcc00cc00cc00cc
def s_40 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_40 : Nat := 0x40044004400cc
def ep_40 : Nat := 0x40008800000040000000880000000000000000000400000000000000000000000000000004004400440000
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def nh_40 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0xf0f0f0f0
def s_41 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_41 : Nat := 0x105050f0
def ep_41 : Nat := 0x40a000000000004000a0000000000000000000000000100000000000000010505000
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0xf0f0f0f
def s_42 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_42 : Nat := 0x107070f
def ep_42 : Nat := 0x6080000000000060008000000000000000000000000010202000000000001040400
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_16, s_16, 4, g_16), (m_10, s_10, 4, g_10), (m_12, s_12, 4, g_12)]
def cc_42_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_42_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_42 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_42_1 (Nat.sub p 32)) (cc_42_0 p) (Nat.blt p 32)
def hc_42_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_42_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_42 : Nat → Nat := fun p => Bool.rec (hc_42_1 (Nat.sub p 32)) (hc_42_0 p) (Nat.blt p 32)
def f_42 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_42 : Nat → Bool := dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 43 (dagTraceF m_42 s_42 6 f_42) cur_42 nh_42
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 43 bds_42 (dagTraceF m_42 s_42 6 f_42) (cur_42 0) (nh_42 0) s_42 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_0 : treeBlockF 0 32 ch_42 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_1 : treeBlockF 32 43 ch_42 = true := by decide +kernel
theorem nj_42_1 : ∀ i, 0 ≤ i → i < 43 → ch_42 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_42_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_42_1 h1 h2)
theorem nc_42 : ∀ i, 0 ≤ i → i < 43 → ch_42 i = true := nj_42_1
theorem lb_42 : LowerBin m_42 s_42 g_42 7 :=
  lowerDagV5 (kn_cons lb_3 (kn_cons lb_16 (kn_cons lb_10 (kn_cons lb_12 (kn_nil))))) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xaaaaaaaa
def s_43 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_43 : Nat := 0x202aa
def ep_43 : Nat := 0x2a800000000000200a8000000000002020000000000000202000000000000000000
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def nh_43 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) (nh_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 nh_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xff000000ff0000
def s_44 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_44 : Nat := 0x17000000570000
def ep_44 : Nat := 0x40000000000000000000000000000000000000000600000002000000120000000200000014000000540000
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def nh_44 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) (nh_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 nh_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0xf000f000f000f0
def s_45 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_45 : Nat := 0x100050005000f0
def ep_45 : Nat := 0x4000a000000040000000a00000000000000000000000000000000000100000000000000010005000500000
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def nh_45 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) (nh_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 nh_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xf0f00000f0f00000
def s_46 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_46 : Nat := 0x10000010500000
def ep_46 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000010000010500000
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def nh_46 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) (nh_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 nh_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0x5500aa005500aa
def s_47 : List Nat := [0xaa000000aa, 0x11002200110022, 0x5000a0005000a, 0x5500aa]
def g_47 : Nat := 0x150002005500aa
def ep_47 : Nat := 0x4000a800000000000000000000000000000000000400020000000000100002000000000000000000000000
def bds_47 : List (Nat × List Nat × Nat × Nat) := []
def cur_47 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x1a4471b4371343927d8d5ed5949d1540f 7 127 3 7 6 63 10 1023
def nh_47 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_47 : Nat → Nat × Nat := unpackForestF 0xfa7536ed0caf472174aa0f 3 6
def ch_47 : Nat → Bool := dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 10 (dagTraceF m_47 s_47 4 f_47) cur_47 nh_47
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 10 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) (nh_47 0) s_47 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47 : treeBlockF 0 10 ch_47 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 10 → ch_47 i = true := fun _ h1 h2 => treeBlockF_at nb_47 h1 h2
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV5 (kn_nil) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0x1111222211112222
def s_48 : List Nat := [0x222200002222, 0x101020201010202, 0x11002200110022, 0x11112222]
def g_48 : Nat := 0x111020211110222
def ep_48 : Nat := 0x1000002000000000000000000010000000000020010002020000020000000000000000000000000000000000
def bds_48 : List (Nat × List Nat × Nat × Nat) := []
def cur_48 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1d283091e3420d0d2420a263a88d993a54d903a10d800f 7 127 3 7 10 1023 14 16383
def nh_48 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_48 : Nat → Nat × Nat := unpackForestF 0xc74636f1a14e8a6c43a49220a086c00f 3 10
def ch_48 : Nat → Bool := dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 10 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 10 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48 : treeBlockF 0 10 ch_48 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 10 → ch_48 i = true := fun _ h1 h2 => treeBlockF_at nb_48 h1 h2
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_nil) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0x55550000aaaa
def s_49 : List Nat := [0xaaaa, 0x111100002222, 0x50500000a0a, 0x55000000aa]
def g_49 : Nat := 0x1555000002aa
def ep_49 : Nat := 0x40000000a8000004000000020000001000000002000000000000000000
def bds_49 : List (Nat × List Nat × Nat × Nat) := []
def cur_49 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0xd2440c34d0c309343924cf626af2d592906842c00f 7 127 3 7 9 511 13 8191
def nh_49 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_49 : Nat → Nat × Nat := unpackForestF 0x33d33532dd3432573472421a21600f 3 9
def ch_49 : Nat → Bool := dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 10 (dagTraceF m_49 s_49 4 f_49) cur_49 nh_49
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 10 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) (nh_49 0) s_49 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49 : treeBlockF 0 10 ch_49 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 10 → ch_49 i = true := fun _ h1 h2 => treeBlockF_at nb_49 h1 h2
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV5 (kn_nil) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0x55005500aa00aa
def s_50 : List Nat := [0xaa00aa, 0x11001100220022, 0x50005000a000a, 0x55000000aa]
def g_50 : Nat := 0x150055000200aa
def ep_50 : Nat := 0x40000000a80000000000000000000400000002000000100000000200000000000000000000
def bds_50 : List (Nat × List Nat × Nat × Nat) := []
def cur_50 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0xd2440c34d0c309343924cf626af2d592906842c00f 7 127 3 7 9 511 13 8191
def nh_50 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_50 : Nat → Nat × Nat := unpackForestF 0x33d33532dd3432573472421a21600f 3 9
def ch_50 : Nat → Bool := dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 10 (dagTraceF m_50 s_50 4 f_50) cur_50 nh_50
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 10 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) (nh_50 0) s_50 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50 : treeBlockF 0 10 ch_50 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 10 → ch_50 i = true := fun _ h1 h2 => treeBlockF_at nb_50 h1 h2
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV5 (kn_nil) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0x2222222222222222
def s_51 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_51 : Nat := 0x2020200020222
def ep_51 : Nat := 0x2000000200000002200002000000020020000202020002020000000000000000000000000000000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def nh_51 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 0 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) (nh_51 0) s_51 4 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 0 (dagTraceF m_51 s_51 4 f_51) cur_51 nh_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0xa0a0a0a0a0a0a0a
def s_52 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_52 : Nat := 0x202020002020a
def ep_52 : Nat := 0x800000200000002080002000000020008000000000000000000020202000202000000000000000000
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def nh_52 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 0 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) (nh_52 0) s_52 4 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 0 (dagTraceF m_52 s_52 4 f_52) cur_52 nh_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0x5a5a00005a5a
def s_53 : List Nat := [0xa0a00000a0a, 0x121200001212, 0x5a0000005a, 0x5a5a]
def g_53 : Nat := 0x12520000525a
def ep_53 : Nat := 0x400800000000000000000000004000000008000000000000000000001202000002000000000000000000
def bds_53 : List (Nat × List Nat × Nat × Nat) := []
def cur_53 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x193430d19282090d28209263a88d9d3a54d903a10d800f 7 127 3 7 10 1023 14 16383
def nh_53 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_53 : Nat → Nat × Nat := unpackForestF 0xc7463629d64a0a6c43a494209086c00f 3 10
def ch_53 : Nat → Bool := dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 10 (dagTraceF m_53 s_53 4 f_53) cur_53 nh_53
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 10 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) (nh_53 0) s_53 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53 : treeBlockF 0 10 ch_53 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 10 → ch_53 i = true := fun _ h1 h2 => treeBlockF_at nb_53 h1 h2
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV5 (kn_nil) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0x5a005a005a005a
def s_54 : List Nat := [0xa000a000a000a, 0x12001200120012, 0x5a0000005a, 0x5a005a]
def g_54 : Nat := 0x1200520052005a
def ep_54 : Nat := 0x40000800000040000000080000000000000000000000000000000000120002000200000000000000000000
def bds_54 : List (Nat × List Nat × Nat × Nat) := []
def cur_54 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x193430d19282090d28209263a88d9d3a54d903a10d800f 7 127 3 7 10 1023 14 16383
def nh_54 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_54 : Nat → Nat × Nat := unpackForestF 0xc7463629d64a0a6c43a494209086c00f 3 10
def ch_54 : Nat → Bool := dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 10 (dagTraceF m_54 s_54 4 f_54) cur_54 nh_54
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 10 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) (nh_54 0) s_54 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54 : treeBlockF 0 10 ch_54 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 10 → ch_54 i = true := fun _ h1 h2 => treeBlockF_at nb_54 h1 h2
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV5 (kn_nil) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0x55aa000055aa
def s_55 : List Nat := [0xaa000000aa, 0x112200001122, 0x50a0000050a, 0x55aa]
def g_55 : Nat := 0x1502000055aa
def ep_55 : Nat := 0x40a800000000000000000000000000000000000004020000000000001002000000000000000000000000
def bds_55 : List (Nat × List Nat × Nat × Nat) := []
def cur_55 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x1a4471b4371343927d8d5ed5949d1540f 7 127 3 7 6 63 10 1023
def nh_55 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_55 : Nat → Nat × Nat := unpackForestF 0xfa7536ed0caf472174aa0f 3 6
def ch_55 : Nat → Bool := dagCheckNodeV5 m_55 g_55 ep_55 1 1 bds_55 10 (dagTraceF m_55 s_55 4 f_55) cur_55 nh_55
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 1 1 10 bds_55 (dagTraceF m_55 s_55 4 f_55) (cur_55 0) (nh_55 0) s_55 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55 : treeBlockF 0 10 ch_55 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 10 → ch_55 i = true := fun _ h1 h2 => treeBlockF_at nb_55 h1 h2
theorem lb_55 : LowerBin m_55 s_55 g_55 5 :=
  lowerDagV5 (kn_nil) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0x5555555555555555
def s_56 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_56 : Nat := 0x115155511555555
def ep_56 : Nat := 0x1040400000001440000044000014004000440000010404000000000001101000110000000000000000000000
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_26, s_26, 7, g_26)]
def cur_56 : Nat → List (Nat × Nat) := fun _ => []
def nh_56 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_56 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 1 1 0 bds_56 (dagTraceF m_56 s_56 7 f_56) (cur_56 0) (nh_56 0) s_56 7 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_56 g_56 ep_56 1 1 bds_56 0 (dagTraceF m_56 s_56 7 f_56) cur_56 nh_56 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_56 : LowerBin m_56 s_56 g_56 8 :=
  lowerDagV5 (kn_cons lb_26 (kn_nil)) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0xff00ff00ff00ff00
def s_57 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_57 : Nat := 0x100170011005700
def ep_57 : Nat := 0x1000400000001600000046000000000000000000010006000000020001001200110002000100140011005400
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 7, g_21)]
def cur_57 : Nat → List (Nat × Nat) := fun _ => []
def nh_57 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_57 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 1 1 0 bds_57 (dagTraceF m_57 s_57 7 f_57) (cur_57 0) (nh_57 0) s_57 7 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_57 g_57 ep_57 1 1 bds_57 0 (dagTraceF m_57 s_57 7 f_57) cur_57 nh_57 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_57 : LowerBin m_57 s_57 g_57 8 :=
  lowerDagV5 (kn_cons lb_21 (kn_nil)) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0xf0f0f0f0f0f0f0f0
def s_58 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_58 : Nat := 0x101050105050f0
def ep_58 : Nat := 0x104040a000001040000040a000100040004000a0000000000000000000101000100000000010105010505000
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_24, s_24, 5, g_24), (m_31, s_31, 7, g_31), (m_45, s_45, 5, g_45), (m_41, s_41, 5, g_41), (m_26, s_26, 7, g_26), (m_9, s_9, 4, g_9), (m_38, s_38, 5, g_38), (m_36, s_36, 5, g_36), (m_46, s_46, 5, g_46), (m_30, s_30, 6, g_30)]
def cur_58 : Nat → List (Nat × Nat) := unpackCursorV5 0x13098486411188442030078bc1e0e1703443801 0x3120c8d1c2074d08102493d2fe4af527b48e82f90ae027608d41f406cc17104c01f 9 511 4 15 10 1023 14 16383
def nh_58 : Nat → Nat := unpackHintV5 0x17dd14b166c5253326ed1f129277987e36daf586d80b54714ce6e1dd450b7db63b50514b47831ba0000c600000 0x13aac78eaa739ce739ceaaaaf7bce739ce755a9fe9efa8e739d55f4f78de3c6f2739cd3aad5475539ce755a9feaa3d47a5555aa7c739ceab5579cef510e13aad47a8eaaab54ab51ce73aad3eaaa6739ceab0e2a2aa739cd3aad5475539ce7557b4ff9ce73aad53def7a7558e78e75539ce739d55efaa99ce739ce73aaaabf6af7bea39ce7557d3ef39dde378f1bc4eab1e3aa8ce318ce31aaaa80739ceaafa78c63b8e6318c60c3a211fa0a860c4eab551d54e739d56a800008f80000700e02020417026002755a8f51d5556a954039ce755a7555ea860c44a1d0103062755aa8eaa739ceab540000047c013aac73c73aa9ce73aabe9e1c0000008000e01c04404d8030b8130013aa9ce73aa9ce73aacef3b8ce318ce31aaaa8de3870c600c60c3a20c184cf8c60318d3aa9ce73aa9ce739ceab39ce60000004cf800700e020203c080180275539ce75518c6718c67555518c70e1bce739d56739cc018311060c18c63181313aa9ce73aa8c6318ceaa318c600000000cfa75539ce75539ce739d56779dc3800000001303807011013603c080180275539ce75539ce75539ce755 21 2097151 9 511
def f_58 : Nat → Nat × Nat := unpackForestF 0x14bc52b149f234148c42f10ac42774d0423107c41b105c924104c01f 4 10
def ch_58 : Nat → Bool := dagCheckNodeV5 m_58 g_58 ep_58 3 7 bds_58 16 (dagTraceF m_58 s_58 8 f_58) cur_58 nh_58
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 3 7 16 bds_58 (dagTraceF m_58 s_58 8 f_58) (cur_58 0) (nh_58 0) s_58 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58 : treeBlockF 0 16 ch_58 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 16 → ch_58 i = true := fun _ h1 h2 => treeBlockF_at nb_58 h1 h2
theorem lb_58 : LowerBin m_58 s_58 g_58 9 :=
  lowerDagV5 (kn_cons lb_24 (kn_cons lb_31 (kn_cons lb_45 (kn_cons lb_41 (kn_cons lb_26 (kn_cons lb_9 (kn_cons lb_38 (kn_cons lb_36 (kn_cons lb_46 (kn_cons lb_30 (kn_nil))))))))))) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0x3333333333333333
def s_59 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_59 : Nat := 0x113131311131333
def ep_59 : Nat := 0x1000002000001200000002200012000000020020010202020002020000000000000000000110101011101000
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_30, s_30, 6, g_30), (m_37, s_37, 5, g_37), (m_25, s_25, 5, g_25), (m_32, s_32, 5, g_32), (m_39, s_39, 5, g_39), (m_51, s_51, 5, g_51), (m_48, s_48, 5, g_48), (m_5, s_5, 4, g_5), (m_11, s_11, 4, g_11)]
def cur_59 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x215d3495a5d249935a3958956791d547149c01f 6 63 2 3 10 1023 14 16383
def nh_59 : Nat → Nat := unpackHintV5 0xdf00ac66ac00707870006791620b3658006c0000 0x140016ad5d80de36e73c79d02718c0017ab1ac631ec06f39e3be80671ec73b65bd60080d182a3540f1e9a005a802c6300469e3c000c7471e 16 65535 7 127
def f_59 : Nat → Nat × Nat := unpackForestF 0x215d191da5d151cb5a2958956149c01f 4 10
def ch_59 : Nat → Bool := dagCheckNodeV5 m_59 g_59 ep_59 3 7 bds_59 9 (dagTraceF m_59 s_59 7 f_59) cur_59 nh_59
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 3 7 9 bds_59 (dagTraceF m_59 s_59 7 f_59) (cur_59 0) (nh_59 0) s_59 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59 : treeBlockF 0 9 ch_59 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 9 → ch_59 i = true := fun _ h1 h2 => treeBlockF_at nb_59 h1 h2
theorem lb_59 : LowerBin m_59 s_59 g_59 8 :=
  lowerDagV5 (kn_cons lb_30 (kn_cons lb_37 (kn_cons lb_25 (kn_cons lb_32 (kn_cons lb_39 (kn_cons lb_51 (kn_cons lb_48 (kn_cons lb_5 (kn_cons lb_11 (kn_nil)))))))))) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0xcccccccccccccccc
def s_60 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_60 : Nat := 0x40444004444cc
def ep_60 : Nat := 0x40408800000440000044880004004000440088000404000000000000000000000000000004044400444400
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_31, s_31, 7, g_31)]
def cur_60 : Nat → List (Nat × Nat) := fun _ => []
def nh_60 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_60 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 1 1 0 bds_60 (dagTraceF m_60 s_60 7 f_60) (cur_60 0) (nh_60 0) s_60 7 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_60 g_60 ep_60 1 1 bds_60 0 (dagTraceF m_60 s_60 7 f_60) cur_60 nh_60 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_60 : LowerBin m_60 s_60 g_60 8 :=
  lowerDagV5 (kn_cons lb_31 (kn_nil)) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0xff00ff00ff00ff
def s_61 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_61 : Nat := 0x170057005700ff
def ep_61 : Nat := 0x4000a800000040000000a80000000000000000000600020002000000120002000200000014005400540000
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_2, s_2, 4, g_2), (m_50, s_50, 5, g_50), (m_47, s_47, 5, g_47), (m_54, s_54, 5, g_54), (m_29, s_29, 5, g_29)]
def cc_61_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb42b2ac2b099660946509060480200801b56c1b06c1b06499064145501405014048920480d507001 0xfa443c0910b5e40d68eb5238958d95632970bb5c20d34c34510934b24528d749a5d2457050360409872341a4d0845e1f168645216d5850560c910292410d783b5a08d481a560415a034f78d1dba4f6691d714f5451d11373449ca84f2211c48370209c001f 10 1023 4 15 11 2047 18 262143
def cc_61_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x88441dae870b81b2bc5c2e1709548225108132180c0601e8e070381c0a85028028000000 0x3f4b9f15d909afa174b06bd84ce4a642537a28a404de022ecd7352bae125d02e8609724b9835ca5a6e2d16149b7a45b5aed8976326cd926ac2e4e8d260694c5ea22d4b14a46ad1956 9 511 3 7 11 2047 17 131071
def cc_61_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xc29a21100 0x884c854c534d8745204d8245 6 63 3 7 9 511 16 65535
def cur_61 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_61_2 (Nat.sub p 64)) (cc_61_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_61_0 p) (Nat.blt p 32)
def hc_61_0 : Nat → Nat := unpackHintV5 0xed09ca437c66c8cbb797602e815d00b90546b28c05180a3010cea180430084090411e883a0c6e18a2e944028804f089a111481f8c391838e801c0000 0x3fd3d13fdff0d555005103c000141540003e20019660000880f00fff13d3df7fc905550001103c43ffd0f53fdff2555400001440f055550410041000 15 32767 6 63
def hc_61_1 : Nat → Nat := unpackHintV5 0xd000d000af42af00ae02ae00ad029530950095009500744274007302730072025a305a005a005a00384438003800360434042c10260c200c023c020002000004 0x5b6d5fb555550c484155557dd754015d5555d757d4312150550f30c000004d4d30c0f0300000fff1f43df7fc341554440f10000f 16 65535 7 127
def hc_61_2 : Nat → Nat := unpackHintV5 0xd00c82c80c02030000 0x55fb6d555500 12 4095 6 63
def nh_61 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_61_2 (Nat.sub p 64)) (hc_61_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_61_0 p) (Nat.blt p 32)
def f_61 : Nat → Nat × Nat := unpackForestF 0x2204c82516114c821140b4f7a971e95d7a1740b4776131c14572531c0450293da35c68575a05d0291d925c5ed15835c5e914094f56d755a5d561700947471791c5a4c8d13034471491b5646558093736d78db5a3c910f02436d48da5636558092732970b3452ed70b2450213c935d24974915c0211c545e151686a341a4d0545214d585056020dc135e04d682a440a49013520495810560209c001f 7 11
def ch_61 : Nat → Bool := dagCheckNodeV5 m_61 g_61 ep_61 2 3 bds_61 69 (dagTraceF m_61 s_61 7 f_61) cur_61 nh_61
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 2 3 69 bds_61 (dagTraceF m_61 s_61 7 f_61) (cur_61 0) (nh_61 0) s_61 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_0 : treeBlockF 0 32 ch_61 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_1 : treeBlockF 32 64 ch_61 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_2 : treeBlockF 64 69 ch_61 = true := by decide +kernel
theorem nj_61_1 : ∀ i, 0 ≤ i → i < 64 → ch_61 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_61_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_61_1 h1 h2)
theorem nj_61_2 : ∀ i, 0 ≤ i → i < 69 → ch_61 i = true := block_join nj_61_1 (fun _ h1 h2 => treeBlockF_at nb_61_2 h1 h2)
theorem nc_61 : ∀ i, 0 ≤ i → i < 69 → ch_61 i = true := nj_61_2
theorem lb_61 : LowerBin m_61 s_61 g_61 8 :=
  lowerDagV5 (kn_cons lb_0 (kn_cons lb_2 (kn_cons lb_50 (kn_cons lb_47 (kn_cons lb_54 (kn_cons lb_29 (kn_nil))))))) rc_61 nc_61 (by decide +kernel)

def m_62 : Nat := 0xf0f0f0f0f0f0f0f
def s_62 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_62 : Nat := 0x10707070107070f
def ep_62 : Nat := 0x800000600000006080006000000060008000000000000000001020202010202000104040401040400
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_42, s_42, 7, g_42)]
def cur_62 : Nat → List (Nat × Nat) := fun _ => []
def nh_62 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_62 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 m_62 g_62 ep_62 1 1 0 bds_62 (dagTraceF m_62 s_62 7 f_62) (cur_62 0) (nh_62 0) s_62 7 = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_62 g_62 ep_62 1 1 bds_62 0 (dagTraceF m_62 s_62 7 f_62) cur_62 nh_62 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_62 : LowerBin m_62 s_62 g_62 8 :=
  lowerDagV5 (kn_cons lb_42 (kn_nil)) rc_62 nc_62 (by decide +kernel)

def m_63 : Nat := 0xffff0000ffff0000
def s_63 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_63 : Nat := 0x117000011570000
def ep_63 : Nat := 0x1040000000000000000000000016000000460000010600000002000001120000110200000114000011540000
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 7, g_22)]
def cur_63 : Nat → List (Nat × Nat) := fun _ => []
def nh_63 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_63 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV5 m_63 g_63 ep_63 1 1 0 bds_63 (dagTraceF m_63 s_63 7 f_63) (cur_63 0) (nh_63 0) s_63 7 = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_63 g_63 ep_63 1 1 bds_63 0 (dagTraceF m_63 s_63 7 f_63) cur_63 nh_63 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_63 : LowerBin m_63 s_63 g_63 8 :=
  lowerDagV5 (kn_cons lb_22 (kn_nil)) rc_63 nc_63 (by decide +kernel)

def m_64 : Nat := 0xffff0000ffff
def s_64 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_64 : Nat := 0x1757000057ff
def ep_64 : Nat := 0x40a8000000000000000000000040000000a8000006020000020000001202000002000000145400005400
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_14, s_14, 4, g_14), (m_49, s_49, 5, g_49), (m_53, s_53, 5, g_53), (m_28, s_28, 5, g_28), (m_55, s_55, 5, g_55)]
def cc_64_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb42b2ac2b099660946509060480200801b56c1b06c1b06499064145501405014048920480d507001 0xfa443c0910b5e40d68eb5238958d95632970bb5c20d34c34510934b24528d749a5d2457050360409872341a4d0845e1f168645216d5850560c910292410d783b5a08d481a560415a034f78d1dba4f6691d714f5451d11373449ca84f2211c48370209c001f 10 1023 4 15 11 2047 18 262143
def cc_64_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x88441dae870b81b2bc5c2e1709548225108132180c0601e8e070381c0a85028028000000 0x3f4b9f15d909afa174b06bd84ce4a642537a28a404de022ecd7352bae125d02e8609724b9835ca5a6e2d16149b7a45b5aed8976326cd926ac2e4e8d260694c5ea22d4b14a46ad1956 9 511 3 7 11 2047 17 131071
def cc_64_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xc29a21100 0x884c854c534d8745204d8245 6 63 3 7 9 511 16 65535
def cur_64 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_64_2 (Nat.sub p 64)) (cc_64_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_64_0 p) (Nat.blt p 32)
def hc_64_0 : Nat → Nat := unpackHintV5 0xed09ca437c66c8cbb797602e815d00b90546b28c05180a3010cea180430084090411e883a0c6e18a2e944028804f089a111481f8c391838e801c0000 0x3fd3d13fdff0d555005103c000141540003e20019660000880f00fff13d3df7fc905550001103c43ffd0f53fdff2555400001440f055550410041000 15 32767 6 63
def hc_64_1 : Nat → Nat := unpackHintV5 0xd000d000af42af00ae02ae00ad029530950095009500744274007302730072025a305a005a005a00384438003800360434042c10260c200c023c020002000004 0x575d5f7555551c484155557cd354014d5554d357d4312150550fb2c000005d4db2c0f0b00000fff1f43df7fc741554440f10000f 16 65535 7 127
def hc_64_2 : Nat → Nat := unpackHintV5 0xd00c82c80c02030000 0x55f75d555500 12 4095 6 63
def nh_64 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_64_2 (Nat.sub p 64)) (hc_64_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_64_0 p) (Nat.blt p 32)
def f_64 : Nat → Nat × Nat := unpackForestF 0x2204c82516114c821140b4f7a971e95d7a1740b4776131c14572531c0450293da35c68575a05d0291d925c5ed15835c5e914094f56d755a5d561700947471791c5a4c8d13034471491b5646558093736d78db5a3c910f02436d48da5636558092732970b3452ed70b2450213c935d24974915c0211c545e151686a341a4d0545214d585056020dc135e04d682a440a49013520495810560209c001f 7 11
def ch_64 : Nat → Bool := dagCheckNodeV5 m_64 g_64 ep_64 2 3 bds_64 69 (dagTraceF m_64 s_64 7 f_64) cur_64 nh_64
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV5 m_64 g_64 ep_64 2 3 69 bds_64 (dagTraceF m_64 s_64 7 f_64) (cur_64 0) (nh_64 0) s_64 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_0 : treeBlockF 0 32 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_1 : treeBlockF 32 64 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_2 : treeBlockF 64 69 ch_64 = true := by decide +kernel
theorem nj_64_1 : ∀ i, 0 ≤ i → i < 64 → ch_64 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_64_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_64_1 h1 h2)
theorem nj_64_2 : ∀ i, 0 ≤ i → i < 69 → ch_64 i = true := block_join nj_64_1 (fun _ h1 h2 => treeBlockF_at nb_64_2 h1 h2)
theorem nc_64 : ∀ i, 0 ≤ i → i < 69 → ch_64 i = true := nj_64_2
theorem lb_64 : LowerBin m_64 s_64 g_64 8 :=
  lowerDagV5 (kn_cons lb_1 (kn_cons lb_14 (kn_cons lb_49 (kn_cons lb_53 (kn_cons lb_28 (kn_cons lb_55 (kn_nil))))))) rc_64 nc_64 (by decide +kernel)

def g_65 : Nat := 0x1171757115757ff
def ep_65 : Nat := 0x104040a800001640000046a800160040004600a8010606020002020001121202110202000114145411545400
def bds_65 : List (Nat × List Nat × Nat × Nat) := [(m_63, s_63, 8, g_63), (m_61, s_61, 8, g_61), (m_27, s_27, 7, g_27), (m_59, s_59, 8, g_59), (m_64, s_64, 8, g_64), (m_62, s_62, 8, g_62), (m_58, s_58, 9, g_58), (m_57, s_57, 8, g_57), (m_60, s_60, 8, g_60), (m_21, s_21, 7, g_21), (m_42, s_42, 7, g_42), (m_43, s_43, 5, g_43), (m_31, s_31, 7, g_31), (m_26, s_26, 7, g_26), (m_22, s_22, 7, g_22), (m_51, s_51, 5, g_51), (m_52, s_52, 5, g_52), (m_7, s_7, 4, g_7), (m_34, s_34, 5, g_34), (m_39, s_39, 5, g_39), (m_33, s_33, 5, g_33), (m_11, s_11, 4, g_11), (m_37, s_37, 5, g_37), (m_30, s_30, 6, g_30), (m_40, s_40, 5, g_40), (m_53, s_53, 5, g_53), (m_35, s_35, 5, g_35), (m_24, s_24, 5, g_24), (m_50, s_50, 5, g_50), (m_44, s_44, 5, g_44), (m_54, s_54, 5, g_54), (m_9, s_9, 4, g_9), (m_46, s_46, 5, g_46), (m_38, s_38, 5, g_38)]
def cc_65_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9804c0260130098047163811818c0450628110188043061810428204006000fc17233901c80e407203901c80d0568033040e4001 0xf56f0ed630e16f0d95f0d1570c1460b1640a154091640617e081540716c0624f0ad6f09d6308b6f07b5f06b570596e0456f03d630336f02b5f0235701146d345fd2c5bd1c57d1453d0b5fcf357ce34fcdb47cb25fcaa5bc9257c6a53c5a4fc324bbea47bda43bba3bb8a37af15fa995ba2157981539294f8994b7d147779437193b6a9376112f5792b4c9273a9233785f3705b308572f8532b04f2a04b23047228432203b168371002f0f82b0c8270b8230501f0481b01817008130003f 13 8191 6 63 11 2047 20 1048575
def cc_65_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x84e10806007c5f0785e0745d0705c0701a2681735c0da340c1300b1284a024490240721c06101800 0x828ddf9376249dec6877181cc686f181ad7866d299348699fd8d7260d42156f7d189e26f7495dc16f6c55d79275c168c02204049626454951294f4e9912a7e48951126c575bd4d63509b9316f4657d0957 10 1023 4 15 11 2047 18 262143
def cc_65_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xf1f0e9e8e1e0e0d2b4b0a29998917b7871706968685a584a2c28282112090801 0x2c927bb192dc64b35fac358bd1bae26fb45beb9275c51aa844a45169245a691e89479249e7d689b5a25b5a94d624e7290d8285629c9be616f8e49da927871a1a127804d60235 8 255 3 7 11 2047 18 262143
def cc_65_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xa4290a065394241901c87012a4812048120480d5340d0304c02c4b0284a024490240721841504001 0x3ea4b7f8d8fd181f1303d46e878bf0d16e0e2bc0c53806bef6d5de5a7bc34797adf2b5ae4ab3c85638f8df1719e262fc445777468ec5b9d127b9a477229ee251dc093b6c7c6bae0d31f19eb832a5b644a6c6dc1b127b52476829ecc51d8893b0044 10 1023 4 15 11 2047 19 524287
def cc_65_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xacaa1a82a0a099f641725c1525054044d01388d1304b12c074184420c4300c0300c0120400100000 0x4fd7e79240f048272b4cdd61adadf575aea2b3d3563a58df4119e7a2fcec579a6c4ee481c037b1067570be8e15cbc23c3a34982c90c8d258aa42a34948f9068d24cbe411248146922552011a3fa347e4691d5f236b83da348c2f8f48d22abf3ca34784690adb2113041144 10 1023 4 15 11 2047 19 524287
def cc_65_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xa4690a42729c26198260982608ce30886208819964163581334851138ce02cca1244811c45205001 0x2fcaa5ec7cbc2f974552debe5b570b52f9675fb02b7df56bbbacf7358ee237da467b28bf6315ec0b757368872406811e71b856358862410a48210985547ca96e1064826db853b588124100481fc903f1207d2814496df0985257ca3ae142dc1ec903d120 10 1023 4 15 11 2047 19 524287
def cc_65_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xe974383c0d8ec343a0c8cda6121904462110793c1c2e070381c0b35828540a00c8400200 0x1c08ef7d1beec68db4b9b29735e3070d6fde8c5b89bf6931ec25bd64afa8993492a6847ccf4f99a9532abe64d70c84f98d5fb4eb7e8d6bceacf9958f2e37e3c67c58bf8915f0d3760964 9 511 4 15 11 2047 19 524287
def cc_65_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x98251942415b96054550505405012248111440c5300b12c0a12809124081200711c0160400100000 0x7f26c7e4608856287b6f85b6784a6f82a6b812677fa637ea3b7da373886f330671b0371082f0d0277c9647b9347a97c7a07c791347c36f7b36b79b6778b637816e771647616475134741347316c76d6f75b6f74b6373b5b72b577216e71468 10 1023 4 15 11 2047 20 1048575
def cc_65_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xe8f43a1b2d86874191c860700f9783c168b0582c12481401c4e061301088040110804002 0x8f9348e97c8e07c8d1348c1348b15c9246f914679036f8f36b8db678cb638bb4b8ab478a16e83a6980a618924b88a478724f86a4386570855688425683e708326c825708187c80e708026c 9 511 4 15 11 2047 20 1048575
def cc_65_9 : Nat → List (Nat × Nat) := unpackCursorV5 0x8c2308862084610841f27c1e1781d1741c143100400f13c0e1380e0308c02c429080200441000400 0x9e9549d9349ce709c16c9b1349a1349915ca1d6fa1563a0c5fa04579fb6f9f3639e35f9d35b9bb579ab5399b4b98b4797464962549547c9487c93a5497c6e96a6f95a6b94267932633906f340671182f0d8279197c90964 10 1023 4 15 11 2047 20 1048575
def cc_65_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x722e01b0b60682d0190b205c4b8160a44480809001c2380608c0142280500a01401883000300000000000000 0xb846fb7c63b734fb6b47b626fb5a63b4a4fb3a4bb2a47b1a43b0a3bafa372d04f260471c0371302f0e027ae954ad934ac956ac670ab96caa934ae35fad35bab357aa353a947ca507ca827ca487ca7570a407ca627ca387ca513fa493ba4137a3933a8a4fa7a4ba6a47a5a43a306ca2860 11 2047 5 31 11 2047 20 1048575
def cc_65_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xa45be6c16558151540f63c0e1380e0308661806018060180601805114041100310c0210801104001 0xbfd70c1d62c136fbf367b296fab16ba69679b9637293b6b1373986f350671d0370681f02017be26eb196faa16ba59679a963bd264bcd6fbc26eb096f999638b95b7e957bb468ba13bb9937bad6fb9462af96f989638a95b7d957b5464b4264b3568b2264b1264b0468 10 1023 4 15 11 2047 20 1048575
def cc_65_12 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2aaa49898888808808808806715e45645604a64a04a04a04a032c3202092002001e11e00c90c00c0044040040040002 0xd046ccfc60c424bbf2479114b859476392f5a12b50127459236312f5992b4f92745123cec6ecc26fc7a63b716fa09636292f5912b4f12744923cba6fc7263b696fa01636212f5892b4e92744123cd46fccc63cc34fcbb47b616f9f9639694f9014b849477c1437593b6e1372e04f270471e0370881f030179595f8f15b829577b1539483f8e03b818377a0339414f8d94b8114779943ca06cc9860c8d6fc8563c7c5fc7457b596f9f1639315f8c95b7f957789537494b6d147c646eb496fae16ba89679e1633a06f360670781f02817c4a7cc546fc4467c3a6eb396fad16ba79679d1637394b6c147ac1699c961c294bc2147c094fc0143 12 4095 5 31 11 2047 20 1048575
def cc_65_13 : Nat → List (Nat × Nat) := unpackCursorV5 0xa632921238541842042004 0x33537e4663bcc77758dee0b7d0d6376a76e14dda697b012b56a4e9748c841b8ac2f0f04e1507c100bb452f5f256ab49d2a91b412f5ea56aa49d2891e936c6725ebb4ad5093a4923cccdf9098edeb7d09636625eb94ad4c93a41231485e1d09c260f81c17c54978291e48a5c3d4765a5eb84ad4a93a3d236525eb74ad4893a392364a5eb64ad4693a3523 11 2047 5 31 10 1023 19 524287
def cur_65 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_65_13 (Nat.sub p 416)) (cc_65_12 (Nat.sub p 384)) (Nat.blt p 416)) (Bool.rec (cc_65_11 (Nat.sub p 352)) (cc_65_10 (Nat.sub p 320)) (Nat.blt p 352)) (Nat.blt p 384)) (Bool.rec (Bool.rec (cc_65_9 (Nat.sub p 288)) (cc_65_8 (Nat.sub p 256)) (Nat.blt p 288)) (cc_65_7 (Nat.sub p 224)) (Nat.blt p 256)) (Nat.blt p 320)) (Bool.rec (Bool.rec (Bool.rec (cc_65_6 (Nat.sub p 192)) (cc_65_5 (Nat.sub p 160)) (Nat.blt p 192)) (Bool.rec (cc_65_4 (Nat.sub p 128)) (cc_65_3 (Nat.sub p 96)) (Nat.blt p 128)) (Nat.blt p 160)) (Bool.rec (Bool.rec (cc_65_2 (Nat.sub p 64)) (cc_65_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_65_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 224)
def hc_65_0 : Nat → Nat := unpackHintV5 0xcd0e11c43a35bc7defb32656aa2a3fa505499f556c9a194f947d678c221786756b7dd22978ad4972359e6c018d64add55ead8056d5f65388d34da579482d5e43094937bad42bc6fd2409ef1aee4712063a0ad9cb05c94401192c000046000000 0xa0757fa81d5540c1831e0c583060c183060c7ab2b2aa0d36aa8341aa0d506a8b547aaaaaaaaaaab540c18301870603060c18f3e7c7a1d15156aaaaaaaaa96555bfd540eaaff40eaaa2e0c7831e3cb8b1e3cb8b1e3d5959506a97554ba6d552e97545aa3d555552e935555556a8b83065cb872e170e5c1e7cf8f43a2a2ad55555545e3f554b2aadfea80aa0e0c3970e0c387aa0e1c38f0e2c3873e3cf8f56565543a6d550e87541aa5d516a8f5555555555548ff415070381c0e21c14112aaaaaaaaa96555bf9403a2e1d1d5070e01fa1e5c1831e1c3871e1c5870eaca9b541aa5d550e9b5543a1d516a8f555555555554390033f830600c1830e0710e0a089545e07070f07a0e1cd9fa1f1b949aaadfc8380c1d503460e81807e8783160c183060c783060c1ab2a6d5506835541a6d506a83545aa3d555555555550e403061c1830019fc381c438282255033740c1d0381c3e37293555bf90728fd0f3e3cf8f5654daa0d52ea8b547aaaaaaab4bd7af1e7cf8f43a2a2ad51b8dc3e37293555bf9b8dd555542c58b175542c58b162c7d4cc9349a8b5168b45d5275ebd38b162c58b162c593527555540e85d0baa89d15155547c79f1ecc9349a4d1f54bd7af5e3cf9f1e4d49d55555554ab7faaaaaa8bd40ea1f50ba89d15078568000a80282a8f8b1e3cf8b1e3c183060ea91a6c9a34d93060c1831e6cf8f000000000000aaaaaaaaaaa3f5500503abfd40eaaa060c18f062c183060c183063ea81a0c9834183060c1831e6cf8f00000000000020200180c00060000c00600f005804c0400aaaaaaaaaaa3f5505fc002a8a000a000aa2e0c18f3e2c78f3e2c78faa2e0c197469b268d364c79b3e3c000000000002aaaaaaaaaa8fd5400103aabfd03aaa8b831e0c78f2e2c78f2e2c78faa2e0c1972e97265d2e4c79b3e3c00000002e070000020200b800c02e17000b8000f005804c0400aaaaaaaaaaa3f5505fc002a000aa460d197460d197aa3e2c78f3e2c78f3e3cf8f1500505555000000000000aaa55a5aaaa3f2a803354a9741ad52a3d16a7c79f1ecff55555554000000000000808044004000b800c01e00b0109808801554accb55547e550bf80040e8bcb47552d193260007e8797060c79f163c79f163c7aa883540141540000000000023f51b2f0395438751f1b367e550000745d46aca934fd0f2e0c18f547a2d55506ff5555540000000000000200b800c0440040007802c0404008fd46cbc0e564da8f8d9b3f2a85fc0003c347550d183a060c18001fa1e7c58f1e7c58f1e0c18306aaa000a2aa0000000000011fa8d870eaaa0e070f8d9b3f2a802b2a8c1d035067e87a2d551e0c18306aaaaaa0dfeaa000000000000330201000440006003007802c04260220047ea36a6cfaaad0381c3e366cfcaa17f0000e00cb832f328d46ab363aa4d163c58f478b5541bfd5400002aa9a40aa460d997660d197aa3e2c78f3e2c78f3e3cf8faa469b271d364cdb3363cd9f1e000000000000155555555555540147e879f1e7c7d1b366c79b3e3c000000000200b800c01e00b009808011fa979f8fc3e3e7cfc6e3705fc0003d5551f1e7c7d51b366cd8f366c7c4070381c0e070395555555417fa0aaaa8bd40ea1f50ba89ccd41e0281d5fea0755503060c783160c183060c1831f540d064c1a0c183060c18f367c7d55503060c183061d783061c383060c183060c183060c1870e1c5870e1c7870e1d0e8727100c18030e00c06070381c0e5555555555555400505fe07557fa0755517063c18f1e5c58f1e5c58f1f545c1832e5d2e4cba5c98f367c7d555070e0c183061cb870e1c3872e1d7870e1c3872e1cb870e1c5870e1c7870e1d0e8727101c06070e1700e1c38700e070381caaaaaaaaa2f1faaaaa00282fecd52a5d06b54a8f45a9f1e7c7b3fd5555555aaaa5550ebd4387550e1c3830e0c3970e1c38b0e1c38f55558850438070381c0e225554accb5554aa00505fc1d1751ab2a4d3f43cb83063d51e8b55541bfd555550e1ea83af0e1c183060c3975550ebd4387550e1c38b0e1c38f55550e407018a08700e07112aaa2f0395694d9f51f1b95400a0bfab2a8c1d035067e87a2d551e0c18306aaaaaa0dfeaa1c3d5075ea1c3aaaaa875e0c183060c183061c387161c3871eaaaa1c843828030181c0e2255549b556070387c6e5500282ff47e879f1e7c7d1b366c79b3e3c387aa0ebc3870e0c3830e5c3870e2c3870e3c3870e8743930e4070381c0e070395551f8fc3e3f1b8dc00505feaaaa858b162eaa858b162c58faaa8d9b366c58b162c58b162c0000000000002000180b01600130002aaa8f8f3e3ea8d9b366c79b363c00000002aaaaaaaaa000bf901005c00600f005804c04002078f1e3c78f1e3c78f 24 16777215 10 1023
def hc_65_1 : Nat → Nat := unpackHintV5 0xea3df3e4d55adb7259d445cbc94abfc34182b68330ae02209f5baa9e603e9be49f9b282f99a4619421618dcd9583d27f7d3da5749a296e5d8f62f6da5ca99350e6f14a61a1448976398ac034d52d2cfdf620bf10192de40c1b450499e0000126 0x2aa17557f858b162c58fa169cba306cc1a32f55555552736ccd8b162c5a34d934d93aa4ebd9a7162c58b461d781d186d79baaabfd55555543e1f51faa8fd555550b162c5d555232e8c1a3068cbad2aaaaaaaaaaad5275f2d38b162c5a30e8c461d18ab55554d4aaaab54cd52a5d06b5554aaa2d458b55162c583160c597aaa55163d458b5162c58b163ea67faaaaaaaaaa8b49aad52a21d13af969c587160b0e2c162c58b55aaa55a58fad51fa1742eaafeaab1faa0740c5d0b060c183868eaa1a3060c183060c1835a555555555555974bc183060c58b162e1875e430ebc55aa0703060e1730f1eaaaaa6cfc6e36acaa30740d418b17542d9a8b16aaaaa2c183060c183060c5d50b5162d55458f060c183060ea55555506ff555555974bd0e8a80c183062c38b0587160b162c5aad1b8fca6cfaaad038183070b163c58ba85dfd554d9f8dc6eaaa858b162e2a81197460d183465c387aaaaa4e6e59b162c58b469b268d364e20381c0e0728280381caaaaaaaaaaaa2802a83830e5c3830e1eaaa83870e1c387161c38b161c3870e2c58b062c18b2f5541c3870e2c7870e2c5870e2c58b162c7d5541d0e4c3a1c3a7372cd8b458b168b262c58b1647fa0a8381c0e1c38700e1c1601c0e07039555555078fd551fa1742eaaff1faa0a00740c5d0b060c183868eaa1a3060c0180c1830740e060e5d1b060c183162c58b869b270d364c3900c06070381c38070e01c0e55038183070b81c3c7d030746cfc6e5e41c060ea81a30740c0162ea85b3060c58b060c183060c183060c583060c183060c18baa160c18b160c183060c18b1e0c183060c1d52e8d8341830683260c183062d162c5a2c98b162c587201830e0c1800cfe1c38070e01c0e070394ae3f03067cfd030703a0703060e162c78b1750bbf9b3f1b97841c0197163d46bb367efe0c583065c78b1ebb41832e8b798b1e6e3ffcfdfe45d3fc79f858f562e0c197a172087039542eafe2c7c2cb83065eaaa66651a0d2e8b45a2d1eaaaa351a6d26aa01d78070e1c43a21baaff50f87cc7d5a50e749c5d0b162c58b163d5555571a3aac68d397c60f1834e5d695541143901c0e07038881c38070e1546e370b995478f55520e527162ea858b162c18b062cb8baa162c58b162c7d4acaa3541aa5d55168b5545aa8b45aa2d1eaaaaaaaaaa00720381c0e1c038700e07143a8086e8dc7e371b367e162c78b1750bbfa9b3eaab4aaa1070aaaa060c183060eaa8183060c183aaa8183060c58b162c58b162ea8183060c58b162c58b162cd9b366eaaa0742e85c3eaa89d5454527162ea858b162c18b062cb8baa162c58b162c7d546d39b362d162c5a2c98b162c5d2f4ebd38b0e2c161c582c58b166d79ba571f8fc7cfc2c58f162ea177f367e371f3f1faaaaaaaaa8183aa3e2c78f3e2c78f060c183665a5a41a0d268faa461d188c3a30183060c79f3e3c9a93aaa9a5aaaaa3f4b55503abfd40eaaa060c18f062c183060c183063d9941935060d068349a3eaaa8183060c183264c183260c183060c183060c183063c793164c58f1f55503060c061c180c183063cf9f1e4d49930e4c261c99555555555547e5bfad2b5555555540c1d55517060c79f163c79f163c7b320d26b4b49347d517060cba30e8c461d183cf9f1e4d49d55554d2d551fa55aaa07557fa0755517063c18f1e5c58f1e5c58f1ecc8349a93264c9a5d499349a3eaaa8997060c183264c997265c993264c997264c993263c793164c58f1f55517060cb970e5c2e1cb83cf9f1e4d49930e4c261c99555555555547e5bfad2b5544ea9183665d983465ea8f8b1e3cf8b1e3cf8f3e3da626b4b49349a4d1f548c3af1f87462f66bc79f3e3c9a93aaa5a9aaaaa96aaa0a8460d197460d197aa3e2c78f3e2c78faa3e3cf8f5a5a6649a4d268fa0a0880e070381c0e24d2d55555551fa58a00aa0e0c3970e0c387aa0e1c38f0e2c3873e3cf8f6650e4d438749a4d268faaaa0e1c3870e1c9930e1c9870e1c3932e4c193064c98f1e4c593163c7d447fa0a8381c0e0703881c384c03870e1c2aaaaaaaaaa8fcb7f5a54a2260cb832f548c3a30e1c3b30efc3870e02c78b1e1c78b0f136649a1c381c067f0603074cd552d1d54b460e8b830600c1930fd0f3e2c78f3e2c78f2e0c18f649ad2879069349a3c3901c18030601c060c181c0e07123f51b0ed2d1781c3e366cfc1d5620e03a2e1d1d5070e01fa1e5c1831e1c3871e1c5870ec9341a4d439350e1d268f27544c9932e0c183064c9870e1c3870e4c9870e4c3870e1c78f262c98b1e3ea0e400cfe0c1803060c381c0e2070e01c3847ea365e07070f41cdd0f8d9b3f2dfd69520e03a070d1d543460c180301833f43c183060cf8b1e3cf8b1e3d9268341a83969268f0e4030181c38070e01c0e07123f51b07039681b43e366cfc0d620e0307540d183a0601fa1e0c583060c1831e0c18306c935060d419341a0d268f26cea8993060c983060c183060c183064c983060c183060c18f1e4c593163c7d41c8060c383060033f870381c40e1c2601c3870e11fa8d83066cfd030703a070387c6cd9f96feb4a90728fd0f3e3cf8f649a4d26934793aa264c997260c983264c78f262c98b1e3eaa5ebd78f3e7c7935264c39309872647ea366e370f8d9b3f2dfd695371baaaa8f8f3e3d555556a97af5ebc79f3e3d56aaaaa96feab54caca97541aa3d516aaa2a1d19 24 16777215 10 1023
def hc_65_2 : Nat → Nat := unpackHintV5 0xb99db5b4355aac45fca63d829b42bf97ace591918787f6677fd2097c10f076417472dcd972342a6e31016795a762096359ae1753818b4806df47d80b468c53428d003c01a333063f2aaa17250d671ef58618819d0ac370061d29055831000156 0xa2f5517aaaaaa3e2c78f3e2c78f2e0c18faa469b26ed364cb83065c79b3e3ea91875e3b0e8c2e0c1971e7cf8f36bcdd5555555555555555552d2ad51f163c79f163c7d517060c7aaaaaaaaaaa30e8c461d19545c1832e3cf9f1eaaab4b54d554ab54cd52a5d06b5554aaa5cba9755aaa951e8b52e0c18f2e2c78f2e2c78f67faaaaaaaaaaab54a88742e0c1972e1cb85c397079f3e3d56a95996aff03a81d54ab5541500c1d55551f163c79f163c7d517060c7a34d93469b27545c1832e3cd9f1f4141101c06070381c0e5555555555551401540c1872e0c1870f55541c3870e1c3972e1c3970e1c387aaa83870e3c38b0e1cb83063cb8b1e3cb8b1e3ea83a1c98743872e0c1972e97265d2e4c79b3e3c8ff415070181c38070e01c0e0703955555557f81d40eaaaa288bc5ea858f163d99576bb551a8d069745a3d540381c43a21baaa63ead03a2e7e8797060c7aaaaaad747555d1aaad0f1e7c59f163c7a8228720380c0e0711038700e1c2a981c3e372a8306aaa41c0745cbd5172f51fa1e5c1831e5c58f1e5c58f1eacaa3541aa5d552eaaa5d2ea8b547aaaaaa5d26aaaaa00720380c0e1c2e01c3870e01c0e2875010dd540efe0c1d03060c7c6e5367d5569548380e8b97aa2e5ea3f43cb83063cb8b1e3cb8b1e3e8d97060cb974b932e97263cd9f1f4bcb83065cb872e170e5c1e7cf8f36bcdd540efe0c1d03060c7c7e371b8fc7eaaaa060c183aa060c183162c58baa060c183162c58b366cd9baaaaaaaaaaaaaa060c183aa060c1831e6cd8faa060c1831e7cf8f366cd9baa81dfeaaaaaaaaaaaa81d0f87d42ea89ccd4541e2a073320da075493262d479f1e7c7b2aa9b4d87111af466da63ead5507136930e340e8a81d40ea80161c38f3e3cf8f43a4d19b3741c3870e1c46235e1e83c7eaaaa81d5503aaaaaa060c1833e2c78f3e2c78faa060c183469b269b263cd9f1f540c183068c3af03a3079f3e3cdaf37555555555555555555554b4ab540c183067c58f1e7c58f1eaaaaaaaaab540c183068c3a31187460f3e7c7aad55352aad51f956a99aaaa55506a0c1aad52a0d06b5552a3d16a0c583060c1831e0c18306cff5555555506935555aa5443a030e0c060c180c183063cf9f1eab54accb03a07557faa3f2ad55545500307555540c183067c58f1e7c58f1f540c183068d364d1a6c98f367c7c40301941401c0e0703955555555547eaa2802aaa8183060c187060c183060c3830f540c183060c18307555070e1c787161c383160c183060c783060c1d50743930e870e0d060c1a0c983060c18f367c791fe82a060c3870060c0600c06070381c0e55555540e81d55fea8fd54508355a81c3c58b1e821c0e5503a07542c78b1eccca341a0d55546a345a3d36935500ebc03870e21d10dd554b03a067e8783060c1aaaaaabb4754ed1ad2a8f1e7c59f163c7a8228720180c0e071103870060c2a81839818f8d9b3f2a972eaaa41c060ea8183a0751fa1e0c583060c1831e0c18306acaa35541a0d5506aa0d506a8b547aaaaaaaaaa801c8061c0183006030381c50ea021baa060cb8307503bf8f8d9b3f26d559548380c1d5030740ea3f43c18b060c183063c183060e8d8341830683260c183063cd9f1f4bc1870603060c060c1831e7cf8f36bcdd503065c183a81dfc7c7cf9f8dc6e3f1faaaa8b83063ea8b83065c79b363ea8b83065c79f3e3cd9b366eaaaa077faaaaaaaaaa8bd0fa85d44e66a2a0f1555550b162c5d51b366cd8b162c5d5275ebd38b162c59b366cdd55551fa177faa8dd547eaaaaaa2f503a85d1399a8a83c5555540c183aaaa8183aaa060eaaaa8183060c58b162d1a6c9a34d93aa060c183162c58b461d188c3a30daf3755540eaaaaaaaaaaa0757fa81d555540c183060c18b060c58b060c183060c183060c183060c597aaa060c183163c183162c183060c183060c18b1f5550341930683060c183062d162c5a2c98b162c5d503060c061c180c183062c38b0587160b162c59b5e6eaaaaaa071faaa0742e85d55fe3f551faa1757f163d99069745b42d3a3668eaaa4993636aaa9b4d87111af466daafec7d5aa87c3e53f07136930e3fe85d5fc58f8a0e0c19785d42d3a3668eaaa010e93466cdd2f0e1c3870e1c46235e1eabf878fd5550f87c7e0 24 16777215 10 1023
def hc_65_3 : Nat → Nat := unpackHintV5 0xaea4a6ae8807abd0aea79110a55c8d9e0dd49731b7943cbd8d3dc088054e80a9d7794dd770124f66d64f5fddbe5a855654c5704f017147d1cc41e97a3aedbf34c58a2bca3f2569981ca2321c4c151bd41e1671590f5dc50a294d061106000184 0x555450b162c5aaaaaa80001700004ff5555554aa01feaaa2858b162d953db4e8b50000000000aaaaaaaaa00aa81d5517aaa175542ff8b162c5aaaab2aaaaaa0000000000027faaaaaaaaaaa5500162cb9787c3c58b0703858b555004fe6e37032e0cb8b170b858b163c58b162c58b1e0c18bfe0c18b160c183555555555550000000000013f9b366cd97060cb8b162e166c5c2c78b162c5aa8003060e07034e0c183060c183162c58b060c583060c183062ffaaaaaaaaaa800000000009fcd9b366c19b0703060e060c183162c58b55001e3c78f55555500000013f9b366cd9b366cd8f366c7aa80008e91a306ccbb3068cba3a1e8c58f1edc58f1edc7b31ec4d264d498750e1d269349a3c00000000000023746e366e8d9ba371b87c6e26b000f1e3c7a4d269349a4d1e000000002004017001803c01600700366cd9b366cd9b1e6cd8f26a4c000836155540eaa2ecacac9f55665549b550baa8797060c7aa3d16aaaaaaa837faaaaab55078a82e0c1975443a0f3e7c7aad5feaaaaa55a58fad52aac7eaaa565655665564fd540eaa06a0eaa17550f45aaa3c183060d55555555541bfd56aa0f15087454060c1831e7cf8f55abfd554b1f555aaaaa5558fd5555503aa8bd5555073f555541c381550baa8797060c7870e1c787161c3d54d4c4cb83065c3a1c98743871e6cf8f888385000cfe0c1803060c381c0e072aff5555555541e3f5551faa0a0aaaaaa8183aaaaa067eaa07550302aa17550f062c183060c18f060c183aa9a9898341830683260c183063cd9f1f11070a0060c383060033f870381c0e55feaaa81c7eaaaaaaaa3f5414155540eaa2f550baa879f1e7c7ab2b2ab32ab27d506a97545aa3d555555555408883850070381c0e2875010dd5feaaaaaaa58faaad2aa850555503aa8bd542eaa1e7c79f1f5535313366c79b3e3eaa0f150bd78f3e7c79b5e6eaff555555547eaa3f5555547c79f1f546cd9b363cd9b1f54bd7af5e3cf9f1e6cd9b3757faaaaaa5755555517a81d43ea1751399a8a83c54b4ab555544c9d51f163c79f163c797060c7aaaaaaaaaad53b0ebc761d785c1832e3cf9f1eab5354aab55547e55aaaa075517aa65559955959526c2eaa1f545c1831ea8f45aaaaab24d5506ff5555560f151545c1832ea88741e7cf8f55aaaaaff54accb547e55aaaa5a55a060eaaa8183060cf8b1e3cf8b1e3d555506aaaaab540c183070c3af21875e0f3e7c7aad4d5552aad51f956aaa55665565595a075503aa5070baa87d522d551e0c18306aaaaaaaaaa0dfeab078a8aa43a2a03060c18f3e7c7aad55557f6556aaaa3f2ad55555555450551f163c79f163c797060c7d53b4d93769b265c1832e3cd9f1f100c18504030381c0e072aaaaaaaaaa8fd5451540eaa2f5541eaaaa8387aaaa0217550faa2e0c18f0e1c38f0e2c3879a989d517060cb8743930e870e3cd9f1f41c385104400cfe0c1803060c381c0e072aaaabfd55555551faa8a2aaaaaa822aa8183060cf8b1e3cf8b1e3ea8183060e1a6c9c34d931e6cf8f88060c8061c3850070381c0e555555555551faa8a2aa060eaaaa81d55540eaa0754042eaa1f540c583060c1831e0c1830735313aa0683060d064c183060c79b3e3e0e141100c187060c0067f0e070381caaaaaff555555547eaa28ce0cb97ce0e3f55547c79f1eaaaaaab4ab9cb83ce0cb8f1e7c59f163c7a822c4070381c0e22070e14153555547e55a55528aa075517aa85d543ea8f8f3e3d55995595656541aa5d516a8f5555649aaaaaa8141c3851044070381c0e2875010dd55557faaaa3f32ab2a945503aa8bd542eaa1f547c79f1f35313aa366c79b3e3e0f15154bd78f3e7c79b5e6eaaaabfd5551faaaaaaaa858b162ea8d9b366c58b162ea97af5ebc58b162cd9b366eaaaaaaa37551faaaaaa3e3cf8faa366cd9b1e6cd8faa5ebd7af1e7cf8f366cd9baaabfd55546eaa5f55545ea0750f87d42ea89ccd4541e2a 24 16777215 10 1023
def hc_65_4 : Nat → Nat := unpackHintV5 0xb906beaeaa97aa4519a33dc29c75b297c92b916599886a3f83793c7cc5ad78990b73a93c6c61d265dda15ce23f53ca464f9d0b4b09254609403ecdcf3ab1072fbabe255e971f8d741b7506193091162cc111e1130e20f0081583024574000091 0x32e0cb8b170b858b163c58b162c58b1e0c18bfe0c18b160c1835655baa0d52eaa8b69aaa2d16a8b45aa2d1eaaaaaaaaaa0070381c06070e01c3807038a1d4043e6cf9b2e0c197162c5c2cf8b858f162c58b4faab2a81c380c18381c0d383060c183060c58b162c183160c183060c18bfeacab35541a0d5506a7541aa0d516a8b555555555500381c061c0183006030381c50ea021f367cd833e0e060c1c0c183062c58b169f55655038722f17060c7d52aaaaaaa0c183065e998f469c7a287019441c0e07110391555554ab5451517063c18f1e5c7971eaaa9757faaa5cb83060c1a3fea8306aa8f468c7a2870181c385c3870ffc0e07110381c2f038bc5e1f239551c8e20e23a468e87b71ecc7aaaaaaaaaccba306cc1a32e3c7a316dc58f1ea08a1c39070381c0e0711038700e1c2a91c8e1f2395519fa467e88383c78f1eacaaa0d52ea8b547aaaaaa801c0e070381c0e2875010d9b366c79b1e9f5565503870b970002a8180502ba1eec58f1eec58f1e0c183060c7b24d43875060d068349a3c000000000002a8d9ba366e81c0e1f1b89ac000cb83a07fe8183a95d0f060c18f062c183060c183063d926a0c9a83068341a4d1e000000000000208c0800603000180003001803c01600700aa060e819ba070387c6e26b000106c2280280b97000aa2e0c18f4e2c78f4e2c78f6641a4d43875a49a3c000000000002aaaaaaaaaa580281ffaaaa2f5517060c7d43e174cc8349ac4d69268f0000000000001080802e1700180c0880080007802c00e0155555555552c000441540c18307448b45b320d0600000000202c0160404003001801c02aaaaaa580008828000183000a2562c78f562c78faa060c1835a50e1d99068349a3c000000000002aaaaaaaaaa5802aa075540ffd0baaa1e3ea8183060d969689936641a0d268f203800000000000084001100101000c2e00301803c01600700aaaaaaaaaa960002200754030600140009e8797063c18f1e9c58f1e9c58f1ec9341a4d43875261d268f00000000000010aa2f038d9ba366e87c6e26b000307540ff83060ea4f43cb831e0c78f2e2c78f2e2c78f649a0d26a4c9a9326934780000000000008230200b800c02e17000b8000f005801c02a8bc0e2e5e8b9ba1f1b89ac00041b0163c5aba4e2c18b2e2c18b1742ffd0b1750b162c58b1ec935164d458b49a4d168b00000000000010460400b058002c560017001802c01600700aa162e859ba371b85c2e26b000106c2aa88183060d99068345a2c000000004202001800c01600b003805555554b000110555450b162c5b324d268b45800000000840401700b802c1e00b05801c02aaaaaaa580008828001f834e5df834e5ea858b000a2162c58b5a50e1d99269345a2c000000000002aaaaaaaaaaa5802aa075545eaa85d550bfe2c58b16cb4b44c9b324d268b45901c00000000000042000880080802e00300583c0160b00380555555555554b0001100b165cbc3e1e2c58381c2c5a4d2600088c8462301d8ec02e030582c0e01b8dc46c065c197162e170b162c78b162c58b163c18317fc183162c183069349a0d26a2c9a8b168b4580000000000008370200b800c0160b000594c00160f00582c00e006cd9b365c1832e2c58b859b170b1e2c58b164d49800106c0183070381a7060c183060c18b162c583062c183060c18317fd26935060d419341a0d168b000000000000106604003138000c060003001802c01600700366cd9b066c1c0c1838183060c58b162c9a9300020d8032e0e81ffa060ea5743c183063c18b060c183060c18f55555555555000000000013fd5030740cdd0381c3e372a80503ff55545eaa2e0c18fa87c2e955555555554000000000004ff5555555554aa01540c1830744aaaaaa00000027faaaaaa5500aa281ffaa060c1836541a8f56ac7800000000055555555005540eaa81ffa175543c7d503060c1aaaab2aaaaaa0000000000027faaaaaaaaaa550007540302013d0f2e0c7831e3d38f4e3d55555555556a8bc0e371b87c6e55060ea81ff060c1d49e8797063c18f1e5c58f1e5c58f1eaaaaaaaaaaaa00000001700004ff545e07172f45cdd0f8dcaa002c78b5749c583165c583162e85ffa162ea162c58b163d5555555555400000000004ff542c5d0b3746e370b85caa0155440c18306aaaaaa00000027faaaaaa5500 24 16777215 10 1023
def hc_65_5 : Nat → Nat := unpackHintV5 0xb79184b3acf9af2522a8b59ca351599ace219276168e90f98a690a85e1227f7d997b80ff71ba7268465d626d765dcd285779954e524a49514042cda13ea10b39415832a9a62c8d87228e80192e5815010b10592a1004150af1450465a3000119 0xa07feaaa8bd545c1831f50f85d2aaaaaaaaa800000000009fc0080802e0030220020001e00b0100aaaaaaaaaa55000220aa060c183a255555500000013f8002c016040400300180805555552a8001105000030600144ac58f1eac58f1f540c18306aaaaaaaaaa00000000002015555555554aa015503aaa07fe85d550f1f540c18306aaaac93555555000000000013f8010004400404003001803c01602015555555554aa0004400e8060c00280013d0f2e0c18f4e2c78f4e2c78f55555555550000000000000aa2f03979fa5e7e87c9e5500060ea81ff060c1d49e8797063c18f1e5c58f1e5c58f1eaaaaaaaaaa0000000170380009fc004604017001805c2e00170001e00b0100aa2f038b97a2e7e87c9e5500020f80b1e2d5d27160c597160c58ba17fe858ba858b162c58f5555555555000000000013f8008c080160b00058ac002e003005802c0402a858ba167e8fc7e170b95400083e155440c18306aaaaaa00000027f00202001800c01600b0100aaaaaa55000220aaa8a162c58b55555500002e0009fc0080802e017005802c0402aaaaaa95400088280023834e5e3834e5ea858b000a2162c58b55555555550000000000100aaaaaaaaaa5500aa81d5517aaa175542ff8b162c5aaaab24d55555400000000004fe004001100101005c00600b0058080555555555552a8001100b165cbc3e1e2c58381c2c5aa8027f0464231180ec760170182c16201f8fc47c065c197162e170b162c78b162c58b163c18317fc183162c18306aaaaaaaaaa000000000027f001b81005c00600b058002ca6000b00580801f367cd97060cb8b162e167c5c2c78b162c5aa800107c0183070381a7060c183060c18b162c583062c183060c18317fd555555555400000000004fe00330200189c0006030001800c01600b01003e6cf9b067c1c0c1838183060c58b162d5400083e0023a468c1b32ecc1a32e8e87a3163c7b7163c7b71ecc7aaaaaaaaaaa800000000000055233f48cfd2391c3e472a800f1e3c7aaaaaa80000009fc000200b800c01e00b01005e6d79b5e6d79b1e6d78f5500020f830381835743c183060d555555554b975a551e3dd8b762c78f50450e4030181c0e22070e00c18550381c3e772abb3f4ecfd10701970740ffd030752ba1e0c1831e0c583060c183060c7ab2a8d5506aaa0d06a8341aa0d2ea8b547aaaaaaaaaa801c8060c0187006030381c50ea0255030740cfd0381c3e93eaacaa41ca6aaa2e0c18f5555555a555552e5c78f4e2d38b1e3d411620380c0e071103870a0aaaaaa55aaaa28a07feaaa8bd545c1831f50f85d2b32b2a8354baab2aacca8b547aaaaaaaaaa81101c065041c0381c50ea02555555555532ab2a945503060c1d32a2d516acaca83541aaaaaa801c0e4403018a1d404aaaaaa65565528aa681ffaa060c1835555555a555060d5478f562d58b1e3d411620180c0e07141103870a0aaaaaa55aaaa28aa81d5503ff42eaa878faa060c183556655655959506a83545aa3d555555555408385044030181c0e2875012aaaaaaaaa9955954a01d29e8797060c7aaaaaaaaa8306aab43c7a7169c58f1ea08a1c80e030381c440e1c03870aa2f0387c9e55ae7eab9fa20e0307540ff83060ea4f43cb831e0c78f2e2c78f2e2c78f566551aa8341aa5d2eaa975552e97545aa3d555552e9355555003901c06070e1700e1c38700e07143a809545e07172f45cfd0f93c9f5565520e0b1e2d5d27160c597160c58ba17fe858ba858b162c58f56551aaa2d56aa8b45aa0d52ea8b45aa2d1eaaaaaaaaaa0072038700e1c0381c0e07143a809542c5d0b3f47e3f0b85c9f5565520e555303060c1ab2b2a0d506a8b545aaaaaa81100c0607038a1d404aaaaaa65565528aaa9a162c58b565654baa5d516a8b5552eaaa81101c2e1c381c0e2875012aaaaaa9955954a13832f555342c58b16aaaaaab4aa9cb83b60d3975162d55411620381c0e07141103870a0aaaaaaa55aaaa28aa81d5517aaa175542ff8b162c5aab32ab2acaca8354baa2d516aaaaaaaaaa041c28220381c0e07143a80955555555554caacaa502c5972f0f878b160e070b16ca355daed546a341a5d168b45a3d540381c43a21f8fc7d6 24 16777215 10 1023
def hc_65_6 : Nat → Nat := unpackHintV5 0x82e301bfea61ded0494ef61c87127a2b6588ed962728c37de55c9b492c168dd5273909d17094bc2b223e0805141aba846d683e050c9d36730d0b6405c1b102b52ae94365cc9672d042e2161ebeac8bcbe504266fe19a1e40904f3032d55408f41e00011e 0x4748c58ba162c58b162c3870e9cba306cc1a32f402c1723a469d9b34e2c58b168d26a3261c39070381c0e07038700e1c0381caa3f1f85c2e3e7e8f9fa3f1f8838ae938ba162c58b161c3d513269cbb706dc1a72ea08aaaaaaaaaaa1c80e0703881c382822551f8fc2e171f3f47cfd2a907126aba4ea9741a870f541d1aaa8750e1d543870e0c3830e5c5d0b545a2d458b162c067faaaaaaaaaa8749aa8721410e01c0e070e1c3870059fd12a9593ea7e3f073f41c3d0b85caa41c5749c5d0b162c58b0ed52a72edc1b7069cb8b1602c162d90e9349a2d16a1e5a0e4070381c0e070e01c380712a8dc6e170b8d9ba366e89ac41c5749c387aa0e8c3870e0c3830e5c5d0b162c58b01699fe9349a1d438750e1c99345a2d5265c983260c9930e1c9870e1c3870e1c3870e4c98b163c78b162c58b162c5d41c80e0703870e1c3802cfe1c40e1c2601c3870e1546e37073741c3d0b85c4d6264e899ba20e03060c18b162c583060c1d746ae5757460c1a834183060c0180c1a4d268341a2d16a1c3a93261c0e030181c06070e00c180710d9b366c183060c58b162cd9b371b366e26a4c0e1c060c1830e1c3c1e0ecc183060c183060c58b162c183060c049a4d06ff5060d438750e4d168b06dc1c0e060d5061c183060c1830e0c383060c183160c783060c583160c183260c381c060303870e1c3802cfe1c4060c01870366cd9b060c1830e6c3c1c387858b162c9a93060c1c0cd8380e1c060c183162c58b060c183ee8d5caeee8c183060c183060d41155555555554381c0603038201c3828221f367cd83060c18b162c59f3e6e3e7cdcaa070e2b2adc183060d41870e1e0f0766a1c3aaaaa87060c183060c183162c58b45aaa2c183060c055555506ff5555550e0710e0a00c06070e1c3870059fd10f9b3e6d3eaac0c183061cf8783870f0b162c5aa81c389d5a70e1c3c1e0e1c387061c1872e2c58b162c58b1602b569d38743870e87262c58b161c0e070381c3870e1c0167f0e070f9f3e7cf9f3e7c39f0f070e1e162c58b3e7cf9f03870b97aa0e1c1d0307030740c1aba1eec58f1eec58f1e0c18306c935050620d06934787201a0a00c06070380c4aa366e8d9ba070387c6e26b10701970740ffd030752ba1e0c1831e0c583060c183060c7b24d41935060d068349a3c3a3aa0e1c183060c1830e1c1830e0c183060c183060c183061c7870e1c5870e007201830061c0180c0e0704fea0ad5030740cdd0381c3e371358387a0e6e88395555545cb83060c1870f545c1831e9c58f1e9c58f1ecc8349a82c24d1f101c064828070390955555555552c5140ffd55517aa8b83063ea1f0ba6641a4d626b49347d555072e0c183061c3d55070f41ea838f0e1c38b0e1c0880e032820e01c0e09fd415aaaaaaaaaa96aaaa28aa060c183aa45a2d9906830e2c3870e2c387aaaa060c183060c18300381c88060304fea0ad555554b555514555503060c183060c1d52b163c7ab163c7d503060c1ac283320d069347a84844030181c0e40855555555554b145540eaa81ffa175543c7d503060c1ad2c4d99068349a3e83d5555070f55540c183060c183061c7870e1c5870e05070e1441100c060703827f5056aaaaaaaaaa5aaaa8a01d07060ea8383a060c1830f27a1e5c1831e9c58f1e9c58f1ec9341a4d4149893478720380c0e828070381c54aa2f038d9ba366e87c6e26b1070183aa07fc18307527a1e5c18f063c797163c797163c7b24d06935264c9934ba932693478747541c3872e0c183061c3872e1cb870e1c3872e1c3870e1c38f0e1c38b0e1c00e4070181c38070e01c0e09fd415aa2f038b97a2e6e87c6e26b070f41cdd107058f16ae938b062cb8b062c5d0bff42c5d42c58b162c7b24d45935162d269345a2c3a3aa0e1c38b0e2c3870e1c38b0eac3870e1c3970e0c3830e1c38b0e1c38b0e1c00e4070e01c38070381c0e09fd415aa162e859ba371b85c2e26b070f41cdd1072aaa8183060d99068345a2eaaa8183060c183060c38b0e1c38b0e1c08806030381c13fa82b5555552d555451555542c58b16cc932697268b45d555072e1c3872e1c387161c387161c381101c0e0703827f5056aaaaaaa5aaaa8a2aaa9f834e5df834e5ea858b0e1c3870e1ea858b162d614199269345a2d424220381c0e072042aaaaaaaaaa58a2aa075545eaa85d550bfe2c58b16b4b136649a4d168ba0f555541c3d555072e1c187061c387161c387161c38141c3851044070381c0e09fd415aaaaaaaaaaa96aaaa28162cb9787c3c58b0703858b49a4d1d07461d1870e1dd87761c3872e0c187161c58700e0713fa29b8dc1e37032e0cb8b170b858b163c58b162c58b1e0c18bfe0c18b160c18349a4d06935164d458b45a2c3b70f0783870e5c183060c3870e2c38b0e1c3870e2c3d30e1c3870e2c3870e2c38700381c0e03038700e1c0381c13fa82a6cd9b365c1832e2c58b859b170b1e2c58b164d49870e1e0e6c3c070e03060e07034e0c183060c183162c58b060c583060c183062ffa4d26a0c1a83268341a2d161d98783c1c383061d383060c183060c183061c383060c183060c187161c387161c3801c0e030e00c18030181c0e09fd415366cd9b066c1c0c1838183060c58b162c9a930e1c3c1cd8780e1c0e1c3a3a468c1b32ecc1a32e8e87a3163c7b7163c7b71ecc7b1349935262824d269347870e41c500e8070381c0e0712a8d9ba366e8dc6e1f1b89ac41c1e3c78f49a4d269349a3c38783c1c3872e1c187061c3871e1c387161c3801c0e070381c0e09fd415366cd9b366cd9b1e6cd8f26a4c3870f07361e03870b9700028180502ba1eec58f1eec58f1e0c18306aaaaaaaaaa00000000000154bcfd2f3f40e070f97caa000cb83a07fe8183a95d0f060c18f062c183060c183063d555555555400000000004fe00230200180c00060000c00600f005808055030740cfd0381c3e5f2a800107c2280280b97000aa2e0c18f4e2c78f4e2c78f5555555555000000000000aaaaaaaaaa5500 25 33554431 10 1023
def hc_65_7 : Nat → Nat := unpackHintV5 0xe6ea3bd82bb0d095e5c64e92be51ffb8b168b1b1c0acc13ca605afa18d1e9da8f996bdbb9019a9874e337fe9d979859972c9af68ca806339645c39c055e5954cd245452de93ae6923465a02be62024b9cb1e719216620408df61040137000100 0xc183073d1ab95d3d1830600c060c58b162c183060d41830683069349a0d06a0c1a8f1e8345870380c06070e01c38070381c4366cd9b060c183366cdc6cd9b858b162c9a9303870183070381b7060c1830058b162c183162c183060c183163c183060d26935060d419341a0d16ff5162c5b3170b858b060c583060c183060c183062c583062cb83060c183060c1aa2c78b0e0701830e0c1800cfe1c0e071038700e1c0d9b366c19b0703060e060c183162c58b26a4c58b170b362e03870183060c58b162c183060fda3572bbda35045060c58b060c183555555555550e0701881c0e070e0a0887cd9f360c183062c58b167cf9b8f9f372a81c380c18381c0db83060c180acab35541a0d5506aa0d5062c58b160c583060c183160c18306a2d5555555555545bfc381c060c383060033fa1c140381c443e6cf9b067c1c0c1838183060d3eaac2c58b16aa070e03060e0703060c1830078f062c183060c18f060c1830683060d064c183060c78f0e0701830e0c1800cfe1c0e07038bd7833e0e060c1c0c183063d78f5ebc0e1c264c0001d1750e1d553d0f4e2c78f4e2c78f2e0c18f19500505555000000000000aa5e7e979fa2f0387c9e550049a0e8baa5d06a9e87aa3d16a5c1831ecff5555555400000000067f000011810088008000701e00b0101002a9593ea5e070f93caa00041f0aaaa2e0c18f4641a4d268f00500e1eaa878f4e2d38b1e3c993000000000000000aaaaaa96aaaa00aaaa2e0c18f67fad20d269347ab17a81d43ea1751380000067f0000000020200380f005804c2602204400400015555552d55540004414000aaa1c3d527163c7a7163c7d517060c7a80028aaaa80000000000055555555552a80555555555517060c7aaa8aaaa80000000cfe0000404040400701e00b010100165060d554b97aa45aaa3ea8b83063d55567faaaa881c00000000067f00001000440080800e03c0160213011001655597d555552a80011003a2e9e8797060c7b4c20d269347a800070e0c183064c38f1e9c5a7163c7d000000000cfe00000000551781c3e371358d9ba366e8001d174f43cb83063d699fe8349a4d1ea932e0c183064c98f1e4c593163c7d40000033f8000000008c0800e03c0160130100984c00260001545e070f8dc4d6264e899ba00020d8000e2f172e0e2e1e8387469e938f462c78f4e2c78f2e0c18f4748d1aec9bb51932e0c1971e9d38f0000000000000aa467e919fa2f0387c8e4723800197065d38f4e3cb83063cb83065c7a74e3c0000067f000000800e03c016013010017af5ebcb83065c7a74e3d7af5ebc00083e05cb800140c02805d0b060c1830e1c183060c183574adbadc9b75b93060c183162c58b000000000000aa3e7e8f9fa070385c2e3f1f8001970740ffd030750ba160c183160c583060c183060c5aba560d064c1a0c183060c18b162c58000000002cfe0000230200180c00060000c2e00301801c0980801540c1d033f40e070b85c7e3f000107c09930005749db834e5db834e5c5d0b550e1d458b162c5401415554000000000002a8f9fa3e7e8fc7e170b9540126aba4ea9741a8ba16a8b45a8b162c5b3fd555555500000000059fc000046040220020005c006007040400aa564fa9f8fc2e172a800107c15d271742c58b162d91269345a2d40013976e0db834e5c58b161c387162e80000000000000002a8dc6e170b89ac6cdd1b37400ae938ba162c58b16b4cff49a4d168b54997260c983264c58b162c58b162ea0000059fc0000000260701181005c00600702602013098004c0002a8dc6e170b89ac4c9d1337400041b0060c183162c58b060c18349a4d45068b45d746ae57574600a00c183061c383064c980000000000000001b366cd83060c18b162c5935266cd9b8d9b370003060c18b162c583060c1a4d26837fa83068b45836e0e070306a83160c183160c183260c0000167f000000001981000c00600702602003018000c0000d9b366c183060c58b162c9a93060c1c0cd8380008361ad1ab95dad183060c183060002c58b161c3aaa83060c1aaa80028aa8000000000001f367cd9f3e6e3e7cdc0c183062c58b16aa00acab7060c1835062c58b16a2c5aaa8b1e0c18306aaaaaa0dfeaa000000000b3f80000cc08040011000185c006030038202001f367cda7d558183060c58b162d5400083e0023a468c1a72ecc1a32e2c5d0b161c3d0b0e2e162c58b4748d1b1c9c751934ecd9a7162c58b0000000000000aa3e7e8f9fa3f1f85c2e3f1f8013ab4e2c58b162c58b16ad5a74e2c58b1600000b3f8000004017001801c09808007cf9f3e7cf9f3e2c58b167cf9f3e00041f00740c5d0b060c1830e1ea8b97060e81c0c1830600c060d5d2b060c183162c58b6eb726dd6e4c3900c06070181c38030601c0e550381c2e171f3f47cfd1f8fc41c065c1d03ff40c1d41c3d507460c183060c187060c387060c183060c183060c183060c3971742c183062c18b060c183060c18b015d2b0683260d060c183060c3a1c3874393162c58b0e4030600c38030181c3870e1c0167f0e072a8183a067e81c0e0e7e8387a170b8fc7e20e0b161c3a746cd1c0b168c993668d4693264c3c872e0c193858b95264c3870e070381c371b89c6e162d90e834ba2d83874e8d9a38162d264d46cd55546a30e1c3881c0e1f58fc7e 24 16777215 10 1023
def hc_65_8 : Nat → Nat := unpackHintV5 0xcca1a2c80527c420f9bd9da1b74995ae3645a691e99c4a9295c9a08d920e8665cb80717d7aad7175f52e6dea03604b686000125f5c29595981505e3f4a318b410a4a4040323bd11c36595e2e161128c15523ed351c71df1475ff0d55c8000355 0x2aaa8183060d9feb48341a4d1eac0ea0750fa85d44e00019fc000000000080800603c016013010220020000aaaaaa96aaaa000220a000060d556a958b1e3d58b1e3ea8183060d4001455554000000060000015555555554aa0155555555540c18306aaa2aaaa0000033f8000001010101000c07802c040400594183555065ea916aa8faa060c18355559feaaaa000000033f8000000800220040400301e00b0101001655597d555552a80011003a06ae8783060c1b220d069347a80003060c183060c18f1ecc5b3163c7d0000000000000000550381c3e371358d9ba366e8001d035743c183060d699fe8341a4d1ea83060c183060c18f1e4c593163c7d400033f80000000004c0e0230200180f005804c040261300098000550381c3e371358993a266e800083600c183062c58b160c183069349a0d06a28b9e8d5cae9e8c183060c183060c014078f0000000000000000366cd9b060c183162c58b26a4cd9b371b366e00060c183162c58b060c18349a4d068345bfd458b16cc5c2e162c183060c183060d5163c58000cfe0000000000370200180b005804c040160b000580001b366cd83060c18b162c5935262c58b859b17000106c0183060f5a3572bb5a35060d5458b162c183060c58b00055555000510000000000003e6cf9b060c1833e7cdc7cf9b858b162d5400183060d59566a835418b162c583060c1a8b5555555516ff00019fc00000000006e04003040011000583c0160b0101000f9b3e6c183060d3eaac2c58b16aa00041f000183a060c183a060c1c8e87a3163c7b7163c783060c1a3a468d8e4e3a8c983060c18f6edc7800000000000055233f48cfd0381c3e472391c000c183063c783060c183060c18f1e00033f80000000400301e00b00980800bd7af5e0c183063d7af1ebd7af5e00041f0060c1838060d18f6e3d183264c9a351a4c99326dc1c0e41830703072a3c58b1e4c9870e1c0e070386e3713364e370306cc8341a0d81838060d264c5a8f463db8f546a355546a36e870e1c40e0713e8d5a472391a0c1d03060c183a0060391d0f060c183462c78f6e2c78f4748c183060d1a4d464c7b76e3c38720e030181c38070e01c0e07039540e07233f48cfd0f91c8e47107058f160c1d503460c183060c583560c183060c583160e8183060c183060c18142ffd0b17503062c583060c183062c783060c18306ae958b4593168b160d060c1a0c983060c18b162c5872038700e1c01830e0c1800cfe1c0e07039542c5d0b3f40cfd030740e070b85c7e3f1072276d89db478b03d555555011555540c183062c583060c18307540c18306db276d262c58b17100c200e1c280381c0e072aaaaaaaaaaaa8a2aa060eaaaa81d555503075540cbd50142eaa85ff062c183060c18b060c1839a989d50341830683260c183062c58b17070a088060c383060033f870381c0e555555555555555551403a060c1d51326a08aae8783060c1b3163c7b3163c7aaaaaaaaaaa87201881c38280703889540e07333f4ccfd0fa5caa41c49a0c1d50346aaa0d4183550740d506835015d0f547a2d418b060c183063c183060d9feaaaaaaaa0d26aaaa1c85043803061c1830019fc381c44aa564fa833f40c1d0381c3e972a90701d20c183261e8a060c183463d58f41a0d41a9349a3ea81d5551381901c80e070389441caaaaaa96aa28aaa59aa08aaa060c183562c78f562c78f69a41a0d41835264d268f88064070e1401c0e0712aaaaaaaaaa58a2aaaa81d501540c583060c1831e0c18306cff5a5060d419341a0d268f56075540e075503a81d43ea17513a201830e0c1800cfe1c0e0712820e155555555552d555451555554a08b540c18306ac58f1eac58f1eaab3fd555555562018304067f0e1c140381c44aaaaaaaaaa5528aaaaaaaaaaaaaa02aaa818b060c183063c183060d55555555555622201830e0c1800cfe1c0e222ca0c1aaaaa83aaaa41aaa0ea8045aaa3ea818b060c183063c183060d55567faaaaaaaaa1c142201830e0c1800cfe1c0e222caab2faaaaaaaaaa55288060c183060d18f463d06835264d46ff06934783260c183060ff835060c1835063c9931f5030181c0e070381c40e1c261c387fe0381c6e370f8dc4d6271388380e81836a941830060306ae8783060c1b3163c7b3163c7b20d06835072d24d1e1c80603038700e1c0381c0e2550381c6cdd1b3743e3713588380c1d03a81a3060e8180ae8783160c183060c783060c1ad33fd06a0c1a83064c9a0d069347aa0c193060c183060c183060c993060c997060c183060c1831e3c98b262c78fa83900c187060c0067f0e0703881c384c03870e1c2a819ba060e81c0e1f1b89ac4c9d1337441c 24 16777215 10 1023
def hc_65_9 : Nat → Nat := unpackHintV5 0xd95a0dd3a56dcc5dd2c6318bbd1e45b82d3cb29d64aad5f2a445a49b663895398b8c26458695647ee5ec7a85187242116c25876346385ddd5a55c6065101314c2d35447dec3d25d630cb172842221e268718b15d1181cc0bf16404f1c000013c 0x5548ea958f563d699fe9349a4d1ea932e4c193064c98f1e4c593163c7d40047f0000000000981c080b800c01e00b00984c04400e0700110002aaaaaa5aaaa80008801d170e1d5549930004f43cb83063d38b1e3d38b1e3d5441aa00a0aa000000000001545e072f3f4bcfd0f93caa000e8ba8d59526a7a1e5c1831ea8f45aaaa0dfeaaaaa8011fc00000000000e05c2e003018088008000f0058080801545e072b27d47c9e5500020f803a06ae8783060c1b24d45069347870f540c180280f1ecc5b3163c79326000000000000001540e070f8dc4d6366e8d9ba000740d5d0f060c183649a0dfea0c1a4d1e0d1d50306a831e0c183160c183260c008fe000000000007006003007802c0261301100180c00060001540e070f8dc4d6060e819ba00020d840c183060c183463d18f5155550000119fc000000019fc0011000004fe000e072391c3e472a80002aa870e0e818306000ae87b3163c7b3163c783060c1aaa80028aa800000000000552f3f4bcfd0381c3e5f2a802b32a8d0740d41aba1e8b554783060c1aaaaaa837faa8011fc40e000000000007040011000185c00603007802c0426022005527d5581c0e1f2f95400083e00e8ba7a1e5c1831ec935060d06ff1268f0e1ea898750001e3d38b4e2c78f060c0000200000000002a8bc0e1f1b89ac6cdd1b374000e8ba7a1e5c1831ec935060d06ff49a3c9a3aa264d51e3c98b262c78f060c18011fc00000000000e05c00600f005804c040261300098000551781c3e371358993a266e80008360ae938ba162c58b16c9349a4d45161c3d50b0e9cbb706dc1a72e00a03c7800000000000000551b8dc2e171358d9ba366e8015d271742c58b162d9269349a2dfea2c58b47542c58b2e2c18b062c5aa2c78b0023f800000000001c0b800c01600b00984c0440160b00058000551b8dc2e17135858ba166e80008360ae93aaa870e9cbb706dc1a72e2e858b162c58b16000aaaaa000a2000000000001547e3f1f3f47cfd0b85caa00ae93ab2a8d506a971742c58b162d45aaaaaaaa8b7f8011fc0040e000000000702e003010004400160f00582c042602200551f8fc9f556170b95400083e14ae878f1f43c78011fc0000000e05c00600f005804c0400aa5f2f87cbe5f2f800083e01c38707178b9707172811d0f462c78f4e2c78f2e0c18f4748d1aec9bb51932e0c1971e9d38f0e1c8380c18070601c06070381c0e55233f48cfd1781c3e472391c41ca264e838750540745d38b1e3d38b1e3d3d0f2e0c18f555555555550060c039080c0e07111f9fa7e7eaa8bc0e1f279548389341d1754ba0d43a3aa0e1d55438750eaa027a1ea8f45a97060c7870e1c787161c3b3fd555555555550e42821c0067f060c0183061c0e22552b27d4bc0e0e1e839fa1f2795483952b5554151549c58f1e9c58f1e5c1831ecca4c9a870e8349a4d1f11400c184030381c0e255555555554b1455555501545c1831e1c3871e1c5870ecff5a41a4d439350e1d268f562f503a83c1eaa0f5543ea17513a20067f060c0183061c0e0712820e155555555552d555451555554a8a1549c58f1e9c58f1e5c1831eaaaaaaaaab100c1828200c0381c44aaaaaaaaaa5528aaaaaaaaaaaaaa02aaa8b83063c3870e3c38b0e1d5555555555562220067f060c0183061c0e222c83554bd5287555550e1eaaa8045aaa3ea8b83063c3870e3c38b0e1d55567faaaaaaaaa870e0a2110033f830600c1830e07111655597d5555555552a942d50741d17060c01832627a1e9c58f1e9c58f1e5c1831ec875a50f20d26934787203830060c0380c1830381c0e2551b3746cdd1781c3e3713588380e8b8747541c3809e8797060c7870e1c787161c3ad33fd069350e4d438749a3d5265c997060c183260c9930e1c3870e1c9930e1c9870e1c38f1e4c593163c7d41c8019fc1830060c1870381c40e1c03870aa2f038387a0e6e87c6e26b132744cdd1070197065c38783c1c3809c7a71e5c1831e1c3871e1c5870e5c1832e1d0e4c3a1c38f4e9c787038033f830600c1830e070381c5ebcb83065c3870f073e1e1e9d38f5ebc0e1c163c583a060c183060c1830742ffd0b17503060c18306ae958b4593168b160c183062c58b16000000033f80000008c080160b00058ac000602c1e00b05804c0400aa162e859fa070385c2e3f1f800083e140000c183aaaaaa162c002a28183060e3b1c9c76393aa060c183162c58b0000000000000aaaaaaaaaaaaa00aa8183aaa065eaa85d550bfe0c1830735313aa060c183162c58b000000019fc000000800220020200180b005804c0400aaaaaaaaaaaaa000220264c0001d0355060d55d0f662c78f662c78f060c1831500505555000000000000aa5e7e979fa070387cbe550049a0e81aa0d06aae87aa3d16a0c18306cff55555554000000067f00000011810088008000301e00b0101002a9593ea0e070f97caa00041f0aaaa060c1834641a0d268f0050aa060e878f562d58b1e3c993000000000000000aaaaaa96aaaa00 24 16777215 10 1023
def hc_65_10 : Nat → Nat := unpackHintV5 0xb5e977b1711eab6184a6ad2d9f5dd49ef8199b78e096f12290c98a8c152d847de680550a7b5540746dba6ecd6866422360c55f5a11ad54a95a4b8e4747451241bd623d751237ed623514b631ccd22d09312436351b3e3e10d69a0696900001a5 0x507061cb87061c3aba1e1c3871e1c5870e3c7d0743930e870e3c791fe82a0e070381c0e072a8387a0e7ea87d51072a95694993000aa2e0c18f4e2c78f4e2c78f5515005055000000000000aaaaaaaaaa5500aa656549b545c1831ea8f45aaaa0dfeaaaaa91fc00000000000080b800c0440040007802c040400aaaa5665aa55000220aaaa060c18366441a4d1f555400a03c7ab16ac58f1e4c98000000000000005555554b555500555503060c1b320dfea0c1a4d1f5554a831e0c183160c183260c8fe000000000000400c00600f005804c0400603000180005555554b555500011003814020740c183068c7ab1ea2aaaa000000000000c00000402aaaaa95400016956a8183000aa562c78f562c78f060c18355500051552000000000000aaaaaaaaaa5500566566a941d522d551e0c18306aaaaaa0dfeaa47f00000000000020400110001800c01e00b0101002a9955aaaa954000882aaa8b83063d990689347d55528000f1e9c5a7163c783060000000000000015555552d55540155545c1831ecca0c1a0dfe9347d5552a3c793164c58f1e0c18323f8000000000004c0e0405c00600f005804c0402613000980005555554b555500011055552b1eac7d50f56ac791fc0000000080b800c01e00b0098080155555554000440a08b555544c9d527163c7a7163c797060c7aaaaaaaaaaac2070e0a01c0607038895555555554aa50040eaa2f54caab32ab2b2a4d85d543ea8b83063d51e8b55555649aaa0dfeaaaaad07a023f87018a08700e07112aaaa8dd5552b32d52a945045552d4d552b163c7ab163c783060c1b32d29326839060d268f880e1c0183006030381c0e255555555554b140140c1d55032f550baa87d503060c1ad2c4d9906ff5060d268fa07555540c1d5552a0c783060c583060c983a0f4047f06030381c0e2030600c38555551baaaaaa96aaaa28aa5045a060eaaa8183060d58b1e3d58b1e3d555541bfd5555568123f830181c382807038895555555554aa5002ab32ab2acad03aa81d528385d543ea916aa8f060c183555555555506ff55a0f4047f43828030181c0e22555551baa6556aaaa5528a08aaaa9a5aa4e2c78f4e2c78f2e0c18f665a5060d06c9347c4070e01c38070181c0e0712aaaaaaaaaa58a00a060eaa8b97aa85d543ea8b83063d96968993665060d06ff49a3e89d555513275554a8f1e4c593163c783060e83d011fc380c0e0703881c384c03870e1c2aaaa8dd555554b55551415555532b2b2b2a4daaaa2e0c18f547a2d5555506ff5555562210380c50438070388855555555540c18306cccc837fa83069347d55555552a0c783060c583060c983888806030381c0e2030600c38152b2b2b2b5555283aaaa45aaa3c183060d555555541bfd5622110e0a00c06070388855555555545c1831ecccca0c1a0dfe9347d55555552a3c793164c58f1e0c18388880e030381c0e2070e01c3815555555551f1e7c7d5550f3e7c7c444070381c0e070395554ac7ab1f546cd9b363cd9b1f101c0e070381c0e45555555140103aa8bd542eaa1f54ac7ab1f35313aa1ead58fa0f4047f0e070381c0e072aaaaaaaaaaaa8a281d5fea0755503060c783160c183060c1831f540d064c1a0c183060c18f56ac78011fc00006070000000200603000181c00061700180c01e00b0098080155555555555400044103aabfd03aaa8b831e0c78f2e2c78f2e2c78faa9197060cb974b932e97263d3a71e0047f000000b81c0000080b85c0060300381c0006030007802c026020055555555555500011003a2e2d1d50b162c78b162e858f060c5ff060c58b060c1aba565c1832e2d164c5a2c58b162c58011fc00000000000e05c2e00301802c16000b298002c01601301002a8bc0e162e859fa163e162e3f1f800083e00c1d503460e8183060c5d0b060c583060c183062ffaba560d060c1a0c983060c18b162c58011fc00000000000e00c4e0003018000c2e00301802c1e00b05804c0400aa067e8183a070385c2e3f1f800083e0cd52a5d06b54a8f45aab1eac7b3fd55555550023f800081c0000000811001038005c00600f0058084c04400aa5665aaaa55000220 24 16777215 10 1023
def hc_65_11 : Nat → Nat := unpackHintV5 0x872ae6423b56a00e43ef77a3e77b5023879d85b34422d0c6376504d7b002a017929bab86d0a58bcdeaacc6493ed5e493c6e9432fad1e59cf8e28c1066de9a304cc895f38cca15b9044c2fb1f36ca8d5b9005c7b982252fb0d98e403d1bec120322000240 0x152ab32ab2acad40c1d55032f54a0e85d550bfe8b554583060c1aaaaaaaaaa837faac1e2a2a90e8a80c183062c58b16ab555554caad55554ab54aca83060c1a831e3d16aa8f060c18355555506ff5543a2a03060c18f1eaa6cda7d558183060c79b1eaa6cd93264c1c5e2e5c1c5da5469e938f462c78f4e2c78f2e0c18f6269326a4c1a83068349a4d1e8e91a30eec761d185c1832e3d3a71e4d49d51b3746cdd1781c3e371358dc6e065c1974e3d38f2e0c18f49a4d418341bfd268f264e271326a8f1e4c593163c783060cb83065c7a74e3c9a93261c984c3930d9b366cb83065c79b363c9a93264c9c4cd938d9b366cb97aa162c1d0307030740c18ba160d060d4183060c183649a8f1ea0c1a0d068345aba56dc3b71b876e03060c18b162c593527546cdd1b3740e070b85c4d6371b81970740ffd030750ba160c183160c583060c183060c5b24d41935060d068345bfd458b168ea858b060c183060c58b060c583060c183062cb83060c183060c1aa2c78b574ac18306030e0c060c183162c58b26a4c587160b0e2caa060e819ba070385c2e26b0b1742cdd1b8dc2c58b4748d1834e5d983465c58ba162d685a2e162c58b6269326a3c7a8f1e9349a2d168e91a30efc7e1d189d9b34e2c58b164d49d51b3746cdd1b8dc2e171358dc6e4ead38b162c58b162c5a4d269349a2dfea2c58b170b858b165c583160c58b5458f16ad5a74e2c58b164d498b0e2c161c586cd9b366cd9b362c58b164d498b162e166c5c6cd9b36d031742c183060d554b975a55060c58b060c1835555555555574ac183060c58b162db876e370edc55aa070385c2e3e7e8f9fa553f1f81970740ffd030752b2a8d5506aaa0d06a8341aa0d2e2e8583060c583160c183060c18316a2d5555555555545bfd5d2b060c180c3830183060d0e8a82c58b16ab540c1d033f40e0727d5585c2e553f1f858b54e8d9a3858b16aaa8c19a31180241701902c0e074403f1f88f82c5a287060cbc2c3ca9d1b3470b162c0555550e8d9870e1c3870e23119f83c7e3f23a462c5d0b162c58b16aa72e8c1b3068cbd0b162c58b9555555555551d234ecd9a7162c58b461c0e8c55aa3f1f85c2e3e7e8f9fa553f1f93ab4eacaaa0d52e2c58b162c58b16a2d555555545bfd5ab4e9d0e8a82c58b16aa7cd9f367cd9f369f556162c58b553e6cf9b0281830e0c380030180c1830757fa8183060c3832e0c183060c1d523aa0e1c38f0e2c387060c18f062c183060c183063ea83a1c98743870683260d060c183060c7ab563c8ff4150306030060c387006030381c0e072aaaaaaaaaaaaaaa8a0081d55fc1830e1cb97061c1830e1e8183060c180070181c3870f555070e1c787161c397063c18f1e5c58f1e5c58f1f541d0e4c3a1c397060cb974b932e97263d3a71e47fa0a8380c0e1c2e01c3870e01c0e07039555555555555555450003a2e0c1872e0c1870e2d1d50b161c3870e1c38b161c38ba61c3870e2c78b162e858f0e1c38b0e2c387060c5ff060c58b060c1aba561d0e4c3a1c397060cb8b4593168b162c58b1647fa0a8380c0e1c038700e070381caa0e1e839fa2f03858ba167e858f858b8fc7e20e000c1d503460c183060c3834e0c183060c3830e0e8183060c183060c183060c5d0b0e1c38b0e2c387060c583060c183062ffaba561d0e4c3a1c38341830683260c183062c58b1647fa0a81870060c0180c0e070381caa0e1e839fa067e8183a070385c2e3f1f8838032874380222ad507061cb87061c3aa5d06b541c3871e1c5870ea8f45aab1eac7b3fd5550e935555555548ff4152882870e01c0e07038895555554accb5554aa5005507061cb87061c3d5070e1c787161c3ab1eac7ad33fd4387264d0ea1c3a4d269347aaaa001c40e1c387265c983260c9931e3c98b262c78fa88ff415070381c0e0710387098070e1c3855555555554b555514282a03064c983061c383a2e9c58f1e9c58f1e9e8797060c7aaaaaaaaaaa85024070181c0e22473f51cfd551781c3e4f2a907000745c1830e5c1830e1d46aca8743aaa1d5549a9e87870e1c787161c397060c7aa3d16aaaaaaa837faaaaaa47fa0a8380c504380703889541c3d073f45e072b27d47c9e5520e5050301a0c1a83060e81b3163c7b3163c7aba1e0c18306a4c9a870ec9341a0d268f070500320180c0e0703886cdd1b375540e070f8dc4d620e000e8183060c183060c1aba1e1c3871e1c5870e0c18306c9350e4d438741bfd418349a3c1a3aa060c187061c183060c187060c18306a831e0c183160c183260c8ff415030181c0e07101830061c2a8387a0e6e81c0e1f1b89ac0c1d0337441c0740d1540183060c183060d5d0f060c183662c78f662c78f5555555555420060328140381c44aa0703999fa667e87d2e5520e00acaa35543aaa874383a060c183060c18306a0d5d0f0e1c38f0e2c38745aaa3c183060d55555555541bfd548ff4152870e0a200c060703889541c3d073f49f556070387d2e5520e5051301835060c3a0e8ba7163c7a7163c7a7a1e5c1831ea0c1a8706c9341a1d268f0f050072a0380c0e0703886cdd1b375545e070f8dc4d620e000e8b83061cb83061c3a7a1e1c3871e1c5870e5c1831ec9350e4d43875060d06ff49a3c9a3aa264c3870e1c387264c387261c3870ea8f1e4c593163c783060c8ff415070181c0e071038700e1c2a8387a0e6e8bc0e1f1b89ac4c9d1337441ca0a1637069cbb7069cbaba4e1d0e1d43871742c58b162d478f50e1d9269349a1d161e0a00e4070381c0e0710d9ba366eaa8dc6e170b89ac41c015d270e0c3970e0c3871742c3870e2c38b0e1c58b162d926a1c9a870e9349a2dfea2c58b47542c5870e1c3870e2c5870e2c3870e1c597160c583162d5163c591fe82a0e070381c0e2070e01c3855070f41cdd1b8dc2e17135858ba166e8838ae938ba162c58b168aa09cbb706dc1a72e1c38b161c3870eaaaaaaaaaa901c0e0703940a089547e3f0b85c7cfd1f3f4aa41c015d270e0c3970e0c38756551aaa1d5543a1d506a971742c3870e2c38b0e1c58b162d45aaaaaaaaaaaa8b7f91fe82a0e071438705100e07112a8387a0e7e8fc7e4faab0b85caa41c 25 33554431 10 1023
def hc_65_12 : Nat → Nat := unpackHintV5 0xe85d37df8a35d58e7fcbe66ac2ee3eba1a35affa88a64a6ca274f59dc12d9b60989890b494590e88b6e97ceef26f1776613f765ad59a53a9cb4db57d40176839d98f30de3f289a112012221c40f41739421045bd062a8705e012053c2900014f 0x2aa075545eaa85d550bfe2c58b1735313aa4e9c58b162e0f151549d38b162c5d555555555555550b162c1c5e2e5c1c3c7d0f1e2c5d0b160c1d0b062e160c583162d1d2346bb26ed464cb83065c58b162d1d23461dd8ec3a30b83065c58b162ea8f9fa3e7e8bc0e170b8fc7e3f1f8197065c58b85c2c58b1e2c58b162c58f060c5ff060c58b060c1ab565c1832e2d164c5a2c58b162c5ab565c1832e2c38b0587160b162c59f3e7cf97060cb8b162e167c5c2c78b162c59f3e7cf9f3e7cf83060e07034e0c183060c183162c58b060c583060c183062ffab560d060c1a0c983060c18b162c5ab560c38301830603060c18b162c59f3e7cf833e0e060c1c0c183062c58b167cf9f3e7cf9f3ecd03555060d419355abfd40d541975060d6a91d52a3d16a0c1831e0c583060c183060c7b3fd555541a4d5555556a9510e80c18301870603060c18f56ac7aad52b32d55555552ad53303aabfaa972ea0c1ad03555264d418355aaa951e8b52e0c7831e3cb8b1e3cb8b1e3d9feaaaaaaa5d26aaaab54a88742e0c1972e1cb85c39707a74e3d56a95996aaaaaaa956a92683a2ea9741a8b47542c5aaa8b16a2e9aa8b1e2c58ba163d5168b5060c5ff060c58b060c1b3fd55555555555574ad510e85c1832e2c38b0587160b162c5aad52b27d4bc0e162e859fa163e162e553f1f9268307540d1aaa834ea0c1aa83a06a8341a83060c5d0b545a2d4183160c183060c18bfecff5555555555555d2b5443a030e0c060c180c183062c58b16ab54ac9f5067e8183a070385c2e553f1f926d2a5d06aae87aa3d16a3c7b3fd5555555a5443a0f1eab54ac9f5a1f4ab55554ac7ab1ecff5a49a4d268f562f503a87d42ea27550f56ac79352751078aaaaaa96aaaaaaaaaaaaaaaa3e3cf8f55555555aaaa1e7cf8f55aaaa563d58f555555aa5ebd7af1ead58f55aaaaaa55aa5906aa97aa45aaa3ea958f563d55567faaaaa1d152a87ab563d556555aaaaaa956aa81d5fea0755503060c783160c183060c1831eb4cff5060c99341a83068341a4d1eaaa83064c98306a0c183060c1932e0c183060c183063c793164c58f1f55503060c061c180c183063d5ab1e4d49930e4c261c9955555555552d55555503aabfd03aaa8b831e0c78f2e2c78f2e2c78f5a67fa0d26a4c99326975264d268f54997265c183060c983264d54183060c9835264c9931e3c98b262c78faaaa465c1832e5c3970b872e0f4e9c7935264c39309872655555555554b55555503a2e2d1d50b162c78b162e858f060c5ff060c58b060c1ad33fd06935164d458b45a2d5265c997060c183260c993162c58b162c993162c9d3162c58b162c58b162c58ba95d2b2e0c197161c582c38b058b162c9a93261c984c3932a8bc0e162e859ba163e162e26b132744cdd1b8dc0c1d503460e8183060c5d0b060c583060c183062ffad33fd41835064d068345a2d5060c9a7060c183060c183060c993060c997060c183060c183162c78f162c58b162c58ba95d2b061c180c1830183060c58b162c9a93261c984c3932a819ba060e81c0e170b89ac4c9d133746e3752ba1e3c7ad33fd269349a3d5265c983260c9931e3c98b262c78faa878f26a4c98726130e4caa371b87c6e26b132744cdd1b8dca838bc5cb838b93a264d1d0f462c78f4e2c78f2e0c18f555555555554748d187763b0e8c2e0c1971e9d38f55aa467e919fa2f0387c8e5547238197065d56549a9c7a71e5c1831ea8f45aaaa0dfeaaaaa97060cbaa21d07a74e3d54d9b2e0c197564fa8f369c7aa9b362c78b0740c183060c183060e85ffa162ea060c183060d926a2c9a8b16837fa83068b458347540c183160c583060c183160d583060c1aa0c5831e0c183160c583060c983574ac587160b0e2c060c183162c58b26a4c18306030e0caa162e859ba070385c2e26b030740cdd1b8dd5554ad4d5550b160c183060c1d5503060c1ad29326ccb28345a2df877e3f0efcaa060c183162c58b26a4eaaaaaaaaaaa5aaaaa060eaa8197aaa175542ff83060c1ad2c4d9906ff5060d168ba07555540c1d5552a0c583060c583060c98383c545503060c18b162c5935260c183018706555555555554b55555503060c183a060d681a0e4743d18b1e3db8b1e3c183060d89a4c9a9326a4c9a0d069347a3a468c3bf1f874603060c18f6edc793527546cdd1b3740e070f8dc4d6371b8183060c78f060c18349a4d06ff5060d268f060e070306a831e0c183160c183260c183060c78f26a4c18306030e0c366cd9b060c1831e6cd8f26a4c1830703360e366cd9b060d6060c1a31edc7aaaa3004623001ba0404030381c782c440472384647c060d0156060e581830600b0e1c7a31edc7aaaaa871188c3870e1c388c46dc3873e8e0e1e91c8e461c183a060d5a060c1830723a1e0c183068c58f1edc58f1eaaaaaaaaaaa8e9183060c1a30e07460f6edc7aad50381c8cfd233f43e472aa391c2c78b56551aaa2d56aa8b4583a060c183060c18306a0e85ffa162ea5162d55458f060c183060d55555555541bfd555d2b161c582c38b10e8a80c183062c58b16ab542c5d0b3f49f556070385c2e553f1fa37878de1c78b26d52d2ad03060eaaaa68183060c58b55555555555555aa060c1830fbcde1c162c58b55aaaaaaaaaaa55aa 24 16777215 10 1023
def hc_65_13 : Nat → Nat := unpackHintV5 0x8ffde3da52db81a8b15563abef8d87ec371a8000dc 0x32e0e81ffa060ea5743c183063c18b060c183060c18fa0683260d060c183060c78fa060c180c3830183060c78faa060e819fa070387d55503ff55545eaa2e0c18fa87c2eaa8b83065e627343d3a71f545c1832f510781e9d38faaaaaaaaaaaaaaaa060c183aa162c58baa060c183162c58baa060c183aaaaaaaaaaaa81d5503ff42eaa878faa060c1839a989d503060c18f56ac7c1e2a2a8183060c7ab563eaaaaaaaaaaaaa8183aa07fc18307527a1e5c18f063c797163c797163c7d17060cb974b932e97263d3a71f45c1832e5c3970b872e0f4e9c7d51781c5cbd173f43e4f550b1e2d5d27160c597160c58ba17fe858ba858b162c58f574ac5a2c98b458b4e9c58b162d5d2b161c582c38b13a7162c58baa162e859fa3f1f85c2e3f1f8fc7eaaaa060c183aa060c183162c58baa060c183162c58baaaaaaaaaaaaaaa162c58baa2e5cb97162c58baa2e5cb97162c58baaaaaaaaaaa 21 2097151 9 511
def nh_65 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_65_13 (Nat.sub p 416)) (hc_65_12 (Nat.sub p 384)) (Nat.blt p 416)) (Bool.rec (hc_65_11 (Nat.sub p 352)) (hc_65_10 (Nat.sub p 320)) (Nat.blt p 352)) (Nat.blt p 384)) (Bool.rec (Bool.rec (hc_65_9 (Nat.sub p 288)) (hc_65_8 (Nat.sub p 256)) (Nat.blt p 288)) (hc_65_7 (Nat.sub p 224)) (Nat.blt p 256)) (Nat.blt p 320)) (Bool.rec (Bool.rec (Bool.rec (hc_65_6 (Nat.sub p 192)) (hc_65_5 (Nat.sub p 160)) (Nat.blt p 192)) (Bool.rec (hc_65_4 (Nat.sub p 128)) (hc_65_3 (Nat.sub p 96)) (Nat.blt p 128)) (Nat.blt p 160)) (Bool.rec (Bool.rec (hc_65_2 (Nat.sub p 64)) (hc_65_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_65_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 224)
def f_65 : Nat → Nat × Nat := unpackForestF 0xc5f00c5bd236c00c5700c5300b5fcfc6ccfc6000b57cec6e00b4f00b47cbc6fcbc63cbb4fcbb4700a5f00a5bc986cc986000a57c756fc7563c745fc745700a53c646e00a4fc3c6fc4a7cc3c67c3a6e00a4bc214bc2147bf562bf36fc014fc0143bfd70bf36700a47be26e00a43bd264bc56fbc26e00a3bbb468b956fb993bb9937b946200a37afc6fafc63afb4fafb47afa6fafa63b5464afa4fb4264afa4bb3568afa47b2264afa43b1264afa3bb0468afa370095fae954aa35fad934aa35bac956abe70ab96caa357aa934aa3530095ba947ca2a4fa827ca2a4ba7570a2a47a627ca2a43a393fa393ba3937a3933a286ca28600095798d6f98d6398c5f98c5798b6f98b639e95498b5f9d93498b5b9c6709c16c98b579b13498b539a13498b4b9915c98b47009539346e974649326f962549326b94c7c9487c9326793a54932630094f8a46f9197c8a467909648a36f8f9348a36b8e17c8e07c8a3678d1348a3638c1348a34b8b15c8a3478a16e0094b88a4b88a477dd627db6f86a4f86a43865707db67855687da6f84256836708326c7da6b81d708187c7da67806708026c7da637f26c7da3b7e4607da37009477c9647836f7b9347836b7a17c7a07c7836779134783637816e00943771647256f761647236f7513472363741347235b7316c723577216e0093b714686b56f6fa3b6fa376b4626ec686b26f6da5c6b2636ca5c6b25b6bc606b257009376a26461d6f6925461d6b67c7c67a7c61d6766a5461d6361c6f6457c645706427c61c676357e61c5f61c5761a6e0092f609645856f5f9545856b5e47c5e17c585675d154585635846f5ad7c5ad705a97c5846759d7e5845f584575816e0092b573684d56f563584d56b54c7c54b704d56753b584d5634d46f50d7c50d705125b50b704d4674fd7e4d45f4d4574dd694dd614d362009274c1643b56f4b1543b56b49c7c4997c3b567489543b5633b46f4657c465704617c3b4674557e3b45f3b4573c45f3c45b4236c422603c457411443c4533c35f3e46c3e4603ea4b3e2603c3573d46e3c34f3c3473b2343b16e009233824f382473814f38147381270085f0085b36c7c3124f35d703124734c7c3114f33d70311473225b3225331b70311270085730044008532bc6e2ec642ba6f2dc642b96f2c57e2c3582b9270084f2a8440084b28a47292452894723d6227d6823a6f26d682396f2535a2535824672243602392700847008430083b21c681756f1fa37202351f937174621ec681726f1dc60172571cc681716f1bc60171571ad781867f1934a193481857218350171271705a008371626410d6f1525410d6310a6e13a641096f1227e122541095f1126c109570082f0082b0d56f0d5630d16f0d15f0d157008270c146008230b16405d6f0a15405d630916405b6f0815405b5f0716c05b570624f0596e0081f0081b0256f025630236f0235f023570081701146008130003f 9 11
def ch_65 : Nat → Bool := dagCheckNodeV5 fullMask g_65 ep_65 5 31 bds_65 423 (dagTraceF fullMask rootStock 11 f_65) cur_65 nh_65
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV5 fullMask g_65 ep_65 5 31 423 bds_65 (dagTraceF fullMask rootStock 11 f_65) (cur_65 0) (nh_65 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_0 : treeBlockF 0 32 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_1 : treeBlockF 32 64 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_2 : treeBlockF 64 96 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_3 : treeBlockF 96 128 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_4 : treeBlockF 128 160 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_5 : treeBlockF 160 192 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_6 : treeBlockF 192 224 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_7 : treeBlockF 224 256 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_8 : treeBlockF 256 288 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_9 : treeBlockF 288 320 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_10 : treeBlockF 320 352 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_11 : treeBlockF 352 384 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_12 : treeBlockF 384 416 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_13 : treeBlockF 416 423 ch_65 = true := by decide +kernel
theorem nj_65_1 : ∀ i, 0 ≤ i → i < 64 → ch_65 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_65_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_65_1 h1 h2)
theorem nj_65_2 : ∀ i, 0 ≤ i → i < 96 → ch_65 i = true := block_join nj_65_1 (fun _ h1 h2 => treeBlockF_at nb_65_2 h1 h2)
theorem nj_65_3 : ∀ i, 0 ≤ i → i < 128 → ch_65 i = true := block_join nj_65_2 (fun _ h1 h2 => treeBlockF_at nb_65_3 h1 h2)
theorem nj_65_4 : ∀ i, 0 ≤ i → i < 160 → ch_65 i = true := block_join nj_65_3 (fun _ h1 h2 => treeBlockF_at nb_65_4 h1 h2)
theorem nj_65_5 : ∀ i, 0 ≤ i → i < 192 → ch_65 i = true := block_join nj_65_4 (fun _ h1 h2 => treeBlockF_at nb_65_5 h1 h2)
theorem nj_65_6 : ∀ i, 0 ≤ i → i < 224 → ch_65 i = true := block_join nj_65_5 (fun _ h1 h2 => treeBlockF_at nb_65_6 h1 h2)
theorem nj_65_7 : ∀ i, 0 ≤ i → i < 256 → ch_65 i = true := block_join nj_65_6 (fun _ h1 h2 => treeBlockF_at nb_65_7 h1 h2)
theorem nj_65_8 : ∀ i, 0 ≤ i → i < 288 → ch_65 i = true := block_join nj_65_7 (fun _ h1 h2 => treeBlockF_at nb_65_8 h1 h2)
theorem nj_65_9 : ∀ i, 0 ≤ i → i < 320 → ch_65 i = true := block_join nj_65_8 (fun _ h1 h2 => treeBlockF_at nb_65_9 h1 h2)
theorem nj_65_10 : ∀ i, 0 ≤ i → i < 352 → ch_65 i = true := block_join nj_65_9 (fun _ h1 h2 => treeBlockF_at nb_65_10 h1 h2)
theorem nj_65_11 : ∀ i, 0 ≤ i → i < 384 → ch_65 i = true := block_join nj_65_10 (fun _ h1 h2 => treeBlockF_at nb_65_11 h1 h2)
theorem nj_65_12 : ∀ i, 0 ≤ i → i < 416 → ch_65 i = true := block_join nj_65_11 (fun _ h1 h2 => treeBlockF_at nb_65_12 h1 h2)
theorem nj_65_13 : ∀ i, 0 ≤ i → i < 423 → ch_65 i = true := block_join nj_65_12 (fun _ h1 h2 => treeBlockF_at nb_65_13 h1 h2)
theorem nc_65 : ∀ i, 0 ≤ i → i < 423 → ch_65 i = true := nj_65_13
theorem lb_65 : LowerBin fullMask rootStock g_65 12 :=
  lowerDagV5 (kn_cons lb_63 (kn_cons lb_61 (kn_cons lb_27 (kn_cons lb_59 (kn_cons lb_64 (kn_cons lb_62 (kn_cons lb_58 (kn_cons lb_57 (kn_cons lb_60 (kn_cons lb_21 (kn_cons lb_42 (kn_cons lb_43 (kn_cons lb_31 (kn_cons lb_26 (kn_cons lb_22 (kn_cons lb_51 (kn_cons lb_52 (kn_cons lb_7 (kn_cons lb_34 (kn_cons lb_39 (kn_cons lb_33 (kn_cons lb_11 (kn_cons lb_37 (kn_cons lb_30 (kn_cons lb_40 (kn_cons lb_53 (kn_cons lb_35 (kn_cons lb_24 (kn_cons lb_50 (kn_cons lb_44 (kn_cons lb_54 (kn_cons lb_9 (kn_cons lb_46 (kn_cons lb_38 (kn_nil))))))))))))))))))))))))))))))))))) rc_65 nc_65 (by decide +kernel)

def wg : List Gate := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [5, 8]⟩, ⟨GateOp.and, [7, 11]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.and, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 4004030464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676776 * 2 ^ 32 + 4004030464)) (13 - 1) := by
  rw [show canon fullMask (4276676776 * 2 ^ 32 + 4004030464) = g_65 by decide]
  exact lb_65

end PEqualNP.Outside.L_meta_48721

theorem PEqualNP.Outside.L_meta_48721 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 4004030464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 4004030464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_48721.table2_from_lowerBin (4276676776 * 2 ^ 32 + 4004030464) 13 PEqualNP.Outside.L_meta_48721.root_lb PEqualNP.Outside.L_meta_48721.wg 18 rfl PEqualNP.Outside.L_meta_48721.wfits PEqualNP.Outside.L_meta_48721.weval

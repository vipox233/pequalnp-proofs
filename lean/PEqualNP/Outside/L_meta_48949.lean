import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48949

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

def m_0 : Nat := 0xcccc0000
def s_0 : List Nat := [0x44440000, 0xc0c0000, 0xcc0000]
def g_0 : Nat := 0x44c0000
def ep_0 : Nat := 0x480000000000000408000000000000000000000000000004400000
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

def m_1 : Nat := 0xf000f0000000000
def s_1 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_1 : Nat := 0x100070000000000
def ep_1 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
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

def m_2 : Nat := 0xf0f000000000000
def s_2 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_2 : Nat := 0x107000000000000
def ep_2 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_3 : Nat := 0x2200220022002200
def s_3 : List Nat := [0x200020002000200, 0x220000002200, 0x22002200]
def g_3 : Nat := 0x20002002200
def ep_3 : Nat := 0x200200000000200000020000000000000000000000002000200000000000000000000000000000000000000
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

def m_5 : Nat := 0xc0c0c0c00000000
def s_5 : List Nat := [0x404040400000000, 0xc000c00000000, 0xc0c00000000]
def g_5 : Nat := 0x4040c00000000
def ep_5 : Nat := 0x408000000000004000800000000000000000000000000000000000000000004040000000000
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

def m_6 : Nat := 0xaa00aa00000000
def s_6 : List Nat := [0x22002200000000, 0xa000a00000000, 0xaa00000000]
def g_6 : Nat := 0x2002a00000000
def ep_6 : Nat := 0x28000000000000000000000000000200080000000000020020000000000000000000000000
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

def m_7 : Nat := 0xa0a0a0a00000000
def s_7 : List Nat := [0x202020200000000, 0xa000a00000000, 0xa0a00000000]
def g_7 : Nat := 0x2020a00000000
def ep_7 : Nat := 0x208000000000002000800000000000000000000000000020200000000000000000000000000
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

def m_8 : Nat := 0x4444444400000000
def s_8 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_8 : Nat := 0x4044400000000
def ep_8 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_9 : Nat := 0xff0000000000
def s_9 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_9 : Nat := 0x170000000000
def ep_9 : Nat := 0x6000000000000001200000000000000140000000000
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

def m_10 : Nat := 0x2222222200000000
def s_10 : List Nat := [0x202020200000000, 0x22002200000000, 0x222200000000]
def g_10 : Nat := 0x2022200000000
def ep_10 : Nat := 0x220000000000002002000000000000202000000000000000000000000000000000000000000
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

def m_11 : Nat := 0xaaaa00000000
def s_11 : List Nat := [0x222200000000, 0xa0a00000000, 0xaa00000000]
def g_11 : Nat := 0x22a00000000
def ep_11 : Nat := 0x2800000000000002080000000000000220000000000000000000000000
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

def m_12 : Nat := 0xcc00cc00000000
def s_12 : List Nat := [0x44004400000000, 0xc000c00000000, 0xcc00000000]
def g_12 : Nat := 0x4004c00000000
def ep_12 : Nat := 0x48000000000000000000000000000400080000000000000000000000000004004000000000
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

def m_13 : Nat := 0xff000000000000
def s_13 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_13 : Nat := 0x17000000000000
def ep_13 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_14 : Nat := 0xff000000
def s_14 : List Nat := [0x55000000, 0x33000000, 0xf000000]
def g_14 : Nat := 0x17000000
def ep_14 : Nat := 0x600000000000000120000000000000014000000
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

def m_15 : Nat := 0xf0000000f000000
def s_15 : List Nat := [0x500000005000000, 0x300000003000000, 0xf000000]
def g_15 : Nat := 0x100000007000000
def ep_15 : Nat := 0x600000000000000000000000000000000000000000000000000000001000000020000000100000004000000
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

def m_16 : Nat := 0xf0f000000000
def s_16 : List Nat := [0x505000000000, 0x303000000000, 0xf000000000]
def g_16 : Nat := 0x107000000000
def ep_16 : Nat := 0x6000000000000000000000000000001020000000000000104000000000
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

def m_17 : Nat := 0x4444000044440000
def s_17 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_17 : Nat := 0x4000004440000
def ep_17 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
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

def m_18 : Nat := 0xa0a00000a0a0000
def s_18 : List Nat := [0x202000002020000, 0xa0000000a0000, 0xa0a0000]
def g_18 : Nat := 0x20000020a0000
def ep_18 : Nat := 0x208000000000000000000000002000000080000000000000000000000020000020000000000000000000000
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

def m_19 : Nat := 0xc0c00000c0c0000
def s_19 : List Nat := [0x404000004040000, 0xc0000000c0000, 0xc0c0000]
def g_19 : Nat := 0x40000040c0000
def ep_19 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000000
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

def m_20 : Nat := 0xcc000000cc0000
def s_20 : List Nat := [0x44000000440000, 0xc0000000c0000, 0xcc0000]
def g_20 : Nat := 0x40000004c0000
def ep_20 : Nat := 0x48000000000000000000000000000000000000000400000008000000000000000000000004000000400000
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

def m_21 : Nat := 0xcccc00000000
def s_21 : List Nat := [0x444400000000, 0xc0c00000000, 0xcc00000000]
def g_21 : Nat := 0x44c00000000
def ep_21 : Nat := 0x4800000000000004080000000000000000000000000000044000000000
def bds_21 : List (Nat × List Nat × Nat × Nat) := []
def cur_21 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_21 : Nat → Nat := fun _ => 0
def f_21 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_21 : Nat → Bool := dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 1 (dagTraceF m_21 s_21 3 f_21) cur_21 nh_21
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 1 bds_21 (dagTraceF m_21 s_21 3 f_21) (cur_21 0) (nh_21 0) s_21 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21 : treeBlockF 0 1 ch_21 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 1 → ch_21 i = true := fun _ h1 h2 => treeBlockF_at nb_21 h1 h2
theorem lb_21 : LowerBin m_21 s_21 g_21 4 :=
  lowerDagV5 (kn_nil) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xcccc
def s_22 : List Nat := [0x4444, 0xc0c, 0xcc]
def g_22 : Nat := 0x44c
def ep_22 : Nat := 0x48000000000000040800000000000000000000000000000440
def bds_22 : List (Nat × List Nat × Nat × Nat) := []
def cur_22 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_22 : Nat → Nat := fun _ => 0
def f_22 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_22 : Nat → Bool := dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 1 (dagTraceF m_22 s_22 3 f_22) cur_22 nh_22
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 1 bds_22 (dagTraceF m_22 s_22 3 f_22) (cur_22 0) (nh_22 0) s_22 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22 : treeBlockF 0 1 ch_22 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 1 → ch_22 i = true := fun _ h1 h2 => treeBlockF_at nb_22 h1 h2
theorem lb_22 : LowerBin m_22 s_22 g_22 4 :=
  lowerDagV5 (kn_nil) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0x30c030c030c030c0
def s_23 : List Nat := [0x1040104010401040, 0xc000c000c000c0, 0x30c0000030c0, 0x30c030c0]
def g_23 : Nat := 0x1000104010403040
def ep_23 : Nat := 0x40200000000040000020000000000000000000000000000000000000000000000000001000104010400040
def bds_23 : List (Nat × List Nat × Nat × Nat) := []
def cc_23_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a490320230c608c108a104207c4f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c50244438453c3d3c3930302c2c24253c2134183c143408100924ee3fda3bd637d233cd3fc93bb537a1339d2f952b89277d23783f743b60374c33482f402b342728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_23_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b09490909090747070707070707070545050505034292821202012101002 0xfd38f934f438f034e928e524e028dc24c64cc240bc4cb840b13cad34a818a41499389a3c903c8c3084188014 8 255 3 7 10 1023 16 65535
def cur_23 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_23_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_23_0 p) (Nat.blt p 32)
def hc_23_0 : Nat → Nat := unpackHintV5 0xb47533a905480a4050125952829404a024090ca8224009f08f807823919c80dc46833309904ace541290911c6902a50d400b0002 0x0 13 8191 5 31
def hc_23_1 : Nat → Nat := unpackHintV5 0xe41c83906c6d81b03606c0ccd81ad34ce7dcf09e03c0708ba9612c0580a10f51a4304510a010414c28032006 0x0 11 2047 4 15
def nh_23 : Nat → Nat := fun p => Bool.rec (Bool.rec (0) (hc_23_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_23_0 p) (Nat.blt p 32)
def f_23 : Nat → Nat × Nat := unpackForestF 0xf138f134f038f034063fdd28dd24dc28dc24063b06370633053f053bba4cba40b84cb8400537a53ca534a418a4140533052f9a3c052b8c3c8c300527801880140523043f043b664c6640654c65400437503c5034502c50240433042f453c042b393c393004272c2c2c240423213c2134041f143c1434041b041709240413000f 6 10
def ch_23 : Nat → Bool := dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 64 (dagTraceF m_23 s_23 5 f_23) cur_23 nh_23
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 64 bds_23 (dagTraceF m_23 s_23 5 f_23) (cur_23 0) (nh_23 0) s_23 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23_0 : treeBlockF 0 32 ch_23 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23_1 : treeBlockF 32 64 ch_23 = true := by decide +kernel
theorem nj_23_1 : ∀ i, 0 ≤ i → i < 64 → ch_23 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_23_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_23_1 h1 h2)
theorem nc_23 : ∀ i, 0 ≤ i → i < 64 → ch_23 i = true := nj_23_1
theorem lb_23 : LowerBin m_23 s_23 g_23 6 :=
  lowerDagV5 (kn_nil) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0x2828282828282828
def s_24 : List Nat := [0x808080808080808, 0x28002800280028, 0x282800002828, 0x28282828]
def g_24 : Nat := 0x2800082028
def ep_24 : Nat := 0x8200000000028000020200000002800080008000000000000000000000000000000000000000000000000
def bds_24 : List (Nat × List Nat × Nat × Nat) := []
def cur_24 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xb9710f 4 15 2 3 6 63 8 255
def nh_24 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_24 : Nat → Nat × Nat := unpackForestF 0x1e788f 1 6
def ch_24 : Nat → Bool := dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 3 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 3 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24 : treeBlockF 0 3 ch_24 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 3 → ch_24 i = true := fun _ h1 h2 => treeBlockF_at nb_24 h1 h2
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_nil) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0x3c003c003c003c00
def s_25 : List Nat := [0x1400140014001400, 0xc000c000c000c00, 0x3c0000003c00, 0x3c003c00]
def g_25 : Nat := 0x1000140014003400
def ep_25 : Nat := 0x400200000000400000020000000000000000000000000000000000000000000000000001000140014000400
def bds_25 : List (Nat × List Nat × Nat × Nat) := []
def cc_25_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a490320230c608c108a104207c4f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c50244438453c3d3c3930302c2c24253c2134183c143408100924ee3fda3bd637d233cd3fc93bb537a1339d2f952b89277d23783f743b60374c33482f402b342728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_25_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b09490909090747070707070707070545050505034292821202012101002 0xfd38f934f438f034e928e524e028dc24c64cc240bc4cb840b13cad34a818a41499389a3c903c8c3084188014 8 255 3 7 10 1023 16 65535
def cur_25 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_25_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_25_0 p) (Nat.blt p 32)
def hc_25_0 : Nat → Nat := unpackHintV5 0xb47533a905480a4050125952829404a024090ca8224009f08f807823919c80dc46833309904ace541290911c6902a50d400b0002 0x0 13 8191 5 31
def hc_25_1 : Nat → Nat := unpackHintV5 0xe41c83906c6d81b03606c0ccd81ad34ce7dcf09e03c0708ba9612c0580a10f51a4304510a010414c28032006 0x0 11 2047 4 15
def nh_25 : Nat → Nat := fun p => Bool.rec (Bool.rec (0) (hc_25_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_25_0 p) (Nat.blt p 32)
def f_25 : Nat → Nat × Nat := unpackForestF 0xf138f134f038f034063fdd28dd24dc28dc24063b06370633053f053bba4cba40b84cb8400537a53ca534a418a4140533052f9a3c052b8c3c8c300527801880140523043f043b664c6640654c65400437503c5034502c50240433042f453c042b393c393004272c2c2c240423213c2134041f143c1434041b041709240413000f 6 10
def ch_25 : Nat → Bool := dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 64 (dagTraceF m_25 s_25 5 f_25) cur_25 nh_25
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 64 bds_25 (dagTraceF m_25 s_25 5 f_25) (cur_25 0) (nh_25 0) s_25 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_0 : treeBlockF 0 32 ch_25 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_1 : treeBlockF 32 64 ch_25 = true := by decide +kernel
theorem nj_25_1 : ∀ i, 0 ≤ i → i < 64 → ch_25 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_25_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_25_1 h1 h2)
theorem nc_25 : ∀ i, 0 ≤ i → i < 64 → ch_25 i = true := nj_25_1
theorem lb_25 : LowerBin m_25 s_25 g_25 6 :=
  lowerDagV5 (kn_nil) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0xc0c03030c0c03030
def s_26 : List Nat := [0x4040101040401010, 0x303000003030, 0xc0003000c00030, 0xc0c03030]
def g_26 : Nat := 0x103000403030
def ep_26 : Nat := 0x40200000000000000000000000002000400000000000000000000000000000000000000000100000400000
def bds_26 : List (Nat × List Nat × Nat × Nat) := []
def cc_26_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682b1560ac148a80d009c3382704a2941282314418810861042084108210420748e81d03a0740c901c001 0x7a3876346c3c68345c305d44564c5244484c4444382039342a48264022381e30144c10440c3c0834f63fea3be637de33d93fd53bc137ad33a92fa52b91277d23703f643b603758334c2f402b3c273423301f2c1b18170413000f 11 2047 5 31 10 1023 16 65535
def cc_26_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0a2a0a092898881808080808080646060606044404040404040242020202004 0xfc38f834f028ec24e230e344d24cce40c84cc440bd3cb934b418b014a3489f40983c94308d4c894484188014 8 255 3 7 10 1023 16 65535
def cur_26 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_26_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_26_0 p) (Nat.blt p 32)
def hc_26_0 : Nat → Nat := unpackHintV5 0xfa27b13925c04dc2654aea160aa084e126090d28223f11b24b905252140f0c6c63601910c805c428314009084802020d180b0002 0x0 13 8191 5 31
def hc_26_1 : Nat → Nat := unpackHintV5 0xa624a4a4091847a93541814a104a322191008044001e10d8c6c03221900b885062230e187003041800a1038c1c00a20500188006 0x0 13 8191 5 31
def hc_26_2 : Nat → Nat := unpackHintV5 0x4 0x0 6 63 3 7
def nh_26 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_26_2 (Nat.sub p 64)) (hc_26_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_26_0 p) (Nat.blt p 32)
def f_26 : Nat → Nat × Nat := unpackForestF 0xf838f834063fec28ec24063b0637e3440633053f053bc64cc640c44cc4400537b13cb134b018b0140533052f052b97489740943c94300527814c814480188014052376387634043f683c6834043b04375d440433524c5244042f444c4444042b042739340423041f041b1e481e401e381e300417084c0844083c08340413000f 6 10
def ch_26 : Nat → Bool := dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 64 (dagTraceF m_26 s_26 5 f_26) cur_26 nh_26
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 64 bds_26 (dagTraceF m_26 s_26 5 f_26) (cur_26 0) (nh_26 0) s_26 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_0 : treeBlockF 0 32 ch_26 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_1 : treeBlockF 32 64 ch_26 = true := by decide +kernel
theorem nj_26_1 : ∀ i, 0 ≤ i → i < 64 → ch_26 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_26_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_26_1 h1 h2)
theorem nc_26 : ∀ i, 0 ≤ i → i < 64 → ch_26 i = true := nj_26_1
theorem lb_26 : LowerBin m_26 s_26 g_26 6 :=
  lowerDagV5 (kn_nil) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0xf0f00000f0f000
def s_27 : List Nat := [0x50500000505000, 0x30300000303000, 0xf0000000f000, 0xf0f000]
def g_27 : Nat := 0x10100000503000
def ep_27 : Nat := 0x40200000000000000000000000000000000000000000000000000000101000000030000010100000500000
def bds_27 : List (Nat × List Nat × Nat × Nat) := []
def cur_27 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x16588f 4 15 2 3 5 31 7 127
def nh_27 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_27 : Nat → Nat × Nat := unpackForestF 0x39c4f 1 5
def ch_27 : Nat → Bool := dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 3 (dagTraceF m_27 s_27 4 f_27) cur_27 nh_27
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 3 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) (nh_27 0) s_27 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27 : treeBlockF 0 3 ch_27 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 3 → ch_27 i = true := fun _ h1 h2 => treeBlockF_at nb_27 h1 h2
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV5 (kn_nil) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0xffff00000000
def s_28 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_28 : Nat := 0x177f00000000
def ep_28 : Nat := 0x6800000000000006080000000000001220000000000000144000000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9), (m_16, s_16, 4, g_16), (m_21, s_21, 4, g_21), (m_11, s_11, 4, g_11)]
def cc_28_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_28_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_28 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_28_1 (Nat.sub p 32)) (cc_28_0 p) (Nat.blt p 32)
def hc_28_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_28_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
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
  lowerDagV5 (kn_cons lb_9 (kn_cons lb_16 (kn_cons lb_21 (kn_cons lb_11 (kn_nil))))) rc_28 nc_28 (by decide +kernel)

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

def m_30 : Nat := 0xaa00aa00aa00aa
def s_30 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_30 : Nat := 0x2002a000a002a
def ep_30 : Nat := 0x800000000002800000020000000000000000000020008000a000800020020000000200000000000000000
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_30 : Nat → List (Nat × Nat) := fun _ => []
def nh_30 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 0 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) (nh_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 0 (dagTraceF m_30 s_30 4 f_30) cur_30 nh_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0xffff000000000000
def s_31 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_31 : Nat := 0x1117000000000000
def ep_31 : Nat := 0x6000000000000000600000000000011120000000000001114000000000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def nh_31 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) (nh_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 nh_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0xff00ff0000000000
def s_32 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_32 : Nat := 0x1100170000000000
def ep_32 : Nat := 0x600000000000000000000000000000006000000000011001200000000001100140000000000
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_32 : Nat → List (Nat × Nat) := fun _ => []
def nh_32 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 0 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) (nh_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 0 (dagTraceF m_32 s_32 4 f_32) cur_32 nh_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0xff00ff00000000
def s_33 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_33 : Nat := 0x17007f00000000
def ep_33 : Nat := 0x68000000000000000000000000000600080000000000120020000000000014004000000000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_13, s_13, 4, g_13), (m_12, s_12, 4, g_12), (m_6, s_6, 4, g_6)]
def cc_33_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_33_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_33 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_33_1 (Nat.sub p 32)) (cc_33_0 p) (Nat.blt p 32)
def hc_33_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_33_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_33 : Nat → Nat := fun p => Bool.rec (hc_33_1 (Nat.sub p 32)) (hc_33_0 p) (Nat.blt p 32)
def f_33 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_33 : Nat → Bool := dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 43 (dagTraceF m_33 s_33 6 f_33) cur_33 nh_33
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 43 bds_33 (dagTraceF m_33 s_33 6 f_33) (cur_33 0) (nh_33 0) s_33 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_0 : treeBlockF 0 32 ch_33 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_1 : treeBlockF 32 43 ch_33 = true := by decide +kernel
theorem nj_33_1 : ∀ i, 0 ≤ i → i < 43 → ch_33 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_33_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_33_1 h1 h2)
theorem nc_33 : ∀ i, 0 ≤ i → i < 43 → ch_33 i = true := nj_33_1
theorem lb_33 : LowerBin m_33 s_33 g_33 7 :=
  lowerDagV5 (kn_cons lb_4 (kn_cons lb_13 (kn_cons lb_12 (kn_cons lb_6 (kn_nil))))) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0xf0f0f0f000000000
def s_34 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_34 : Nat := 0x1010107000000000
def ep_34 : Nat := 0x60000000000000006000000000000000000000000010101020000000001010104000000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def nh_34 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) (nh_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 nh_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0xf0f0f0f00000000
def s_35 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_35 : Nat := 0x107070f00000000
def ep_35 : Nat := 0x608000000000006000800000000000000000000000001020200000000000104040000000000
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_2, s_2, 4, g_2), (m_5, s_5, 4, g_5), (m_7, s_7, 4, g_7)]
def cc_35_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_35_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_35 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_35_1 (Nat.sub p 32)) (cc_35_0 p) (Nat.blt p 32)
def hc_35_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_35_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_35 : Nat → Nat := fun p => Bool.rec (hc_35_1 (Nat.sub p 32)) (hc_35_0 p) (Nat.blt p 32)
def f_35 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
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
  lowerDagV5 (kn_cons lb_1 (kn_cons lb_2 (kn_cons lb_5 (kn_cons lb_7 (kn_nil))))) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0xcccccccc00000000
def s_36 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_36 : Nat := 0x4044c00000000
def ep_36 : Nat := 0x448000000000004004800000000000404080000000000000000000000000004044000000000
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12), (m_21, s_21, 4, g_21), (m_8, s_8, 4, g_8), (m_5, s_5, 4, g_5)]
def cc_36_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_36_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_36 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_36_1 (Nat.sub p 32)) (cc_36_0 p) (Nat.blt p 32)
def hc_36_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_36_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_36 : Nat → Nat := fun p => Bool.rec (hc_36_1 (Nat.sub p 32)) (hc_36_0 p) (Nat.blt p 32)
def f_36 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_36 : Nat → Bool := dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 43 (dagTraceF m_36 s_36 6 f_36) cur_36 nh_36
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 43 bds_36 (dagTraceF m_36 s_36 6 f_36) (cur_36 0) (nh_36 0) s_36 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_0 : treeBlockF 0 32 ch_36 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_1 : treeBlockF 32 43 ch_36 = true := by decide +kernel
theorem nj_36_1 : ∀ i, 0 ≤ i → i < 43 → ch_36 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_36_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_36_1 h1 h2)
theorem nc_36 : ∀ i, 0 ≤ i → i < 43 → ch_36 i = true := nj_36_1
theorem lb_36 : LowerBin m_36 s_36 g_36 7 :=
  lowerDagV5 (kn_cons lb_12 (kn_cons lb_21 (kn_cons lb_8 (kn_cons lb_5 (kn_nil))))) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0xcc00cc00cc00cc
def s_37 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_37 : Nat := 0x4004c004c004c
def ep_37 : Nat := 0x48000000000048000000000000000000000000000400080008000800000000000000000004004000400040
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def nh_37 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) (nh_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 nh_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0x3333333300000000
def s_38 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_38 : Nat := 0x1113133300000000
def ep_38 : Nat := 0x220000000000002002000000000000202000000000000000000000000001110100000000000
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def nh_38 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0x66666666
def s_39 : List Nat := [0x22222222, 0x6060606, 0x660066, 0x6666]
def g_39 : Nat := 0x6462666
def ep_39 : Nat := 0x20200000000000400040000000000602040000000000000000000000000000000000
def bds_39 : List (Nat × List Nat × Nat × Nat) := []
def cur_39 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_39 : Nat → Nat := unpackHintV5 0x2802 0x0 8 255 4 15
def f_39 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_39 : Nat → Bool := dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 1 (dagTraceF m_39 s_39 3 f_39) cur_39 nh_39
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 1 bds_39 (dagTraceF m_39 s_39 3 f_39) (cur_39 0) (nh_39 0) s_39 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39 : treeBlockF 0 1 ch_39 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 1 → ch_39 i = true := fun _ h1 h2 => treeBlockF_at nb_39 h1 h2
theorem lb_39 : LowerBin m_39 s_39 g_39 4 :=
  lowerDagV5 (kn_nil) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xaaaaaaaa00000000
def s_40 : List Nat := [0x2222222200000000, 0xa0a0a0a00000000, 0xaa00aa00000000, 0xaaaa00000000]
def g_40 : Nat := 0x2022a00000000
def ep_40 : Nat := 0x228000000000002002800000000000202080000000000020220000000000000000000000000
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_11, s_11, 4, g_11), (m_10, s_10, 4, g_10), (m_7, s_7, 4, g_7)]
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
  lowerDagV5 (kn_cons lb_6 (kn_cons lb_11 (kn_cons lb_10 (kn_cons lb_7 (kn_nil))))) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0x6666000066660000
def s_41 : List Nat := [0x2222000022220000, 0x606000006060000, 0x66000000660000, 0x66660000]
def g_41 : Nat := 0x6000006460000
def ep_41 : Nat := 0x640000000000000000000000006000000400000000600000602000000000000000000000000000000000000
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_17 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0x6600660066006600
def s_42 : List Nat := [0x2200220022002200, 0x600060006000600, 0x660000006600, 0x66006600]
def g_42 : Nat := 0x60006002600
def ep_42 : Nat := 0x600200000000600000020000000000000000000000006000600040000000000000000000000000000000000
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def nh_42 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) (nh_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 nh_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xcccc0000cccc0000
def s_43 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_43 : Nat := 0x40000044c0000
def ep_43 : Nat := 0x448000000000000000000000004000000480000000400000408000000000000000000000004000004400000
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 4, g_20), (m_0, s_0, 4, g_0), (m_17, s_17, 4, g_17), (m_19, s_19, 4, g_19)]
def cc_43_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_43_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_43 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_43_1 (Nat.sub p 32)) (cc_43_0 p) (Nat.blt p 32)
def hc_43_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_43_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_43 : Nat → Nat := fun p => Bool.rec (hc_43_1 (Nat.sub p 32)) (hc_43_0 p) (Nat.blt p 32)
def f_43 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_43 : Nat → Bool := dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 43 (dagTraceF m_43 s_43 6 f_43) cur_43 nh_43
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 43 bds_43 (dagTraceF m_43 s_43 6 f_43) (cur_43 0) (nh_43 0) s_43 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_0 : treeBlockF 0 32 ch_43 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_1 : treeBlockF 32 43 ch_43 = true := by decide +kernel
theorem nj_43_1 : ∀ i, 0 ≤ i → i < 43 → ch_43 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_43_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_43_1 h1 h2)
theorem nc_43 : ∀ i, 0 ≤ i → i < 43 → ch_43 i = true := nj_43_1
theorem lb_43 : LowerBin m_43 s_43 g_43 7 :=
  lowerDagV5 (kn_cons lb_20 (kn_cons lb_0 (kn_cons lb_17 (kn_cons lb_19 (kn_nil))))) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xaaaa0000aaaa0000
def s_44 : List Nat := [0x2222000022220000, 0xa0a00000a0a0000, 0xaa000000aa0000, 0xaaaa0000]
def g_44 : Nat := 0x20000020a0000
def ep_44 : Nat := 0x20800000000000000000000000200000008000000020000020a000000020000020000000000000000000000
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def nh_44 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) (nh_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 nh_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV5 (kn_cons lb_18 (kn_nil)) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0x5555000055550000
def s_45 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_45 : Nat := 0x1115000015550000
def ep_45 : Nat := 0x440000000000000000000000004000000400000000400000400000011100000100000000000000000000000
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def nh_45 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) (nh_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 nh_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV5 (kn_cons lb_17 (kn_nil)) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xaa00aa00aa00aa00
def s_46 : List Nat := [0x2200220022002200, 0xa000a000a000a00, 0xaa000000aa00, 0xaa00aa00]
def g_46 : Nat := 0x20002002200
def ep_46 : Nat := 0x200200000000200000020000000000000000000000002000200000000000200020022000000000000000000
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def nh_46 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) (nh_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 nh_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0xff000000ff00
def s_47 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_47 : Nat := 0x170000003700
def ep_47 : Nat := 0x200000000000000000000000000000000000000006000000040000001200000032000000140000000400
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def nh_47 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) (nh_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 nh_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0xf0f00000f0f0
def s_48 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_48 : Nat := 0x107000003070
def ep_48 : Nat := 0x200000000000000000000000006000000040000000000000000000001020000030200000104000000040
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def nh_48 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_cons lb_16 (kn_nil)) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xf0f00000f0f0000
def s_49 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_49 : Nat := 0x1070000070f0000
def ep_49 : Nat := 0x608000000000000000000000006000000080000000000000000000001020000020000000104000004000000
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_15, s_15, 4, g_15), (m_19, s_19, 4, g_19), (m_18, s_18, 4, g_18)]
def cc_49_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_49_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_49 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_49_1 (Nat.sub p 32)) (cc_49_0 p) (Nat.blt p 32)
def hc_49_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_49_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_49 : Nat → Nat := fun p => Bool.rec (hc_49_1 (Nat.sub p 32)) (hc_49_0 p) (Nat.blt p 32)
def f_49 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_49 : Nat → Bool := dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 43 (dagTraceF m_49 s_49 6 f_49) cur_49 nh_49
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 43 bds_49 (dagTraceF m_49 s_49 6 f_49) (cur_49 0) (nh_49 0) s_49 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_0 : treeBlockF 0 32 ch_49 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_1 : treeBlockF 32 43 ch_49 = true := by decide +kernel
theorem nj_49_1 : ∀ i, 0 ≤ i → i < 43 → ch_49 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_49_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_49_1 h1 h2)
theorem nc_49 : ∀ i, 0 ≤ i → i < 43 → ch_49 i = true := nj_49_1
theorem lb_49 : LowerBin m_49 s_49 g_49 7 :=
  lowerDagV5 (kn_cons lb_2 (kn_cons lb_15 (kn_cons lb_19 (kn_cons lb_18 (kn_nil))))) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0xaaaa0000aaaa
def s_50 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_50 : Nat := 0x22a0000222a
def ep_50 : Nat := 0x200000000000000000000000002800000008000002080000000800000220000022200000000000000000
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def nh_50 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) (nh_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 nh_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0x3300330033003300
def s_51 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_51 : Nat := 0x1100130013003300
def ep_51 : Nat := 0x200200000000200000020000000000000000000000002000200000000000000000000001100100010000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def nh_51 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 0 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) (nh_51 0) s_51 4 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 0 (dagTraceF m_51 s_51 4 f_51) cur_51 nh_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0xf000f000f000f00
def s_52 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_52 : Nat := 0x100070007000700
def ep_52 : Nat := 0x600000000000600000000000000000000000000000000000000000001000200020002000100040004000400
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def nh_52 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 0 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) (nh_52 0) s_52 4 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 0 (dagTraceF m_52 s_52 4 f_52) cur_52 nh_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0x5555555500000000
def s_53 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_53 : Nat := 0x1115155500000000
def ep_53 : Nat := 0x440000000000004004000000000000404000000000011101000000000000000000000000000
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def nh_53 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 0 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) (nh_53 0) s_53 4 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 0 (dagTraceF m_53 s_53 4 f_53) cur_53 nh_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0xff00ff00
def s_54 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_54 : Nat := 0x17003700
def ep_54 : Nat := 0x20000000000000000000000000000600040000000000120032000000000014000400
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def nh_54 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 0 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) (nh_54 0) s_54 4 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 0 (dagTraceF m_54 s_54 4 f_54) cur_54 nh_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_54 nc_54 (by decide +kernel)

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
def g_56 : Nat := 0x20a222a
def ep_56 : Nat := 0x2020000000000008000800000000020a000800000000020022200000000000000000
def bds_56 : List (Nat × List Nat × Nat × Nat) := []
def cur_56 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_56 : Nat → Nat := fun _ => 0
def f_56 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_56 : Nat → Bool := dagCheckNodeV5 m_56 g_56 ep_56 1 1 bds_56 1 (dagTraceF m_56 s_56 3 f_56) cur_56 nh_56
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 1 1 1 bds_56 (dagTraceF m_56 s_56 3 f_56) (cur_56 0) (nh_56 0) s_56 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56 : treeBlockF 0 1 ch_56 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 1 → ch_56 i = true := fun _ h1 h2 => treeBlockF_at nb_56 h1 h2
theorem lb_56 : LowerBin m_56 s_56 g_56 4 :=
  lowerDagV5 (kn_nil) rc_56 nc_56 (by decide +kernel)

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

def m_58 : Nat := 0xff000000ff000000
def s_58 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_58 : Nat := 0x1100000017000000
def ep_58 : Nat := 0x600000000000000000000000000000000000000000000000600000011000000120000001100000014000000
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_58 : Nat → List (Nat × Nat) := fun _ => []
def nh_58 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_58 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 1 1 0 bds_58 (dagTraceF m_58 s_58 4 f_58) (cur_58 0) (nh_58 0) s_58 4 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_58 g_58 ep_58 1 1 bds_58 0 (dagTraceF m_58 s_58 4 f_58) cur_58 nh_58 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_58 : LowerBin m_58 s_58 g_58 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_58 nc_58 (by decide +kernel)

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

def m_60 : Nat := 0x4444444444444444
def s_60 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_60 : Nat := 0x4044404440444
def ep_60 : Nat := 0x440000000000440000000000004004000400040000404000400040000000000000000000000000000000000
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_60 : Nat → List (Nat × Nat) := fun _ => []
def nh_60 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_60 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 1 1 0 bds_60 (dagTraceF m_60 s_60 4 f_60) (cur_60 0) (nh_60 0) s_60 4 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_60 g_60 ep_60 1 1 bds_60 0 (dagTraceF m_60 s_60 4 f_60) cur_60 nh_60 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_60 : LowerBin m_60 s_60 g_60 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0x2222222222222222
def s_61 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_61 : Nat := 0x2022202022222
def ep_61 : Nat := 0x200200000000220000020200002002000000000000202000202000000000000000000000000000000000000
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_61 : Nat → List (Nat × Nat) := fun _ => []
def nh_61 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_61 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 1 1 0 bds_61 (dagTraceF m_61 s_61 4 f_61) (cur_61 0) (nh_61 0) s_61 4 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_61 g_61 ep_61 1 1 bds_61 0 (dagTraceF m_61 s_61 4 f_61) cur_61 nh_61 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_61 : LowerBin m_61 s_61 g_61 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_61 nc_61 (by decide +kernel)

def m_62 : Nat := 0xa500a500a500a500
def s_62 : List Nat := [0x500050005000500, 0x2100210021002100, 0xa5000000a500, 0xa500a500]
def g_62 : Nat := 0x100050005002500
def ep_62 : Nat := 0x400200000000400000020000000000000000000000000000000000001000000000020000000000000000000
def bds_62 : List (Nat × List Nat × Nat × Nat) := []
def cc_62_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0x793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_62_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014 8 255 3 7 10 1023 16 65535
def cur_62 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_62_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_62_0 p) (Nat.blt p 32)
def hc_62_0 : Nat → Nat := unpackHintV5 0xfa27b13925c04dc2654aea160aa084d1a50d28090248023090c68604112080fc47833a11c08bd25a22b111246902a50d400b0002 0x0 13 8191 5 31
def hc_62_1 : Nat → Nat := unpackHintV5 0xa2351027893c09a24a1a501204900461218d0447e23649a08c845292140e145102230e187003041800a1038c1c00a20500188006 0x0 13 8191 5 31
def hc_62_2 : Nat → Nat := unpackHintV5 0x6 0x0 6 63 3 7
def nh_62 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_62_2 (Nat.sub p 64)) (hc_62_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_62_0 p) (Nat.blt p 32)
def f_62 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def ch_62 : Nat → Bool := dagCheckNodeV5 m_62 g_62 ep_62 1 1 bds_62 64 (dagTraceF m_62 s_62 5 f_62) cur_62 nh_62
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 m_62 g_62 ep_62 1 1 64 bds_62 (dagTraceF m_62 s_62 5 f_62) (cur_62 0) (nh_62 0) s_62 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_0 : treeBlockF 0 32 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_1 : treeBlockF 32 64 ch_62 = true := by decide +kernel
theorem nj_62_1 : ∀ i, 0 ≤ i → i < 64 → ch_62 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_62_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_62_1 h1 h2)
theorem nc_62 : ∀ i, 0 ≤ i → i < 64 → ch_62 i = true := nj_62_1
theorem lb_62 : LowerBin m_62 s_62 g_62 6 :=
  lowerDagV5 (kn_nil) rc_62 nc_62 (by decide +kernel)

def m_63 : Nat := 0xc0c0c0c0c0c0c0c
def s_63 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_63 : Nat := 0x4040c040c040c
def ep_63 : Nat := 0x408000000000408000000000004000800080008000000000000000000000000000000000004040004000400
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_63 : Nat → List (Nat × Nat) := fun _ => []
def nh_63 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_63 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV5 m_63 g_63 ep_63 1 1 0 bds_63 (dagTraceF m_63 s_63 4 f_63) (cur_63 0) (nh_63 0) s_63 4 = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_63 g_63 ep_63 1 1 bds_63 0 (dagTraceF m_63 s_63 4 f_63) cur_63 nh_63 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_63 : LowerBin m_63 s_63 g_63 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_63 nc_63 (by decide +kernel)

def m_64 : Nat := 0xa0a0a0a0a0a0a0a
def s_64 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_64 : Nat := 0x2020a020a020a
def ep_64 : Nat := 0x208000000000208000000000002000800080008000000000000000000020200020002000000000000000000
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_64 : Nat → List (Nat × Nat) := fun _ => []
def nh_64 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_64 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV5 m_64 g_64 ep_64 1 1 0 bds_64 (dagTraceF m_64 s_64 4 f_64) (cur_64 0) (nh_64 0) s_64 4 = true := by decide +kernel
theorem nc_64 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_64 g_64 ep_64 1 1 bds_64 0 (dagTraceF m_64 s_64 4 f_64) cur_64 nh_64 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_64 : LowerBin m_64 s_64 g_64 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_64 nc_64 (by decide +kernel)

def m_65 : Nat := 0xa050a050a050a050
def s_65 : List Nat := [0x50005000500050, 0x2010201020102010, 0xa0500000a050, 0xa050a050]
def g_65 : Nat := 0x10005000502050
def ep_65 : Nat := 0x40200000000040000020000000000000000000000000000000000000100000000020000000000000000000
def bds_65 : List (Nat × List Nat × Nat × Nat) := []
def cc_65_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0x793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_65_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014 8 255 3 7 10 1023 16 65535
def cur_65 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_65_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_65_0 p) (Nat.blt p 32)
def hc_65_0 : Nat → Nat := unpackHintV5 0xfa27b13925c04dc2654aea160aa084d1a50d28090248023090c68604112080fc47833a11c08bd25a22b111246902a50d400b0002 0x0 13 8191 5 31
def hc_65_1 : Nat → Nat := unpackHintV5 0xa2351027893c09a24a1a501204900461218d0447e23649a08c845292140e145102230e187003041800a1038c1c00a20500188006 0x0 13 8191 5 31
def hc_65_2 : Nat → Nat := unpackHintV5 0x6 0x0 6 63 3 7
def nh_65 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_65_2 (Nat.sub p 64)) (hc_65_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_65_0 p) (Nat.blt p 32)
def f_65 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def ch_65 : Nat → Bool := dagCheckNodeV5 m_65 g_65 ep_65 1 1 bds_65 64 (dagTraceF m_65 s_65 5 f_65) cur_65 nh_65
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV5 m_65 g_65 ep_65 1 1 64 bds_65 (dagTraceF m_65 s_65 5 f_65) (cur_65 0) (nh_65 0) s_65 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_0 : treeBlockF 0 32 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_1 : treeBlockF 32 64 ch_65 = true := by decide +kernel
theorem nj_65_1 : ∀ i, 0 ≤ i → i < 64 → ch_65 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_65_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_65_1 h1 h2)
theorem nc_65 : ∀ i, 0 ≤ i → i < 64 → ch_65 i = true := nj_65_1
theorem lb_65 : LowerBin m_65 s_65 g_65 6 :=
  lowerDagV5 (kn_nil) rc_65 nc_65 (by decide +kernel)

def m_66 : Nat := 0xf0f0f0f0f0f0f0f0
def s_66 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_66 : Nat := 0x1010107010503070
def ep_66 : Nat := 0x40200000000060000020200000006000400040000000000000000010101020100030201010104010500040
def bds_66 : List (Nat × List Nat × Nat × Nat) := [(m_34, s_34, 5, g_34), (m_48, s_48, 5, g_48), (m_57, s_57, 5, g_57), (m_55, s_55, 4, g_55), (m_29, s_29, 5, g_29), (m_65, s_65, 6, g_65), (m_26, s_26, 6, g_26), (m_59, s_59, 6, g_59), (m_23, s_23, 6, g_23), (m_16, s_16, 4, g_16), (m_4, s_4, 4, g_4), (m_27, s_27, 5, g_27)]
def cc_66_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xaceb0a0e80a0280a023588611805f17c1f07c1f06d1655816050940501224812040900400e207401 0x204bcfa525498a88c9d29cc9426e2f351493464c95a60ab24051102880143c0a249091474814a3c992cd495694a25a4d211c050c6925b4525ae90d4466bc2b560e2d0514af69f5b4ba5a3cad0e1486f23b70a5ae4ccd246504f1c23880fc106e001f 10 1023 4 15 11 2047 17 131071
def cc_66_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb8959090906d68535050502d282828050000 0x5cd6ad6b382497d20b64c6e8bd6c5d9128d84e592633c5da1aed417286bd3b4e8d28b4506606924598e28be92a248cb131 8 255 3 7 11 2047 17 131071
def cur_66 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_66_1 (Nat.sub p 32)) (cc_66_0 p) (Nat.blt p 32)
def hc_66_0 : Nat → Nat := unpackHintV5 0x7bd71e11c6cd71b0066a439a90065c91695c588395b0e550394d0e534014d00534014d00514410b7442c01011434978d20032050995e264008f1418178600015850275e001380000 0xbaa7971cba9793d3df830317a71c0d67533d5473cba2d4db4303279e759e2c79c314d3d67531d57a5d3db4303272d9e7679e9cfa944a959674cb2d35cf3d756000db08c313c39c030e7e0d4d0c270c0c0c20c5e9c300c3838b435b0c0c09c0c3062c39c30c25e0d6d0c30270c0c0c14d9c30c30839f434f030c0c09c8322ea5d534f59007c86c4 18 262143 7 127
def hc_66_1 : Nat → Nat := unpackHintV5 0xa902250549281a44068f021e8547a0015890548194c0653000b09c2a8189c0e1e0901c5c000700000 0x31c79c71c71e93d3cf0c0c1c7039c71c71c71cb8b8b50c0c1c71c71c79c7a1e1cb2c751d1cf3c70c0c709e71c71c79c71cb875d71e873d1d34c751c31c070c9e79ea71e74f0c8ba9e5e971e2e53537e0c0c9c74d03 18 262143 8 255
def nh_66 : Nat → Nat := fun p => Bool.rec (hc_66_1 (Nat.sub p 32)) (hc_66_0 p) (Nat.blt p 32)
def f_66 : Nat → Nat × Nat := unpackForestF 0x1824905a7d917ac8bb613905a5d4170168f335e99a74c0d0168714598a28c49181486fa5e7d29028edd29c094b622f3114982b4c15604999cd48e694725a39211e908f474794a3c991c05012465b492da28213c86ba435104238ad7856ac083f0a2d05148106e001f 6 11
def ch_66 : Nat → Bool := dagCheckNodeV5 m_66 g_66 ep_66 4 15 bds_66 49 (dagTraceF m_66 s_66 7 f_66) cur_66 nh_66
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV5 m_66 g_66 ep_66 4 15 49 bds_66 (dagTraceF m_66 s_66 7 f_66) (cur_66 0) (nh_66 0) s_66 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_0 : treeBlockF 0 32 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_1 : treeBlockF 32 49 ch_66 = true := by decide +kernel
theorem nj_66_1 : ∀ i, 0 ≤ i → i < 49 → ch_66 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_66_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_66_1 h1 h2)
theorem nc_66 : ∀ i, 0 ≤ i → i < 49 → ch_66 i = true := nj_66_1
theorem lb_66 : LowerBin m_66 s_66 g_66 8 :=
  lowerDagV5 (kn_cons lb_34 (kn_cons lb_48 (kn_cons lb_57 (kn_cons lb_55 (kn_cons lb_29 (kn_cons lb_65 (kn_cons lb_26 (kn_cons lb_59 (kn_cons lb_23 (kn_cons lb_16 (kn_cons lb_4 (kn_cons lb_27 (kn_nil))))))))))))) rc_66 nc_66 (by decide +kernel)

def m_67 : Nat := 0x3333333333333333
def s_67 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_67 : Nat := 0x1113133313133333
def ep_67 : Nat := 0x200200000000220000020200002002000000000000202000202000000000000000000001110100010100000
def bds_67 : List (Nat × List Nat × Nat × Nat) := [(m_38, s_38, 5, g_38)]
def cur_67 : Nat → List (Nat × Nat) := fun _ => []
def nh_67 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_67 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_67 : dagCheckRootsV5 m_67 g_67 ep_67 1 1 0 bds_67 (dagTraceF m_67 s_67 5 f_67) (cur_67 0) (nh_67 0) s_67 5 = true := by decide +kernel
theorem nc_67 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_67 g_67 ep_67 1 1 bds_67 0 (dagTraceF m_67 s_67 5 f_67) cur_67 nh_67 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_67 : LowerBin m_67 s_67 g_67 6 :=
  lowerDagV5 (kn_cons lb_38 (kn_nil)) rc_67 nc_67 (by decide +kernel)

def m_68 : Nat := 0xff00ff00ff00ff00
def s_68 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_68 : Nat := 0x1100170017003700
def ep_68 : Nat := 0x600200000000600000020000000000000000000000006000600040011001200120032001100140014000400
def bds_68 : List (Nat × List Nat × Nat × Nat) := [(m_58, s_58, 5, g_58), (m_54, s_54, 5, g_54), (m_47, s_47, 5, g_47), (m_32, s_32, 5, g_32), (m_51, s_51, 5, g_51), (m_52, s_52, 5, g_52), (m_46, s_46, 5, g_46), (m_25, s_25, 6, g_25), (m_62, s_62, 6, g_62), (m_3, s_3, 4, g_3)]
def cur_68 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x1f 2 3 1 1 5 31 6 63
def nh_68 : Nat → Nat := unpackHintV5 0x860000 0xfb3bd775bd673ce2222211a3468d1a324 16 65535 8 255
def f_68 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
def ch_68 : Nat → Bool := dagCheckNodeV5 m_68 g_68 ep_68 3 7 bds_68 1 (dagTraceF m_68 s_68 7 f_68) cur_68 nh_68
set_option maxHeartbeats 0 in
theorem rc_68 : dagCheckRootsV5 m_68 g_68 ep_68 3 7 1 bds_68 (dagTraceF m_68 s_68 7 f_68) (cur_68 0) (nh_68 0) s_68 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68 : treeBlockF 0 1 ch_68 = true := by decide +kernel
theorem nc_68 : ∀ i, 0 ≤ i → i < 1 → ch_68 i = true := fun _ h1 h2 => treeBlockF_at nb_68 h1 h2
theorem lb_68 : LowerBin m_68 s_68 g_68 8 :=
  lowerDagV5 (kn_cons lb_58 (kn_cons lb_54 (kn_cons lb_47 (kn_cons lb_32 (kn_cons lb_51 (kn_cons lb_52 (kn_cons lb_46 (kn_cons lb_25 (kn_cons lb_62 (kn_cons lb_3 (kn_nil))))))))))) rc_68 nc_68 (by decide +kernel)

def m_69 : Nat := 0xaaaaaaaaaaaaaaaa
def s_69 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_69 : Nat := 0x2022a020a222a
def ep_69 : Nat := 0x20820000000022800002020000200280008000800020208020a000800020220020022200000000000000000
def bds_69 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18), (m_40, s_40, 7, g_40), (m_30, s_30, 5, g_30), (m_3, s_3, 4, g_3), (m_46, s_46, 5, g_46), (m_50, s_50, 5, g_50), (m_56, s_56, 4, g_56), (m_24, s_24, 5, g_24), (m_10, s_10, 4, g_10), (m_11, s_11, 4, g_11)]
def cc_69_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xec1d83b0722e41c0780700e01c03616c0d816a663cc094328240c80847082103e27c0f81d1343680c841c001 0x3ad4070280d028160782a0d07d278f24b1b48e3290c60a70b84b14086260ac481197b5f2d6b652d5c95a99225e202bc220503d270695e096c00cd402da404c510849c0d148152f05453076a408d08080a51b4fa169736d1e61a1cba4f954971091dfd21bd23f78476ec8ddd519b814f6e296d851daca1b113f56276604dc40998712f0c2560649c04918001f 11 2047 5 31 11 2047 19 524287
def cc_69_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xa8291a42909ca25882208822088211841d44e912440f2348d034085200801c4430c4300c02100800 0x7d141e4507650205607e971ea4c64171d02468941b14f6a52d99476450eac58a914a6c509697e425b8295dca5370931ba4062131196c3e05171343c051115c3a0516460565b1095c541b0d8144e0b141344c0d0c814300511350469750a55 10 1023 4 15 11 2047 18 262143
def cc_69_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x9c4e2712390482251076ba198c86432174b855231107a3c1e0c6602914084401c8540400 0x2f460ba5b2e06cb44d2c834c2d7efb5bb6d5ec353ae57a625d949663255809462c50a2131f25c9e0929a3fa48ee82379c8ce64606c132556092971a85c8b142185c8b141a04c86d023c608d1422360841b1984c7c971e024 9 511 3 7 11 2047 18 262143
def cc_69_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xb8b8b8b1949089888180808080795c5851504948484848483a38382a0c080801 0x3e024fd14feb5ef694b895ff2093bc52e4d53a353e6d278a3f484cb7814dad474460ce1b32a5cc8093525fd296f3257c694f0134 8 255 3 7 11 2047 18 262143
def cc_69_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x821042083c5780f01bab34660b95702a4540a815028250098912220440790a5122240480901022004003c807 0x5025c9f4a13c57274a84e05c7e49f348ddd0afcc9370a24ed44fd849da59372f2672c939a4a7af94b4828e5a50da0a6af1494428a5850516284804c222b91c052489fc893b8f26f1a4cd9c17ae02b4204e5408e51ae49b518c6a11657228a83313f5b276824dca499c485c6529a7a516140c420147c47d0c4ee0c99b203f59076740dc9819c101f81026f6d3a1d273194f582967251c94a1c0024 11 2047 4 15 11 2047 19 524287
def cc_69_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x3440 0x28a2f5134e 3 7 1 1 11 2047 19 524287
def cur_69 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_69_5 (Nat.sub p 160)) (cc_69_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_69_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_69_2 (Nat.sub p 64)) (cc_69_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_69_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def hc_69_0 : Nat → Nat := unpackHintV5 0xb9c1973802e482db613b6c016b02ad20459b09b360166c02cb02d9105b180b4e94a4fcdc5649703aad34d158ce2b100512509ec393d80235464482289000f39e947a01aee0082dc001000000 0x3e2fe7d63fef00f8ffef000000000001ef007bc000000000003e00003000181000aa00aa0000a080c63183060030000154183870e018c6318c6318c00630063060c008fd054aa82aaaaaa2800155400010aa0154000000047c0000600000400aa00aa000221f19531c2ff7cf8ea82704b1d0c18aabffcb2063990000000aa832a1d5401554100b060050e808faaa0aaaaaa8a0043860000c0000006318c006a800043860000c0000008f83006000000c01540154000141055555555 19 524287 8 255
def hc_69_1 : Nat → Nat := unpackHintV5 0xdbc03650ad94036005d285b1e2cb3942725c9b41668059a00250189043de1604f295201c48000fd233a054d8103243ca02923c448f00214286e17114a43e070f8003707014c80005 0xfff1c37fc7f86033e2d402a80000000154015400006318c0000000154015403ffdbcfacfbf7b7ede0000fdede000000000000c000000200018000000007c0154100050055004ffc7031ffc58e183ffc392fbdfbee7d67c818e5ffd7fdfff8c14001ac018027fe00004386000abf 18 262143 8 255
def hc_69_2 : Nat → Nat := unpackHintV5 0xd1c173e09ce4171e1bc7803120cbbc8eb53a87a5dc25c5e12973055b8156e00578415e0053840fe503dc1cd42333c14c609294848c191f0407c001a44c69001386c2529040540010 0xfd7fe7d67c87e3bff163860800043860000aa200000007c0000006000302001540154010044000006318c00000001555400000021c30000055551ffcfac7e0b400000000000015554010f8c197e1fdf9f07f8603fa5f3e3d3eb11c3fb778e1fc819f86b3ebff82d3e3d 18 262143 8 255
def hc_69_3 : Nat → Nat := unpackHintV5 0x9e12e99f429910e9652c8bbaa8526979fb375e416c6985daec5b82257c3c57c0055923470e93fe72348b62f553215e0156bf141151221f11b07116050f6200ef070ea050ce1c02f9f0131c0130000013 0x7e631c31df1d43983074454b162ac31d0c75043051a0caa1d43aaa0be1400300282584102aa0aaaaaaa8a004386000318c60035400000000001c38617c001803000180000000000aa00aa00a080000005017ea8001554018000055040017c000000000154400401540018c18e18e18e802f8c6318c631d400c180030806301ac15505555555450fcc00f8b26002e1c30000555d0effc580030160b58c631ae18d70c603067c63018c62c018c58355555541551540018c630006000000a34006318c000006318c0019f0000000600000302001540154000141018000c1c386303e0002aa000c603060c70c6386318c63180c6358c600cf800c18aaaaaa82aa28000318c600000cf800030016000003020015401540100440197fff580fe2cffc217f59f4fffe2c07f4000180b000080018b0003e000002a800800aa807ff03077fe30 20 1048575 8 255
def hc_69_4 : Nat → Nat := unpackHintV5 0x9af5c94f608e46b82aba80d1d7f91471fda665ba60d58525e84d5504765f4710546c0546c004591345900446133db6b367743175029c7b1dcc01924a1860c18600186001810517c05177050f285000f2 0xc63180002a802a8000c631800000002a802a800d5000018c6318c6300000000000180000cf84000318c63000000000000004001554015403e0c6387f0058031833e00c6318c63060c73863863018004d60b0182aa0aaaaaa8a4386318e21c543bf555554318c63a887154aaaaaaaaaaaa31940c6318c60c1ac58aaa318c70efd0c70e1d4318306318c6318c63a18c6306b18aaaaaaaaaaaaa014c00000000aa00aa00318c60c6543aa8858b155557ff1c3fbf18e46318ea61d50c631d52aaaaaaaa8c631ad6b58c631d553552aaaaaaa8053000000002a802a800d57deef18c6395a6aa7deef18c63aaa1d1514318c755543bf554b8aa06318ea99555555555555518e086318c18358b157e37ff78c631c31c361c31cabde3546318c7437bc6318e863877e1c31d4318306318c6318c63a18c6306b18aaaaaaaaa8d555 20 1048575 8 255
def hc_69_5 : Nat → Nat := unpackHintV5 0x1d5ae65cf8b3e418d400063 0x33e0000c6318032000060000000000aa022000aa0021f01070e18002a833e03180318c6318c0638631c318c060003180d603062aa0aaaaaa8a5500000000002aaa8000000318c630000000055005500 18 262143 8 255
def nh_69 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (hc_69_5 (Nat.sub p 160)) (hc_69_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_69_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_69_2 (Nat.sub p 64)) (hc_69_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_69_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_69 : Nat → Nat × Nat := unpackForestF 0x169f44d3805a5ce25c9c4a13857270a84e05c0168f328de649b80b430149f2c9380525c4b5c896a31a4fe349dc804c8d26f1c0523499c4b50892b912542242e00a478049d024ee100c42014812670207e0409c002401486f714dedaf3e0247b4a4028fde41200a3b778a4028dc0519b8b5371692e4d51c51f8094f6f0280252db5a88094701286c697d8d2db3c60670d8c695d912e32024634a6024fd5dafb0134576b6b918170b62e06c576aeb24d1641a2bb53572bc024ecc62c18c524e47e9c8ed4426272374f0489c8ccc62826460314be93581252e18a5b428c08514116282136043680841b0c52b9d5603a4b87d140e9261dc503b28074090c52998a4c314806453cc8a59a2503228e6450cc42600937116be5c4d045ad954602a2d8541b045ab93134270584c0d045a988a5e214ba44d40852a8895e1249e2492c71a80e0501248e340a049218914e120962a0f0541a09043120562408c440a009330f49c024bc34af0092b0b6900914c22288424e046a40b148152f023420124e0405004918001f 8 11
def ch_69 : Nat → Bool := dagCheckNodeV5 m_69 g_69 ep_69 3 7 bds_69 164 (dagTraceF m_69 s_69 8 f_69) cur_69 nh_69
set_option maxHeartbeats 0 in
theorem rc_69 : dagCheckRootsV5 m_69 g_69 ep_69 3 7 164 bds_69 (dagTraceF m_69 s_69 8 f_69) (cur_69 0) (nh_69 0) s_69 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_0 : treeBlockF 0 32 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_1 : treeBlockF 32 64 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_2 : treeBlockF 64 96 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_3 : treeBlockF 96 128 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_4 : treeBlockF 128 160 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_5 : treeBlockF 160 164 ch_69 = true := by decide +kernel
theorem nj_69_1 : ∀ i, 0 ≤ i → i < 64 → ch_69 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_69_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_69_1 h1 h2)
theorem nj_69_2 : ∀ i, 0 ≤ i → i < 96 → ch_69 i = true := block_join nj_69_1 (fun _ h1 h2 => treeBlockF_at nb_69_2 h1 h2)
theorem nj_69_3 : ∀ i, 0 ≤ i → i < 128 → ch_69 i = true := block_join nj_69_2 (fun _ h1 h2 => treeBlockF_at nb_69_3 h1 h2)
theorem nj_69_4 : ∀ i, 0 ≤ i → i < 160 → ch_69 i = true := block_join nj_69_3 (fun _ h1 h2 => treeBlockF_at nb_69_4 h1 h2)
theorem nj_69_5 : ∀ i, 0 ≤ i → i < 164 → ch_69 i = true := block_join nj_69_4 (fun _ h1 h2 => treeBlockF_at nb_69_5 h1 h2)
theorem nc_69 : ∀ i, 0 ≤ i → i < 164 → ch_69 i = true := nj_69_5
theorem lb_69 : LowerBin m_69 s_69 g_69 9 :=
  lowerDagV5 (kn_cons lb_18 (kn_cons lb_40 (kn_cons lb_30 (kn_cons lb_3 (kn_cons lb_46 (kn_cons lb_50 (kn_cons lb_56 (kn_cons lb_24 (kn_cons lb_10 (kn_cons lb_11 (kn_nil))))))))))) rc_69 nc_69 (by decide +kernel)

def m_70 : Nat := 0xff00ff00ff00ff
def s_70 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_70 : Nat := 0x17007f005f007f
def ep_70 : Nat := 0x4800000000006800000020000000000000000000060008000a000800120020000000200014004000500040
def bds_70 : List (Nat × List Nat × Nat × Nat) := [(m_33, s_33, 7, g_33)]
def cur_70 : Nat → List (Nat × Nat) := fun _ => []
def nh_70 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_70 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_70 : dagCheckRootsV5 m_70 g_70 ep_70 1 1 0 bds_70 (dagTraceF m_70 s_70 7 f_70) (cur_70 0) (nh_70 0) s_70 7 = true := by decide +kernel
theorem nc_70 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_70 g_70 ep_70 1 1 bds_70 0 (dagTraceF m_70 s_70 7 f_70) cur_70 nh_70 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_70 : LowerBin m_70 s_70 g_70 8 :=
  lowerDagV5 (kn_cons lb_33 (kn_nil)) rc_70 nc_70 (by decide +kernel)

def m_71 : Nat := 0xffff0000ffff
def s_71 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_71 : Nat := 0x177f0000377f
def ep_71 : Nat := 0x200000000000000000000000006800000048000006080000040800001220000032200000144000000440
def bds_71 : List (Nat × List Nat × Nat × Nat) := [(m_28, s_28, 7, g_28)]
def cur_71 : Nat → List (Nat × Nat) := fun _ => []
def nh_71 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_71 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_71 : dagCheckRootsV5 m_71 g_71 ep_71 1 1 0 bds_71 (dagTraceF m_71 s_71 7 f_71) (cur_71 0) (nh_71 0) s_71 7 = true := by decide +kernel
theorem nc_71 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_71 g_71 ep_71 1 1 bds_71 0 (dagTraceF m_71 s_71 7 f_71) cur_71 nh_71 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_71 : LowerBin m_71 s_71 g_71 8 :=
  lowerDagV5 (kn_cons lb_28 (kn_nil)) rc_71 nc_71 (by decide +kernel)

def m_72 : Nat := 0x6666666666666666
def s_72 : List Nat := [0x2222222222222222, 0x606060606060606, 0x66006600660066, 0x666600006666, 0x66666666]
def g_72 : Nat := 0x6066606462666
def ep_72 : Nat := 0x640200000000660000020200006006000400040000606000602040000000000000000000000000000000000
def bds_72 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10), (m_41, s_41, 5, g_41), (m_17, s_17, 4, g_17), (m_29, s_29, 5, g_29), (m_39, s_39, 4, g_39), (m_42, s_42, 5, g_42), (m_3, s_3, 4, g_3), (m_8, s_8, 4, g_8)]
def cur_72 : Nat → List (Nat × Nat) := unpackCursorV5 0xa82a0a824690231759d0741c1701b15d1705c152541504c9304c11244110440e3380e0380b306801 0x38a6d945ca6b5495c289c25a249a936d22e6359a4d116440ad134a2697d2ada356469a8d191e0233b47688cb9354a6a34a3c8c64f49250e3a128ded37ba2ee37c26f249de24b041486e509c20b801f 10 1023 4 15 10 1023 15 32767
def nh_72 : Nat → Nat := unpackHintV5 0x90a9c86e9c8501e787c97691e75d0c6acb169e0e6891567d0c66e0f65f0f5b4ab58a2a53b4f491aa4672a421463869b3721435e142afaf2a10e2812026d1419dd018f0e17b1415e1d09ac40059500005 0xaf5ebd718c63aedebb79999ae15c060c59312022e5cb9718c632e5cb971a356bd2e05c0000002f7bdef7af72f72f7af71dc7758ef7bdc631ac63bdef7ba8d777dce1c5def7bdeedef5ee5ee5ef5ef5c775bdef75ac77bdee346addbde3871b97ae5e38def7bdc77bd77debdc785ef50c77bdeeb5bdef756ad5bddf78e1cb9cbdef7bdc2f7bdc6fbdef7b970078d6f18d56bd000078005c02e5cb972e5cb972e5cb817397bdef7b85ef7bdef7bd5cb804358e66640000020b805cb972e5cb972e5cb9702f7bdef7bdcbdc02f70f0ee5c2f7bdce75def7ba76e5c18302e1c3dcbd7b837def7bdef3b972f700bdc3c338ee5ee5ef7585ef7ba76e0f2f7039c38170f72f5ef7bdee0ef5eb97bdef72f700bdca19c673acbdef72f740bdcb841c3a205e2e57ae5cbd71ac75cb976e355a970b83058217 20 1048575 8 255
def f_72 : Nat → Nat × Nat := unpackForestF 0x1d343a2f14d0c6f993731a85379e953d1a72351349a8c149e123c0460892dd1da230441549aa53421b9b4a348c64f42138a4a1474251820b801f 5 10
def ch_72 : Nat → Bool := dagCheckNodeV5 m_72 g_72 ep_72 3 7 bds_72 31 (dagTraceF m_72 s_72 7 f_72) cur_72 nh_72
set_option maxHeartbeats 0 in
theorem rc_72 : dagCheckRootsV5 m_72 g_72 ep_72 3 7 31 bds_72 (dagTraceF m_72 s_72 7 f_72) (cur_72 0) (nh_72 0) s_72 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_72 : treeBlockF 0 31 ch_72 = true := by decide +kernel
theorem nc_72 : ∀ i, 0 ≤ i → i < 31 → ch_72 i = true := fun _ h1 h2 => treeBlockF_at nb_72 h1 h2
theorem lb_72 : LowerBin m_72 s_72 g_72 8 :=
  lowerDagV5 (kn_cons lb_10 (kn_cons lb_41 (kn_cons lb_17 (kn_cons lb_29 (kn_cons lb_39 (kn_cons lb_42 (kn_cons lb_3 (kn_cons lb_8 (kn_nil))))))))) rc_72 nc_72 (by decide +kernel)

def m_73 : Nat := 0xffffffff00000000
def s_73 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_73 : Nat := 0x1117177f00000000
def ep_73 : Nat := 0x668000000000006006800000000000606080000000011121220000000001114144000000000
def bds_73 : List (Nat × List Nat × Nat × Nat) := [(m_33, s_33, 7, g_33), (m_28, s_28, 7, g_28), (m_34, s_34, 5, g_34), (m_36, s_36, 7, g_36), (m_40, s_40, 7, g_40), (m_31, s_31, 5, g_31), (m_2, s_2, 4, g_2), (m_38, s_38, 5, g_38), (m_35, s_35, 7, g_35), (m_53, s_53, 5, g_53), (m_32, s_32, 5, g_32), (m_10, s_10, 4, g_10), (m_16, s_16, 4, g_16), (m_13, s_13, 4, g_13), (m_1, s_1, 4, g_1), (m_8, s_8, 4, g_8), (m_9, s_9, 4, g_9), (m_5, s_5, 4, g_5), (m_7, s_7, 4, g_7), (m_4, s_4, 4, g_4), (m_12, s_12, 4, g_12), (m_6, s_6, 4, g_6), (m_21, s_21, 4, g_21), (m_11, s_11, 4, g_11)]
def cc_73_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xc86f3bc2f0bc2c3ac692a4290a064490240902408c62188211751d0741c1701b16c1b060cbd06801 0x3448065180f96c1e0d8389706cae0d05c1968e3b15c611806044158da1d194522a858460f0d81815031aa0856a0eacc1b1982c3304457060d80b15c102a01844288ae4cd6c91a590232172642c1684c2b89056110941411c24230383e020652ad1e4525c5a3b86296fe4ed9491ae84b530766208c04098001f 10 1023 4 15 11 2047 19 524287
def cc_73_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xc9320c8320c8311c0700bc6b4ac2b0a85dd705c06c5b06c192641722b4a024490204711843304801 0x811b5cc657f155b046741b1b8546ed51dd6a73599c4666c1999c579515e425b8c92e12312e48a085a7c15de85678129a84768119902e0408979605e98111223c088786c540f18262428c971623a4c9686e581b5586c1c1954862281546845100f828324ed592b6638480d020469b0c930441b10c57304c0d920 10 1023 4 15 11 2047 18 262143
def cc_73_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc29aa4290a0680a02809c6709c1da705c06c5b06c192641722b4a02449020471184330481004001 0x3234bc692f1233b252ac04ac011af83e820caf02e2c08ab866ae48ee35bb696ed233b256ac05aac15aa83e780caa02e2208a8960a2d8221213e049d06c980b29362868c681623a48a786e9c1b6686c7219658627e155c045660b828229295a3a6638480d8208a9b0c930881b21c57304c1b844 10 1023 4 15 11 2047 18 262143
def cc_73_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xb86e0b46d0b42b2ac292735c0701b15d1705c1705c1615455050504401003c42d080200441000400 0x3ea60fad82282146047716cf0063f362f898bd96ef45b7c96cda597b962e65576145860c50821ce0642811d6513a46ddb1979c55d451b716cd65535b54df5ab6d66d919b5166cf15fb457ea56b9157e255b814ad251f4146c416ed04b840c50021cc0641011c215b0923 10 1023 4 15 11 2047 18 262143
def cc_73_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x9410a21041180300200388700b3158ab0560869082104028010016a2c0544a81501742c0580b01422805000a 0xa0d85f2329f4f9dd329a184c0219e064a41151500bd309bd866a61504c8b922990f92c32980b8a4228f9668a53a19460d599d54e71517648d60599714e58514a08ca0132704e434a8f92a52468552e4d2975485704b920a504212604c941390d6a3e5a8e95a295b8d4a5c1216416e30293c08490134908e2b4b8492a0d4a8951a213e754c96c4b480ce1c19160451c2385d6e125a8356a0956814f9c1326316d1833800644411 11 2047 4 15 10 1023 18 262143
def cc_73_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x909018100100 0x281617e4c69129774866c61520c68c294b085f640 8 255 4 15 10 1023 18 262143
def cur_73 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_73_5 (Nat.sub p 160)) (cc_73_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_73_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_73_2 (Nat.sub p 64)) (cc_73_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_73_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def hc_73_0 : Nat → Nat := unpackHintV5 0xe8403f2b8b795c01cae00e570071f863671478e729b568ed950b2bc0753e1008a5a5bc4475d7058eb8007440c3850e9b944ad563a5ab8023052d0b0686b6d135005983924a8cc847e641865c843bfc0010e00000 0xf063e0fc0b2e03a05a07060eaaaaaaa940000e2c587062c5835a55028000e0c18787c0e1f000000040785c0e172a0b000038b161c18b160e162c58b1e2cb8080b160007061c1870e1c3831e3c180000022aaaa80070e2c183162c593060c5c2c58b1e2e016a2c0e0c183064c1833e2c162c383161c1830e3c78f1e1c780003d0151680070e1c387162c3870e0c5831e2c78b100e2c39b260c19b260c1870e0c39b063c79b878f37070e1c38f0e0d98f0600000000000a000a8aaaaa000c183061c78f0e0c18306000000aa8aaa001c38b162cd870e0c18b170b162c78b805a8b039b061c1831e9c500e1cf8b058b0e0c187075eb81c183066c39306070e0c5831e3c78f063c0001e80a8b40038b0e0c183060c58b060c18f163c588070e4cd93261c383060c193060c5830e8c7871e3c9c3c7938183060c783000000000005550005455500070f1f0f83e8b0e0c1d50faa87d07a87d40ea1f55000000000002aaa8aa802800503063e0fa2e2707360c99b066c1d5550000002aaaaa0007264c3d5550000002aaaaa0007060eaaa8000001555550020f07a8dd50381d44eaa8258383061c787063c18000000aaaaaa8800070e2c387060c583063c5971e5c582007060c3970e0cb8300e00c2e2875069750 21 2097151 9 511
def hc_73_1 : Nat → Nat := unpackHintV5 0xd5f53616ccadbd7d69a22b4d00598076c284d5de1bab51d507a9a3766513e3e77e90b4c3999b456ca41b62715afe8a97b022b1c5e58703aae8a9096707e0352c3969470d45865a2be02158038958b400a5200002 0x140c18795a158ac07caaacaa2c3c1c3d5503a55613546c983066c983061c3830e6c1870eaaa1e9a070f80d9b0367c038071980c1e4aaaaaaaaaaa820c183075534230380c0644aaaaaa8307a8dd40eaa3e014b21cd8381c3d17a2d83c2da0e0e81d7ae87060c19b0e4c1a1c383a95a158ac07caaacaa2c3d038183aaa55613070e4cd93261c383060c1930750787c0c1aaa83a6846070264c099f00600c1e4aaaaaaaaaaa820c7c7c564c99f4587060c3c3e070f80f8007c00020e1cf9b3e6c387060cf933e4c1830005095555500040014383061e1f0387c01c0183cb92aaaaa5d55410e1e83830740d5560129706293266c9a0caf5d01882c99b260b060c383062013061c183060c1831f0f8000441830e0c1872e0c187061c183060c7a71e9c000f8aaa2d40098b164c98b161c3870e1cd87060c183064c1972e2033164c58327170e1eb8f0e9c7871e0d3830e1c801955000e1c387063d18387c3c78f2f43e1e2c5a71efe170808c59b161cdc5d38f060eb8f061d387063c18320065540038f661c183060e1f0f1e3cbd0f878b169c7bb85c208f063e9168b2e87060c3c3e070f83c7e071f8055555559547aaa1c58f0e0c58f070f163c78f1e5d5163d5500 21 2097151 9 511
def hc_73_2 : Nat → Nat := unpackHintV5 0x9594aa31d24830cb5e732871543d8f7af5a7cb16482b4f1d05208df3ed4a8d6d243458accd6203188e8c18252fb058b44542cd81caec252244b883a2b18743c5c62b0ea43c3a4020e800835a2308329c090be01308800026 0xe0c3830e1c38706bc78300e00000028003067c99f260c19f878f1e3cfc02d15555400400143830e0c3870e1c18f060703803078ad7543aaaaa82a83062d983063c5971e5c5ab0016a1c387ae3c383061c783060c1870e37138756ba0d543870e1d61e3e87c3c58b4e3dfc2e5e03d0615c0e0c0060c1834e3c7a7038756ba0d543870e1d61972e8c00da3368c58b668e59b162d060f003a7661c183060c01e3d5ae835147a2d5438f0eb0f1f0043e1e2c5a71f3e1720c183060c3870e1c183060c0e070180c1e0f0e1c3d7061c5870ea8b162c58b016a83060eb83062c183162c58b1602c387060c183060c18306830e1c387060c1830381c06030783d55555504387160c18b170b162c78b859f00162d4588e3707362d0e2c3aaa83060c1a0c1831e3cdc3c79b83870e1c183060c0d9b0367c0e070180c1e2aaaaaaaaaaa083060c1d5550360f50fa81aaad4430380c064410f0a5555555555541060c1830ebc787060c18300006000070e7cd9f361c382801f878f1e3cfc02d5515540040014183060c38f0e0c1830601c0603078aaab5d506aa821c38b461c3aa3c5971e5c5ab0016a0c18f5899b26836bd749831e97164cd932703061c183545a4c1c0e0703947a1f0f975541830e0c18701830e0c383060c1971e3e1f42f17975551697552744c9d070e1c387361c183060c19306a09759c4e064cf815c0ebc0006bc1c3c7c074baa0aa1c3870e0d1a306a2b3e001b566d5d2f572cdd25d471b839b3e2f02b80c03af0e10f1f00d2ea82a8756cc383060c1a8acf8004d593574bd5c7274974061f916c01c1830000aaaa09555400055954aaaa200014000583830e0e6aa80e071580c89555555060f40ea275547c029643c0e064e070b68383 22 4194303 9 511
def hc_73_3 : Nat → Nat := unpackHintV5 0x8328ae08a208058e9fcc257e8059ef8547ba81dea0257114b9ac8be6a1089a382663b299689325432f94c82253200148e1d51089940c1b4e60e924ca63fa4c8f6c3e34ac84b5ee62414b46b528125c3c4402b06fd04000df 0x63c2266c980caf5c260cb85c993364c9c0c187060c01e13070381c0e01e0022d165c060c383061d060c3830e0c183065c79787d0001f0b804e8993a0e1c3870e6c383060c183260c02e8f4797143830e0e2aa80000020f40ea2755048743a9d06cc00b0b5a03c0e064e071f28383a060c3c050001001e0e1eaa81d0123d1ea5e0fa9daa364c183364c1830e1c187360c3870000f45038bc00000000000a6c5a9b16a1d43acd0697600060c183aa8a00000083d46ea0754128d0e8341b3002c2d680e6c1c0e1e03c47c1e3e5070740ebd70383060cd87260c0e1c1d4050001001e81c0c1d550123d1ea5e0fa9d8387266c9930e1c183060c983a83c5e060c0001d1400000000000a343a9316a4c5a8350697600063e0f8b538b262c383061e1f0387c000000a2d5516aa8b000070e2c58b361c383062c58b260c1802800002c1c1830f1781c5e000000b80070f41c183a06001750ea0d2e5d80054eb070e0c1d71e0c3870e1c18f060c6e235ae8706aaa83060c1c3c7d0f878b168c7bb85cbc07a1c3815c061c3870e09c78f46035ae8706aaa83060c1c32e5d58013464d18b168d5c7262c5a1c1e0070e1c383468c1803d6ba1c7aa28f45aaa831e0e1e3e0087c3c58b4e3e9c2e438ce2703262d555060d060c187060c5830e1c3871e3c9c3c7938183060c0e070264c099f0180c1e2aaaaaaaaaaa087061c1d5076aa0eaab03a87d54070390c064410f0a5555555555541 22 4194303 9 511
def hc_73_4 : Nat → Nat := unpackHintV5 0xfcf863daec8ebed6baae26e9b087a321de80863872c8d6fd6b3413fc1e592e252aaf44aa97f299e4bda5e4d78c75920c92a79d4a9c23296724b57474156237d3352a43b490e932d2cd6bc8dd2c196d0449cdf0924a800124 0x3458203061c187060c1832e4c984c2600701800030018172e1349a28306030e1c387060c18300e000300003e00c18000306007e2e3cb8f3f01343a1d06834babc003ea7c5a9f160c5b1745a83169f10018f947a0c3e020c187061c183060c7931e131268b543a0d55506a8352e5c1260c1a0c3870e1c183060c0e070180c1e0f50eaa83555516a08b5060d55418355170b162c78b859f00162d4583060c187060c383060c183065cb93265c3870e1c183060c09801c0e030185c526a8743a0d069750060c1830e1c183060c1830e0ea0f078183a060e81d03a0381c09930267c06030b921d0ea4c5a93168341a5d900e0c3830e0781c5e00e0000010070e000c19f267c983060014121d0eb741a5d8014f8b53e2c3830e0c3a1e070f80e071580c1e4a1d5555564150e1d54183162c593060d556859f00162d60e0c3830e1c3d70e5e0e0e2e5e0e1cb83073381c1c381c0e00c2e40fc243a1d41a5d953ac803060c1c1eaf5540e83d03abd555550380e070180c88890e8741a0d999904e0c18307555507a0754070380c064411f0a43a1d068366585ad209ea060c183060c183060c183060c387a060e83d03a070380d9b0367c0e070180c2e4a6c5a9b168743a0d0697640183060c3c5e060380001800041c39f367cd870e00c180000504b743a0d069760053e2d4f8b060c1830f0f81a0e1581c06030792aa835555904387162c59b0e1d418355555a167c0058b58183060c3c5cbc0c183ae0cbc0c38791c1c1832f030601c06030b903b0943a0d0697654eb201c383075cb830e1c387065c1830ae070600003060c1c3c7d23919b368d7bb8dc0755a8d1e8f000060c060c187060c9830e1c387263c9c4c7938183060c000000000010e875262d498b41a0d2e8007061c1d5072aa0e00103a89d54000000000008743a9d06ccb0b5a000e0c3830e1c387063c78300000050ea2aaa800280003062c58b260c18b858b163c5c0000a2c3830e0c3870e1c1970605700380000003066d98306bcb972e5cd80743a1d41a5d0056ea6c387ae5c383061cb83060c1870e1c0ae03000e1c3870878fa4723264d9a37f13806ab55a3d1e0c183061c3870e0c183061c387ae0c39f0e1c03e4cb9300183075c1833e0c19f2e5cd870e0c183060c18343a1d06834babd3e934fa6c18301870e1c383060c1800000070e4c183264e263c98f2701343a1d06834babc01498b5262c3930e0000c1830603060cb8f37171e6e0e1c387060c183000000000005362d4d8b43a1d06834ba000c1830755540c83d46ea0600150000000000029d0e8341b32c2d6800183060c38f1e1c183060c0000015541a8aa0001c38b162cd870ea0002e162c58f17000028b060c1830e5c383060c180005700180070e4d1870e02f265cb972600d43a0d06974015ba93 22 4194303 9 511
def hc_73_5 : Nat → Nat := unpackHintV5 0x2820ecca1d5721221c641d130001d 0x30f803c1a2d5160c187061c183060cb93a264c9870e0c1932e3c383060c183060c9930985c126975060c183aa0f5503a0f503a81d40eaa0381c060322e5047c290e8741a0d8bb4b0b5a413833e45c1e00cbc03c 19 524287 9 511
def nh_73 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (hc_73_5 (Nat.sub p 160)) (hc_73_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_73_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_73_2 (Nat.sub p 64)) (hc_73_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_73_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_73 : Nat → Nat × Nat := unpackForestF 0x51929a30532c94e5928cf3619e27d3c06658a9cb151986c330986601f4c02e960a72c14405a3c924692253240a40525c635a8c4b51895a3094c6029014770ed2e1ca34393e870320252e01adc025a802b50055a009f4001901276eed89f5b03ba62772dcee5b5dcb63c018772c4cd15d98ad39c6d738aacc55d98ab3314a6aad4dc5b1aab3354666b6a8d459998a3b3146678aecc0640491af34b5e496bc8cd8491af0465e07cbc0b80425aa35b544b6a88cd50ad2a05a57246a8159501f2a02e0107696d8945b0259624b0dc961b52c362602c4b0c46515d252b1925b474cc6492d11362206c438ae648c4c82d1fc6d3f8aa6415cc82b1904a36ad4741b0dab31b466376a86c198c82399046338ae640b8041194a622f4c052588a4371486d290d8540f0a43101457276ac04d6c95b30134b224d8441b0862b812321e2d83c1b0622b8d25c1a2b83417065a38c230022640416852368a455020ae04158082505d6a0f0d8175982e33063540b0cc0411c0823044570207c0c1b00e2b8185403088040c804098001f 8 11
def ch_73 : Nat → Bool := dagCheckNodeV5 m_73 g_73 ep_73 5 31 bds_73 165 (dagTraceF m_73 s_73 9 f_73) cur_73 nh_73
set_option maxHeartbeats 0 in
theorem rc_73 : dagCheckRootsV5 m_73 g_73 ep_73 5 31 165 bds_73 (dagTraceF m_73 s_73 9 f_73) (cur_73 0) (nh_73 0) s_73 9 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_73_0 : treeBlockF 0 32 ch_73 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_73_1 : treeBlockF 32 64 ch_73 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_73_2 : treeBlockF 64 96 ch_73 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_73_3 : treeBlockF 96 128 ch_73 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_73_4 : treeBlockF 128 160 ch_73 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_73_5 : treeBlockF 160 165 ch_73 = true := by decide +kernel
theorem nj_73_1 : ∀ i, 0 ≤ i → i < 64 → ch_73 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_73_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_73_1 h1 h2)
theorem nj_73_2 : ∀ i, 0 ≤ i → i < 96 → ch_73 i = true := block_join nj_73_1 (fun _ h1 h2 => treeBlockF_at nb_73_2 h1 h2)
theorem nj_73_3 : ∀ i, 0 ≤ i → i < 128 → ch_73 i = true := block_join nj_73_2 (fun _ h1 h2 => treeBlockF_at nb_73_3 h1 h2)
theorem nj_73_4 : ∀ i, 0 ≤ i → i < 160 → ch_73 i = true := block_join nj_73_3 (fun _ h1 h2 => treeBlockF_at nb_73_4 h1 h2)
theorem nj_73_5 : ∀ i, 0 ≤ i → i < 165 → ch_73 i = true := block_join nj_73_4 (fun _ h1 h2 => treeBlockF_at nb_73_5 h1 h2)
theorem nc_73 : ∀ i, 0 ≤ i → i < 165 → ch_73 i = true := nj_73_5
theorem lb_73 : LowerBin m_73 s_73 g_73 10 :=
  lowerDagV5 (kn_cons lb_33 (kn_cons lb_28 (kn_cons lb_34 (kn_cons lb_36 (kn_cons lb_40 (kn_cons lb_31 (kn_cons lb_2 (kn_cons lb_38 (kn_cons lb_35 (kn_cons lb_53 (kn_cons lb_32 (kn_cons lb_10 (kn_cons lb_16 (kn_cons lb_13 (kn_cons lb_1 (kn_cons lb_8 (kn_cons lb_9 (kn_cons lb_5 (kn_cons lb_7 (kn_cons lb_4 (kn_cons lb_12 (kn_cons lb_6 (kn_cons lb_21 (kn_cons lb_11 (kn_nil))))))))))))))))))))))))) rc_73 nc_73 (by decide +kernel)

def g_74 : Nat := 0x1117177f175f377f
def ep_74 : Nat := 0x64820000000066800002020000600680048004800060608060a040811121220120032201114144014500440
def bds_74 : List (Nat × List Nat × Nat × Nat) := [(m_49, s_49, 7, g_49), (m_73, s_73, 10, g_73), (m_70, s_70, 8, g_70), (m_43, s_43, 7, g_43), (m_69, s_69, 9, g_69), (m_71, s_71, 8, g_71), (m_68, s_68, 8, g_68), (m_66, s_66, 8, g_66), (m_45, s_45, 5, g_45), (m_67, s_67, 6, g_67), (m_61, s_61, 5, g_61), (m_3, s_3, 4, g_3), (m_72, s_72, 8, g_72), (m_46, s_46, 5, g_46), (m_21, s_21, 4, g_21), (m_34, s_34, 5, g_34), (m_64, s_64, 5, g_64), (m_30, s_30, 5, g_30), (m_37, s_37, 5, g_37), (m_60, s_60, 5, g_60), (m_22, s_22, 4, g_22), (m_44, s_44, 5, g_44), (m_50, s_50, 5, g_50), (m_47, s_47, 5, g_47), (m_36, s_36, 7, g_36), (m_63, s_63, 5, g_63), (m_52, s_52, 5, g_52), (m_58, s_58, 5, g_58), (m_31, s_31, 5, g_31), (m_17, s_17, 4, g_17), (m_48, s_48, 5, g_48), (m_57, s_57, 5, g_57)]
def cc_74_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x8404202004ec57603a05d00e027003705b80d036803401886c406202e0d700b805812c01600a824a2a50128094046121080c0001 0xf56a0eb6b12d6711c6b10c5b0fa660e2560d1660b3800c3480b4710bc730ab720a3700946604b6a08b4807c760637a073480645b05a5604c6b0426609d670846b06c5b0536a03b5a0205b0185702966010149d45b984579735b963579534f9334b913478f34389a5b842578124f7c24b76a4771a436b23f66a3b612375aa335a15b519574994f4014b3c947391433213f2f13b1b937139330d92f0c92b03127009230003f 13 8191 6 63 11 2047 20 1048575
def cc_74_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x942509424188a20791775c1525412348111441104411044110441102605414041100220801104001 0x1e57c7adaddb677f9e9f47a75181ca7a9f59e6c6a9716a426b8a99e025b7095db13460051a17c64591781464955825b5e95d705b5a15d602f560ad50275208dab6b66d9d896650051327c3a999224444911046d 10 1023 4 15 11 2047 18 262143
def cc_74_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x85be9e2e970b65b0d164ab150a15028124743816cb0512814076381c08c4020100800800 0xc4daf0367be59aa27da49c6da48b08d2db4cae8c2c23caed12e23fb48eeca37ac8cea480a56028a5cbb1caac70a69fe82739cd5a225b7c95e636672d9a5266929723d7d8d1c21a5a895ea1b76849da0a5c 9 511 3 7 11 2047 18 262143
def cc_74_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xf0f0f0f0e9c5c0b9b8aaa8a18b88887a786a685a58584a48483a151009080100 0xf6953fb6bfc9afea67f88ffd233f04d3b17ce8593a255eedafab67e659b8a7fe09cf3366dc99b657dd496b5376d29db3e7acc9eb7d67da9af5a67d096f2a57c64d3097c 8 255 3 7 11 2047 18 262143
def cc_74_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x946509064090222846108060074d765c1525413248520481204451044110441013c4f03845901400 0x27d2a4ec7c9baed34d525d2a4bc6698aed2c992552a51466a06d73c9ae7133cca3f94467244d2300a4817c8b02914052180dc326683041064d2312dc5a578a2ad1216e202bc382f850570809e0811c8b6b8f6cf1c99a34b340814 10 1023 4 15 11 2047 19 524287
def cc_74_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x9dce2712390482412077add60a250281249044a21028040200d668341a0a61f050200200 0x2fd3e5e264b84a97b1b6f22ad3155baad5731aae23352967b72bf2c535eca2e056bbeacf7699ad92b52167942bef455ec9a4d5a3fb2af962df2bd3e56d70abafb54df2a5ab53a7ca64c94a95ace36d834bae4975891ea11fd22338e295368fe6119d0b54 9 511 3 7 11 2047 19 524287
def cc_74_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x9048232fc7c3c5e0e257aa142a04ca612290449b0d05a2c1609448240e870310a0400400 0xdd719c0dfb7dbe6f272dc2ffb51b762b554967e1ad7b759f65b36bb56a82cf3257df0abeaa54d34f9a31b73eb56a56bd2acfa099b392b63c78cc8b1951cb263863d69c66ad88d9b2eb5e4567c58d58716ae53260a54 9 511 3 7 11 2047 19 524287
def cc_74_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xbc2e1b82e0b0aa2829d3741d0741b26c1a1681a0608ea380c2300932408120080188240801100400 0x7f27c3513f219373493f2113780d677fc6b7ec677e45b7dc577d3667ca66571673414f201477ab693393f1f9377ae787a36c795703313f1c9377bd6a7b46779b6b78b677834b77b477726a561673293f1c13776244730247527c7426472824743557335b72b5775c6b74c6773a6672024713546e97d 10 1023 4 15 11 2047 20 1048575
def cc_74_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xc0f00bc6f0b86e0b82c2b02b1a49be64990605805c57058560581421b860180511404104c1004001 0x8fb668aa6b84a678ea548da448ce788c26c8b2443713f251378e45f8d45b8bc578ac53773568a2564f15f4895b3f1573b9533694f3114b241471a9433613f2393788c7c87b7c86d7085b7c853648946d8834f8734b8634784b437d24a4e14f4794b3e9473a9433593f3013b2293719933833548247c83c6682b6b81b6780244 10 1023 4 15 11 2047 20 1048575
def cc_74_9 : Nat → List (Nat × Nat) := unpackCursorV5 0x9249018c28c08448408217a47a07625515213ea3e03263202c32c02c02a116a141140140067060060003 0x70a3f6a23b65a37602339ba7d9a2710b9279bb7d9917d3893f299379aa449a4716f34e3814f281479927d6e23f9cb6f9c36394b4b923479b26f99a6380a4b7b2476da3f6923b642375f2339896f3793f279371292f099270912791c5697b5682a5f7fa5b79a5775a535015f3f9571192f0812796c6d9434a81a4f7ea4b78a4774a4395c668e26b882670792794d679446693b668d26b872677e25b78257581671092f069278ca6992d6a9246791b6a8ba6b862677da4b77a4790a6f9026385255 12 4095 5 31 11 2047 20 1048575
def cur_74 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_74_9 (Nat.sub p 288)) (cc_74_8 (Nat.sub p 256)) (Nat.blt p 288)) (cc_74_7 (Nat.sub p 224)) (Nat.blt p 256)) (Bool.rec (cc_74_6 (Nat.sub p 192)) (cc_74_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 224)) (Bool.rec (Bool.rec (Bool.rec (cc_74_4 (Nat.sub p 128)) (cc_74_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_74_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_74_1 (Nat.sub p 32)) (cc_74_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)
def hc_74_0 : Nat → Nat := unpackHintV5 0x831748fd4c71e1fc53971676e9a24d5a3c9aa507b4b64a68c454cb6b1181ea7ac4df8558988a274512a2d623bcc4432a2878f6b0e247d19a1542dcabc53c3e8924aa0f8d5e1afa102b45583d1cb8461a105c57e03044400030000000 0xc183060c1870e5c183060c183060c0e070180c0b9302e4e070781c0e878fa060e01e0c06030180c18030600090aaaaaaaa82aa281c3870e2c187703800300f935e4c993364cd93264c183060c0f003c1c3e1e00000aaaaa1c39f369c387060c183062c18070364c17930180e1f07a0a0640c7c0c1c03c180c070500306030600242aaaaaaaaa0aa8a07060c0380387c1e1f03807870e2c58b0e1c183162c583062c9800b160070580c060011de82a5555415555551400183060c183060c183060c00000002aaaaaaaa800000000000000155555554015400183060c0002aaa8000000008ee0007000060030000020055550055000110ee11dc9845e09d131f02fbf71f13200160c187061c18307dc2e555503a81d13027040c06503018aaaa0c1a0c0e070180eaaaa0a8183aaa060eab19300c64e8228180c06030028481830060c155550555555450183060c383061c183060c1f702e4c0981c0e0301d545e4f555507a83d40ea0740113aaaaaaaa82001830060c0180c060300281d011dd5555555505555554500060c393060010783d46e37523a1c0e060154001101dd55543830e0c0002a2a80280001836e6db9b060c00028000000000000001555401555554003830e0c0ee0070260000c193264c18300f507a83d55030000aa89d551389d55500555500000000000041001dd55540155555555540098700183060015178bd45e3f0783c0e060154001101dd5554183060c0002aaa000387b65ed970e1e80000002800000000000000155540155555400183060c0980077001870e4c9930e1c00075541ea075030000aa89d551389d55500555500000000000041001dd555401555555555400381dc061c3870e003aaaa060c18300264c9932e5c9bb764c99380000005555aaa060e060c187060cb830381c0d930364c0603aaaaaaaa82060301830060c0180c0084555555554155140e0c3830381c01d555541540c1974eec183764c00b93a08a0e1c0e2c06030021058b00e1c1555505555554503b81c1800c1830607aaa0e1c387a00264c993366c99f5e4c993800000055550e5c3d5503060c1c0c18302e4c0b930381c0603aaaaaaaa82060c0183006030180c008455555555415514060c18300e0301d555541070e6d39f0e1ea5e4c00d93a08a060301830183002101830060c1555505555554503830601c01d5507aaa0740113aaaa8200382c060300285d011dd555505555554500060c183060c183060c183060c000000002858ba0e1e0e3e0e1e070300000000000000055555555005500060c183000083c1e070300000000000e1c3f70e5c387060c183060c005aa0001c397060c183060c18300001e3d55400003870e1cb87060c183060c183060c18300000000a162e878b83c1e0703000000000000000e1c3870e1cb870e1fb83060c18306002d5000060c183000087c1e070300000000000e1c183060c005aa000c1830600010f83c0e06000000000047703800030018000002c015554015400014100e1c3870e1c3875555555555 23 8388607 9 511
def hc_74_1 : Nat → Nat := unpackHintV5 0xa6e8f4a69415a69400a5d031a171189ee0a498ad8d94c8f98fcd3f87f9f5835d277cb1ab78e8f273356d6cb1a167d1386089d25941d252bda14db94148296441dd933eecbc3a9117343996290acc2441321af653162d320cc65a0635a400018d 0x20f1783c1e060001376f555172e0c18306001eaa0777aa8bc3c000015555443970e1072e1e0591d060c18300000e1cb970e1c0183000000aaa200a000000000000000055550055555500483c0c0e07220180c2a1e0c183dd803c7800774151aaa0e0c1830740c000380110010003001800000000155555503bb8500043c000000000000003b802aaaaaaa8800802aa80207060c000380003000000387060c8001e00000000001dc01555440040154010183060c00028a0f030703060001400c183060c1830600001c38000000000000002aaa802aaaaa8003060c1800041eef41c3c0c1c0c180540c183060c1830600001c38700000003b80000001c00e0030018000f07811003c1e000f000055550055555500005040387000060c183060c183060c18300000000a000a2a075000000000000002aaaaaaa802a8050781d540c183060c00000002aaa83dde81d400000000000007700200088000e07003800300180040f0220015555555401540001410a000207540c183060000001555117bbd03a800000000000015555540154000060c183060c183060c183060c0000000025c5c797a58f0e1c3870e0c18306000000000000000aaaaaaaa00aa000c18306000107bbd070f0307030601503060c183060c18000070e1c00000000000003870e1c183060c007d0f1e3c7b31f1c78f00a0f03aa8183060c180000000555507bbd03a80000000000000028f55330e1c387060c18300aa00060c18300000e1c387060c183000000000000e1c3f70e5c387060c183060c019b366cc0003872e0c183060c1830600005c7978bc5c78000070e1c3970e0c183060c183060c18306000000005e2e3cbc5c7870e1c383060c1800000000000000070e1c3870e5c3870fdc183060c183008ece3b3000060c183000087c1e060e060c003871e3c7970e1c183060c183060c000078f1e00000000000001d9c70e0c18306014cfbd0f1f50003060c180005555000000000000766cc383060c18306014cfbd500041ea2f503a81d00005400010f8183060c0002a2f507a81d40c00002175540ea00a800000008160000001d9c70e0c183060c18050faaa67dc000183060c00021f0781c0c000000000003b3661c183060c0078faa67dc003871e3c7970e1c183060c183060c000078f1e0001503060c18000070e0c18306000000000001c383060c1800003060c18000070e0c18306000000000770003800030018000f02001555401540001410060c387060c183060c183060c183060d0608c982326070380c0740ca083c1e0703807d00380180c06030012155555555055450183060c383061c183060c1f702e4c11930381c0603a1e3e878f83c1e07038078b462c58b162c597169c58b162c3870e1c3870e1c183060c183060c59300162c0062c18b0060c0600c060301800477a0a95555555505555554503830e0c0000000387060d19b466c183000003c1e1f0300a000000000000000555500555555000e0c38303b801c0980003064c993460c180783c1e1f0300a1e3e878f0e1c3870e1c387060c58b160c180000b262c98b162c58b262c58b162c0000000000003b9010aaaa00aaaaaaaaaa000c1830600001c3a32e8cb870e0000c1800043e0e03818050000000000000002aaa802aaaaa8003060c1813000ee0030e1c993268c3870001c3e0f03818050f1f43c7870e2c58b461c383060c183060c180000b262c98b162c58b262c58b162c0000000000003b9010aaaa00aaaaaaaaaa000c1870e0c183060c183061c1832e0c0e070364c0d930180e0f07a060e818381c0e01e0c06030600c18030180090aaaaaaaa82aa281c587460c1974e0c187061c18172608c981c0e2301d050720e3e0e1e1f03807878280387038b0180c004855555555415514 24 16777215 10 1023
def hc_74_2 : Nat → Nat := unpackHintV5 0xc7245704cbec0e82703a00c0a026fe024bf8002fe000bd8102ceb3bb2f85ac403fafb0aabce0facc13e765e693452a243477dbda9cb15f6b03e182f4951ff612c0df4184c0d5b832bdcc89b89f1fb39858b31071f88000e3 0xc1830600001c383060c180000001dc00000e0000c0060003c0800555500550040110060c3830e1c18307dc00001800c000b9787c3c00001555447c3e098f8591d1e1c1830e4c816c7061c180c18000003060000c1800000070e1c383060c18043e1e0000000000000aaaa00aaaaaa0080f01f0fee1704645e87f7ee3e264002fb81770b83cbc3e01e4cee0b060c1830e0c187060c18307dc002e27000003801c00600300000000022e3cbc3c3870e1c183060c8001e000000000000001dc0155555554400401540100001830183061c1832e0c000000003870e1cdc6c79b8d8f060c18300000000000000555555550055000e0c38300000001832e9db830600001c3870e0c180179b8f6f171e0000000000000aaaa00aaaaaa0081cb870000060c1830e0fb80c18306000000005e2e3cbc5c7870e1c383060c1800000000000002aaaaaaa802a80030e0c18306000001c39b4e7c3870000003a3461c183060c00dc8c7a38d8f0000000000000555500555555000740c1871e0c0e0700d86c086430186c060300083c0c7838078000077554110e0c38300000a00060dd9b766c1830000839070f0f1f3b06000001c38000000000002aaa802aaaaa8007061c1801c00e02300180000107bbd070f0f1f032000780540c18f1e3c18301e000003c78000070e1c000000003b8000002aaa8800802aaaaa802030e0c1830f4070380fc7e01b0d80c360301800555410000077554110e0c383000000e1c00183466d19b060c0002a20f48ea00a00000000000000055550055555500a0f5540c3830e0c0088008003801c0460030000000002aaa83ddeaa2002000000000000000ee00aaaaaaaa200200aa008000c18306001c383bbc0cbd0f878f1e1c3870f4005c7971e3c7b71edc78f1e0c1800002aaaa8c1e06444230381c0603087870f43c078007754111e1e0703060c02e1700b87c0e070180c00207031e1e01e00001dd55044183060c00003877e5df970e1c280000021f07881800000306000000000000aaaa00aaaaaa0080c183060001c0060030000021e3e0f03bbd0306140003c780070e3c78f0e1ea01e000003c7800003060c000000003b8000002aaa8800802aaaaaa802030740c18306070b81c0e0301805c3e0170b800055541000007755411 22 4194303 9 511
def hc_74_3 : Nat → Nat := unpackHintV5 0xa33ed89ac21f93bdc18ecd3c84ae887e25a27961317195f36d950066bdb662850e5c8d7e58391557204655d0544dca024a40e242d5db3fb0c939998637608e33d8e22c5ddf2928cd26e0922085971c790317c52d102de60bb51e05719100015c 0x30e0c1830e0c183060c18007038031600c180c0707bbd070f40c5d03070307030700fa8183060c183162c183162c183060c183060c183060c793001e3c3870e0c060c380c183060c0067700064030600c182aaaaaaaa0aaaaaa8a507a062eaaaa8183061c183061c18381d540c183060c00a08981c0e00c5803060301d55507bbd555503aa0a061400c060c380c183060c006770088555555555555415514061c183062c183060c18300000000020f56ba81c0eaa070baa81d40e82aaaaaaaa03b8100002c01803003b800000002aaaaaaa802aaaaa8007366c383060c18b060c5800000000010f83c040c580c180000b016001dc0600002aaaaaa802a80030e0c183160c183060c180000000010f83d031740c1c0e06400770e1c78f1e8c387060c183060c58b060c58b060c183060c183060c1831e0c1840000b00600c00ee00000000b0582aaaaaaa802aaaaa80030e0c183160c183060c18001c018b0060c06030e1c1c0c5838183060c18300603062c060c183060033b8003018aaaaaaaa82aa280c183060001450781c0c000280183060c183060c000038700000000000000055550055555500060c183000083dde83878183818300a8183060c183060c00003870e0000033b8000000001c00e003000001e0f02200783c001e0000aaaa00aaaaaa00802201c380055503060c18306000000014001455400000000000000aaaaaaaa00aa0141e075503060c18300000000aaaa0f77a07500102c0000000006770000200088000e0700380030000081e044002aaaaaaa802a8020088500015503060c1830000000aaa88bdde81d4004001dc0000180000aaaaaaa00aa008003060c183060c183060c183060000000012e2e3cbd2c7870e1c387060c183000000000000600002aaaaaaaa802a80203060c18000070e0c18306000000033b800001c0001800000f020015554015401004407f70582c1645e1677ee0b058f2f130580b1677060c1830e0c187060c18307dc0000000000160b000582c00e007001800c08b8f2f0f0e1c387060c183002000582c16000000000770000015555555400400554001d03061c783000381c0160b00582c0603083c0c783805800770055410e0c3830000003801c016003020f77a0e1e1e3e06004000ba81831e3c78306000002c5800000b161c387000003b8000000000aaaa002002aaaaaa000c383060c3d0001c0e00b05802c16030185554100077005541a0f5540c3830e0c00000000008800816007003802c0060555507bbd54004004000000000770000015555555400400554020f03220381c0603087870f42c05877005411e1e0703060c000160b00582c0e070180c207031e1e016001dc015504183060c0000016007001800c0878f83c0eef40c18010002c3871e3c7870f5000000b16000002c583060c00000ee0000000002aaa800800aaaaaaa80030740c18306000070380c0600b05802c16155504001dc0155060f030381c8806030a8783062c05c07700415aaa0e0c1830740c00000000016007002200205800c006055555540eee0040040040b00000003b800000aaaaaaaa002002aaa001c1830000005801c01600300387060c0080016000007700000155540040055400183060c000220f038180005003060c183060c18000070e000000000000000aaaa00aaaaaa000c18306000107bbd070f0307030601503060c183060c18000070e1c00000ee0000000007003800c0060003c0801e0f000780002aaa802aaaaa8020088070e0000c183060c183060c18306000000014001455400000000000000aaaaaaaa00aa0141e075503060c18300000000aaaa0f77a075000000000001dc0000800220003801c00600300080800555555550055004011000183060c183060c183060c000000001bc5c7979b8f0e1c387060c183000000000000000555555550055004 24 16777215 10 1023
def hc_74_4 : Nat → Nat := unpackHintV5 0xa82edea2d9559a262d96e0d19281188b81c086614885304c80cd197bd13f71ea7a6ba5916695445ed1f15a651b53f59c4f392f49b1624331a03e55373a09133351ae2c21cc25a1a023e0701f252f1a313d1708ca11556d0e84b40a2119000288 0xc183060c383060c38306001c0e03018032600c1c1eef41c3c0c1c0c1d03063c7c0e8183807d40c183060c183060c183060c18f1e0c18f060c1831e4c0078f0e1c383018033b830600c18300064030600c182aaaaaaaa0aaaaaa8aa03061c383060c183060c1d45001c0e08c9823260301d355555541030180c1850203002215555555505545283c0eaa060c1830740eaaaa8183061c183061c1830028226070380c0600c98030755541eef40eaa81c3eaaa0a818b0a20060300677060c0183060110aaaaaaaaaaaa82aa2a80c18300183009f4fa8bc5ea0f0781c0e2aa0ee400000300555510e1df977e5c387060c183a00000000000aa000a8a00000000000000555555550055004060c183061c183060c1800000000107aa1d40ea0750381d540eaa0aaaaaa070faaa03b81000007701800c000000005555555500555555004060c1800c18043e1f01de78f9e3c78f2e3cb8f1e3c3870e1c38f2e1c183060c18f0640000030055551060cf873e1c078f00510e7cd87060c183060f183000000087c1e02063c060c00000000600002aaaaaa802a802070f4cbd32e1c383060c18306000000000010f83d00040c0600000000000c0000555555550055004060c183061c183060c180000000010f83c0e0740c18f1f03a060c800ee1c38f1e3e1870e0c183060c183063c183060c183060c78f060c783060c18400001dc060030000000015555555401555554010183060c187060c1830600070180c01930060c387060c18307031e0e060c0180c019dc1830060c18003018aaaaaaaa82aa2a80c183060001107818381830000a0060c183060c18300000e1c00000380000000000aaaa00aaaaaa000c18306000107bbd070f0307030601503060c183060c18000070e1c0038033b800000000001c00e003000001e0400f078003c000155540155555400014100e1c000183aaa060c18300000000a000a2a0750000000007006000000aaaaaaaa00aa0141e075503060c18300000000aaaa0f77a075000000000700677000000200088000e00700180000404002aaaaaaa802a80002820003060c183060c183060000002c58b161c3870e0c18306000b00e000300001555554015400100060c183060c183060c183060c00000000fc5c7978f8f0e1c387060c18300000000000000055555555005500060c183000083dde83878183818300a8183060c183060c00003870e001c018000000000070e1c3a834007d0f1e3c7e71ebc78f00a0f03aa8183060c180000000555507bbd03a800000000380300000091d548c3870e1d41a015400003060c183060c183060000002c58b161c3870e0c18306002d50e1c38750680235e8c183060c00003870e1c183060c000038030000000e1c3f70e5c387541834011e75e8c0003872eaa0c1a8000171e5e2f171e00001c3870e5c383060c183060c183060c180000000178b8f2f171e1c3870e0c18306000000001c01800000070e1c3870e5c3870fdd5060d0046bd7a3000060c183000087c1e060e060c003871e3c7970e1c183060c183060c000078f1e008c01800000000007468c3a8340297f7a1e3ea000060d0723ef42d50f07941a0143e060c1830000aaaa00000060000001f3af0ea83068052fef5400107a8bd2ac0d40002a000087c0c183060001517a83d40ea0600015540ea00a801780300000000000ebd7875418340287d552f000060c1830000aaaa00004600c00000038f1e1d5060d00a1fdc00183060c00021f0781c0c000118030000000e8d187506800f1f54bc003871e3c7970e1d54183500001e3c78000540c1830600001c383060c180000030000000e1d41a00000c1830600001c383060c180000033b80000001c0001800000f02001555401540001410061c183061c183060c183000ee00700000060000c183060c18b160c18b160c183060c183060c1830601c3870e1c1c0c5838183060c1830027131e4e263c003803006007700000000555555550055555500 24 16777215 10 1023
def hc_74_5 : Nat → Nat := unpackHintV5 0xc8970dc205a4bac5d0b4499fadb9a4a81d67a0ddd09cd90196cd839169598c9d338571cb80793e7b1d5770b69a69ddb65e7ad958817e5002204ce0c84881184488fe3d81c238853f3331552d95672342951ce19815a5cf109145065a8e000196 0x183061c3870e1c183061c1f7118132604c99326070384c0723a1e3e878f1e3e0f0787c0e802ee3d18f1e3c78f1e5c7a71e3c78f0e1c3870e1c3871e1c383063c18f1e3cd8f060ea0118b0462c0381c06030007903c580f160aaaaaaaa82aaaaaa280c1870e1c387061c1870e1c1972e5c0e070264c03870980e0f07a1e3e838787c0e04381c362c0d8b00603000790aaaaaaaa82aa280c18f1e3c7831e0c3870e5cb83063c19707dc2e4c984c993264070980e2e3c7c3c78f1f10787c0e04b8b0b8b0b85c0603000790aaaaaaa82aa281c787465c1974e8c1870e1c3870a00f01c981c384c274141c838f838787c3e04b8b02e2c03870390c46000f21555555555055450387061cb830e1cb83063c7870e0c181c0e13018132604c9c1e0f0f81d0f1f43c7c0870380c06171605c58000f21555555550554503870e1c387061c1833e0c0e0720180c980c1c1e0f103818f81838106030180c060c060c000642aaaaaaa0aa8a03060c3871e3c3870e1c3870e1cd870e1c3f70d932613264fb81c0e4138d8f1f0f1e3c7c1e0f10f81362c362c0e070d86c001e42aaaaaaa0aa8a073e6c387167c3800cd8f062c18b0000000202007830e002c160b00182d5555443873e6d3870e1c19b063c78f0981c2809c132603270f83d050f21e3e063e04380b0362c0180c001e42aaaaaaaaa0aa8a070e130384c270f83c3e1f401770e1c78f1e1c38f063c78f1e0ea00380000f2078b01e2c155550555555450183060c00003870e1c183060c000e77000006000001c01800c000001e04002aaa802a8020088030600c060c183060c383062c181c0e0bc981b260301830e1c38737231e8e363c183060c1183101830060c01830183000180c555555554155140600070002607703870e1c3802c580000c3870e1cd9b366c00993264c00000000001555401555400387000060c1800c180007000000003870e1e5c8c7cb918f060c18300000000000600002aaaaaaa802a802000c583060c183060c183060c183000000e001dc0062c593162c58b162c58b162c9930e1c3870e1c38700018b858b170b1e1c3870e0c18306004e263c9c4c781c03801dc001800000000aaaaaaaa00aaaaaa0081c38030183060c183a060c1c0c181c0e0fc983f260301c1c3c1c3d030740c1cc0e01e0c4060c018300603060c000642aaaaaaaa0aa8aa000c183060c183060c1830602c580b26070380c0742c5d0b1f070f070f03bbd030700f162c78b162c58b162c58b163c7870e1c3870e1c3d43c9800f1e0c183061c1830e0033b830183060003201830060c155555555055555554550183060e8228183060c183060c0e070180c25930964e83d54d5555040c3880c180c18301830a0008855555555415515402aa170baa85d507a8383060c183060c183060c1d030162c05930381c282260301d555507aaaaa81dde08187060c3800cef030a00603060c008855555555555541555154060030e2c18000783c6e3752397d40e0715507720000005555a0000e0c383966c183966c18300000000a80a00aa000000000000005555555500550040166cd8b162c58b162cfbf0e1c387060c183a00000aa02a0e0703b8000d555440160c18b160c187061c18000000042eaa85c2eaa0f507a81d541555542e1f555407702000e01c00ee002c0000000055555555005555550040e1c0003830e0d19b060d19b060c000000000f0700a087c0c0000000000580000aaaaaaaa00aa0082c580005c197062d183162c180000004042c58b058b1e3e1f03000580077038002c0000555555500550040166cd8b162c58b162cfcb0e1c387060c183160c583061c7830000085c3e007830e0703b800b05800c16aaaaa200b460c18b160c187061c18000000042e858ba162c78f83c1e1f032003b8b163c58b162c58b162c58b1e3c3870e1c3870e1c7870e0c18f1e3c18308003807003b800b00000000160b0555555550055555500400583062c583061c1870602c580b260703803170b162e163c3870e1c18300e1c3870e0073b83018b000582c555555554155154060c1830600c1830183060c18302e4c27930381c06039f171e5e9e3c3870e1c183060c01830060c0183018310183060003018aaaaaaaa82aa2a80000c180c183060c000000000003870e1dbcdc7b79b8f060c18300000000000000555555550055004060c183061c183061c183000ee0070060000c26000003060c183060c183060c183064c983064c183060c03870e1c383060c183818f070306004e263c9c4c78001dc06003000000001555555540155555401018307503060c183060c1803060c0381c1d930764c0603983d070f40c1c0e0700f060301830060c1018000c855555555415514 24 16777215 10 1023
def hc_74_6 : Nat → Nat := unpackHintV5 0x9bb0b39b6c119a4c489242038cf154875d6581fd587c855e789cfa7411236cadd96811276065eb5bb52c56c13d5201304d0d3d4934f64548fb3e6db73b98b537391830a5a52c990328092423c1121fb1041b850b1810dd1181a4065aca000196 0x3061c387061c1f70984ea8bc5e83c6c7d5043e988c5580059de2f0b8bd53ee0b0583060c3870e1c383060c383ee04c981326070384c075551793d541ea0f503a8dd43eaaaaa1f55541770a0058231601c0e0301801410b088555555554155555514060eaaa061c387065cb970381c099300e1c2603aaaaaaaa420e070d8b0362c0180c008855555555415514a9d97065d3bb061c3870e03c78070e0726070e1309c5055555521171605c58070390cd600442aaaaaaaa0aa8a070f072e0c3872e0c1d5501c0e13018132604c9d5555555521070380c06171605c5800442aaaaaaaa0aa8a070e7cda70e1c383360ea0981c078f0263c264c064eaa282aaa908383f1606c58030180110aaaaaaaa82aa281c384c0e1309c1eaa81d550faaaa82ee140070000a0858442aaaa0aaaaaa8a030183000e1c01830000000000083c1e0703a1e3e81830000000000000055555555005500061c1f7060c183061c183060c000000020f0781c0e818fa060c2ee0007003800c006003018000c00001e00000000000000002aaaaaaa802a80880003060001c380007060300000000a1e3e878f83c1e1f0300000000000000055555555005500060c1870e1c387060c18707dc000046130000a1e3e878f83c1e1f030bb8008c000b89c000e007001806c000780000000000000000aaaaaaaa00aa0220000c180000c3870e0cb972e000000010783d0f1f41c3c3e0600000000000000aaaaaaaa00aa000232e0cba7460c3870e1c000000002878fa0e1e0e3e0e1e1f0f00000000000000555555550055000e1c0e5c1870e5c18300000000000083c1e1f03a1e3e878f00000000000000555555550055000e1cf9b4e1c387066c1800000000010f83d0f1f43c7c3c7c0c7800000000000002aaaaaaa802a80070e00010f83c3e1e1770003800030000078000000000000aaaa00aa0220000c060c0000038700000060c0002aaa802aaa80000000000015554015555540018707dc183060c187060c183003800703800c006000300006030000000002aaaaaaa82000bb80000000000000002aaaaaaa8800802a8003060c3870e0c383ee00000c00e0015405dea800015554383060306000000c1800070e00000155540005deaaa800000000000155540155555400183061c3870e1c183061c1f7000b89c00000e00700d800c000000000aaaaaaaa08002ee0000000000000000aaaaaaaa200200aa000c18300000060c183060cbf70018300002aaaa802a80000000001555401555400000018306030e0fb870e0c1972e5c00000002aaaaaaa800000000000001555555540154003870e1c38000000dc1974edcb830000aaaaa00aaaa000000000000555500555555000e5c380003061c381cb8300000000aaaaaaaa00000000000000555555550055000e0cd83000000e1cda73e1c380000155554015554000000000000aaaa00aaaaaa001c38000700006000005555040017700000000000055551001005500060d060c1870e1c3870e1c383060c183060c181c0e030185003a0f0781c0e82819020c06030180c1803060000c855555555415514061c1f7060c183061c183060c0e070180c01930060e0f0781c0e818fa060e802ee1c3870e1c3870e0c183060c183063c183060c183060c78f060c783060c1d40030180c06030600c180003201830060c15555555505555554501830e1c3830e1c387060c387060c383418138280e070980e879410783c3e07028c58231601c0e03018003c855555555415514 24 16777215 10 1023
def hc_74_7 : Nat → Nat := unpackHintV5 0xd64956ce8defc342d3bb160bb5616dada5efa6d1b59ffdb59546ae90114d8a297a818e277cc13376599a6d7a386635d160816d5bc92e55619a49cee545192d3caa1c3819242f9a2027adfb225d541d0d541591df10654b084e06053cc400014f 0xe1c3870e1c387a0000e0c38300000003e00000307070f070f032060c000000000000015555555401554000386c00061c1870600001cee07c020007c1c3c1c3c0eef40c18000f000001e3c3870e1c3870e1ea0000060c180000000000000000800aaaa802aaaaaa8003060c184c987c380cee00c1870e4c9933e1c3800c183878f8f8781dde8183807d0f1e3c7c4e878f0e1c78f1e7c387a87931e4c00783c7d5000f2078f1e3c183060c0603018000c18030600c8060c01830555541555555555551400f801c183060c0181f00000019de1e3e3e1c2800078f81dde8183000e1c78f1e7c3870a000001e3ea01e4c0000183060000000000000000aa2002aa00aaaaaaa0141eaa061c18707541c3870e0cf9f0743c3870e1c387a878f1e3ea83830e0c183060c1831e0c78355555555555550e3c3878183a060c387061d3833e17265c3e4c3870e1c19f3e0e8183a0e0e0e3e0e1e6070f8797160c2e2c181c187060c183060c18fa06aaaaaaaaaaaaaa1c1830e1c183878f83c0eef40c1c3e1e1c38f1e3c387a87931e0f078f060c187060c183060c1831f40c78b060f160c5555555555555550e1c1874e0ea060c78f0e1c1830e1c3870e0cf9f065c3e4cf85c9d555355555507061c183060c197160c2e2c180c1d52aaaaaaaaaaaaa83060eaa1f0faa83c1ea0f27a83c1c187060c383060c183ef40cd86c99b0d930e1c3878a88983060c19b0755551b87d07aaaaa81ddea81830603060c060c18381c5403060c183060c1830754aaaaaaaaaaaaaaaaaaaa0c7870613261f0604c985cef03264c99b061541070e1e9aaa0aaa8180c2e17000984c885555415555140e0c383a08a060c78f263c18303a070e13261f061401c3d07aa9aaaaa08381c06031b8b06e2c0022155555555055452a0f541e0e1c1870743c0e7700e1c2822613261f060513aaaaa264c183264c99b060c3870f41eaaaaa077782aaaa0e072161400c0600131604c58442aaaaaaaa0aaaaaaa8a07061c1d070f5403c780000073b81f00000283d55103a0000000000000000055555555005550000e1400001541ea0e1b000187061c1d0f00000e77000003e01001507aaaaa81ddc0000000000000000004005555555540155402a3f507060c183a0613261f0e414144c980cee00c1870e4c9933e1c3d0550050f1e003060e8fd555540eef0551387d5503019030a006030001830060c221555555550555555545003e007a8fd41c28000021e0c183066c1803a0607c000000082600033bd1fa8280021f55540e060000000000000000000aa2002aaaaaaa00aaa0155070e0c383a1e1c3870f540cf9f07550f060c787060c78f1e3c3830e0ea8183060c1831e0c7835555555555555aaa0e1c183a1e1c3c5444c183aaaaaa81ddea8383070b8a8060c183060ea9555555555555554183060c100e030183060c0060e8183060c1c1c38003070783c0e601f43c7d0f1e0c0603018000c18030600c855554155555514060c183039dc03870183018300183060c183060c3870f0783d030703bbc03e878fa1e3c187060c187060ea064c193000603060c983260c183060c983060c183063c1830180c0600030600c1803201830060c155550555555555506a8a070e0c183060c1800503060c1800000000000f1f0783c0e000000000000001555555540154000380c00060c1830600001cee00c00a0001e3e0f07a060e077700006000000c1830e0c383060c383060ea0064c000018f0600000000000000002002aaaa00aaaaa835400000060c00060e060c00002e77006000003fbc3e0f03070300000000000000015554015400183060c1d03060e060c183060d185c99711930e1c3870e0c1830743c7d070f071f070f03070361f0f060c180c1830183060c183060c183060c1830740d55555555555554183060c0e7700e1c060c060c0060c183060c1830e1c3c1e0f030703601f43c7d0f1e1c3870f2a4c0993264d7938e4c98f54180c06030001830060c01900c06007018000c183060c000039dc0180140003c7c1e0f0307030008e002f0e1c38795001ea8000000000000003060c1870e0c183070f83c0c1c0d87c3c3d7ae1e56bd7af5c7aa0c183060c183060c183060e8183060c183060c1870e0c183070f83d030703bbc3e1e0c383060c183a819306030183063c183060c183060c183060c183a060c1830183062aaaaaaaaaaa0d555068307541c3d0307554070380c0603c78030755551414840c06030180c18030600110aaaaaaaa82aa280c383ee0c183060c383060c181c0e03018032600c1c1ea0f503a81d40e075503aaa1f5555555505dc28006030180c060c0183000a0818442aaaaaaaa0aaaaaa8a540c183a83870f507061c1f70984c1e0faa22a1182c162aaa83075541c3d550706830263c078f0381c26030a8aaaaa48abe2c2f8b00e070180c008855555555415514 24 16777215 10 1023
def hc_74_8 : Nat → Nat := unpackHintV5 0xd6a1a2d1ed2dca31efc369b2b826d1b3692fae2152a649f69fe19a947ada8cbdef8669957fb1ae7bb1007515a76f2d7a66ce1862112f5bb996566555516141486a3e44310e3d1dc537c9552f5a1c2b590024bda71f7552121f560b55b20002d5 0x183060c26070060c0677061c183060c1800c9830e1c183060c981307031e0e060c180c06030001830060c0180c55554155555514060c18300a0060c183060c18300000000883c0e0601c380000000000000002aaaaaaa802a8003060c181c00e003000067700020f77a0e1e060e060c0078f0a000a8183060c183060c00078f01e0000001c38700000000000000005555011000555555000e0c38303870387101870e1ea0e1c1831e003060c1800f07307878f8f83807d070f41c3870380c0600231608c580f21555505555554503830e0c0e1c0e1c06770060c3870e1c3870e1c0060c1c1eef41c3c3c7c7c1c03e878fa1e3ea060c78f1e6c1831e4c0078f1e4c7931e3c78f1e4c78f1e3c7870e1c381c060300098b0262c07903c580f160aaaa82aaaaaaaaaa280c9870600010f1f1f0743c7c5eee00031e3c79b074000000070e1c000000000155540155540028003830e0c993060c78f060c03800000010720e1c000387878f8f83000000000000005555555500550000380070387061c181300e00000033bc1eef41c390003e1e3e3e0c02a01e000003c783063c78f360c18000070e1c0000000000000001544005540155555400183060c0e0701883060ea060c0183060c184c9800f1f4d0781c0e01f41c3d03060c0603018000c18030600c855554155555514060c1830381c0183019dc187060c187060c0064c1c1eef41c3c0c1c0c1c03e81831e3e0740c1d40c183060c183063c9800f1e0c183060c18f1e0c18f060c1830e1c3830180c0600030600c1803201830060c15555055555555554503830f503061c1870e1c18f1e3c3870e1e186c99b2193066cd83983d070f41c3c3c7c0c7c3e1e1c187070c5830d8b0603060c183063e81aaaaaaaaaaaaaa870e1c3870e1c3c1eef41c3c3c7c3e1f0fa87831e3c78f063c98f0783c7870e1c3870e1c7d0f1e2c783c58f1555555555555541830e1c3870e0c3830e1c383a83870e1cd8fc9bf0d93066cd83a6aaaaaaaaa0e0c383362c18fc5830183060c183aa5555555555555500e1c00183060eaa818300000000a2a000aa0000000000000055555555005500a0f03aa8183060c19000440007003800c00002098000cee000555507bbd03a8021e140000000000000000000aaaaaaaa022000aa001c3870e1c3870e1c187061514070e070e1400c180d0183a6aaaaa3f541070388c58231600c0600442aaaaaaaa0aa8a5078dd540c3830e0c28226070e070e033b8030744eaaaa89930e1c3870e1c387001830755541eef47ea82aaaa85850070380c0600131604c58442aaaaaaaa0aaaaaa8a07061c18070e0144c9d500700000600015441eef47eaa0000000000000000055555555005500a0e0044004001c00f1baa8187061c1813000000e00000033bd55507bb900151fa80000000000000000015555544005540154001830e1c183060c183060ea2800e070a0264c0634d555555040c06030600c18030180110aaaaaaaa82aa295540e060c060eaa06130395144fb80c180daaa2f77aa81d5040c0640ca0180c00885555555415514a0f03aa8183060c1905051326070380306033bd03aaaaa060c187061c183061c18306003260eaaa83dde81d50550387d5540c280180c06030001830060c22155555555055555545283d55030e1c3878a889870e1c3d55507bbd55550b8a80e1c387aa55555555555555a8183060c183060c183060c1837617265c764c3870e1c183060eaaaaaa981d5540c18301830603060c183060c183060c1d52aaaaaaaaaaaaad40503060c183060c183060c1881c03870a0180eaaaaa9aa08180c060c0183006030022155555555055450183060e0f507a81c073b8070e03060306144c9905000c183060c183075544c9d13aa0e1c3d540eef555415555030180c065040c0001830060c2215555555505555554528387aa060c183000060c00000002aa8000a800000000000001555555540154000380c00060c18306100000541ea0f5038000039dc018004130000a00087d540eef5550000000000000000000800aaaaaaaa802a8003060c1c1eaa81c1c383060c1c44e2aaa0777aaaaa8183060c183060ea20700c1830754aaaaaaaaaaaaaa0c183061c1830e0c183060fb9b0d93361b261c3870e0c183071ba0e1e878f1e3e0e1e0e1e0777a060e1f0f0e1e83870e1ea83870e1c3870e1c3870e1c7a70e1ea1e4c783c1e3c183060c18301830603060c183060c183060c183a060c1830183062aaaaaaaaaaaaaaaaaa87061c1881c264c3e0c3870e0070e0c193a81830e1c0038783878387981c03e8183a1e0c381c0603001b8b06e2c0790aaaa82aaaaaa281c18706073b8070e13261f06003064c993360c1870e1e0e1e0e1e0777a060e01f43c7d0f1e1c3870e1c3870f50f26003c78f263c98f1e3c78f263c78f1e3c183061c0e03018004c58131603c81e2c078b05555415555555555514 24 16777215 10 1023
def hc_74_9 : Nat → Nat := unpackHintV5 0xb23a04aa26059efacb9b50ea91ee599090578a39967e2f03792d406dbadd6715a96005c45a097f547166505d054ab16b466d113a17163579272e69c4286d7f22c96919c6411529271130fe0cd9160791520001e4 0x18707dc183060c187060c1830e1c387060c1830603260c060c3870e1c183060c1c0c7838183060c183060c183060c180c1830183060c183060d555555555555542613060c1801c0601c38700181c0387060c18707dc2e2700000038006c0465d3974e8ef803c803870e1c19b360c00460000000000000000aaaa0220aaaa00aa000c1830e1c3870e0c1830e0fb813264c985c4e070e070e13261b060000c187061c38070e1c383064c99347ccba72e9d1870e1c383366c1931184c993898f27131e5f78174e01c0e03018004c58131608c15555555505555554522021181070701c19030f00c384130000e1b2821e501e3701230000551487c3c1830750781d070e1ea0707a0e1c183061c1f7465d197468f9c44e283870e1c19b360e2f27aaaaa83d546eaaa9197060cba3060ea21701c187060c183060c1d52aaaaaaaaaaaaaaaaa8306030038000177a80055060c387266c060c381c383264c3871e6c98f1e3c7c3c78f2743e060c3c1c383263c980f07d40131e3c78f1e3c582c160b15554183061c3870e1c183061c1f7477cba32e8d1870e1c383366c1d0f1e3c7c5e4f070f070f0f1f1b070f878faaa060c3830e1e83870e1c1831e4c783c1e3c78f1e5e983065d183061c187060c183060c18fa063c583078b062aaaaaaaaaaaaaaaaa8b85800e07503018383838180c1c0c1c130584ca170faaa0f03a462c1d040c580c383062c1d2aaaa8003060c1830060c183061c1830600c183060c383060c183ee05cb817de02c980b16070380c065cb972e5cbd3170b1e2e162c3870e1c183060c1180c060c5831600c5830603061c0603060c05800c18b0180d5555555555550554550183061c3870e1c183061c1f713934e130e1c387060e4e3d3c3c3870e1c183160c4e2c181c187060c183060c18306aaaaaaaaaaaaaa1c187001830e0c3870e0c9932620700e1c0387099301930e1c387471b1e6e463c19b360c98130e07218b0362c0180c00460aaaaaaaa82aa281c3870e073b8070e13261300983264c993061c3870e1c3872604c9c4c793898f0e07000098b0262c01555505555554501830e1c3870e0c3830e1c383000000000003870e1cdc8c7a38d8f066cd830000000000000005555555500550000e0000c3870e1c000039dc0020007870e1c3800000000000000800aaaa802a80000c183060c183060c183060c1800000000301bc5c7979b8f0e1c387060c1830000000000000055555555005500060c183038000300006770000387060c18300790000000000000002aaa8088002a8003060c187060c383060c183ee1b00e1c0993264c0e1c0e1c06770060c38700e1c387000e1c3870e1c3870e1c387269c38700183066e363cdc6c7870e1c383060c1930264e263c9c4c7830600c18030180c0600030600c1803018aaaaaaaa82aaaaaa2801c00061c1870604c3870e1c38700003870e1c19f3e0c993264c00000000000155555554003930e1c060c01830e1c1874e0c018300e0c0e4c0e1c4067e2e3cbc7c7870e1c3833e7c1930265c58171601c0e03018008c15555555505545038306132607019dc01830e1c993261c3800c1830e1c1832604c9c4c793898f0e00c0600131604c5802aaaa0aaaaaa8a070e0c3a706003064c9870e0c1800000000070e1c387067cf832f1f1e7e2e3c0000000000000155555554015400183060013098001c0e00713801c0e0c383061c183060c18300600001b0980700000019dcdc6c79b8d8f0e1c3872000783060c19b060000000000000000000aaaaaa2002aaa00aa0000070e0c3830260013060c987060c3870e1c0019f3e0c993264c0000000001540155555400000387060c0980000000cee1c390003c18300000000000000551001550055001f0f060ea0e0ea06030703070306130384c8987060cbc5eaaa0f50301900c060d555541830603060c184c0e4c383070f1e3cbc5e0e1e2f5540c183060c183060c98071e3c180c060c180c55555060c1830600c1830183060c1830264c038703930387018301b171e5e1e1c3870e1c183060c9813060c01830060c060c0603000180c555555555415514 24 16777215 10 1023
def nh_74 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_74_9 (Nat.sub p 288)) (hc_74_8 (Nat.sub p 256)) (Nat.blt p 288)) (hc_74_7 (Nat.sub p 224)) (Nat.blt p 256)) (Bool.rec (hc_74_6 (Nat.sub p 192)) (hc_74_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 224)) (Bool.rec (Bool.rec (Bool.rec (hc_74_4 (Nat.sub p 128)) (hc_74_3 (Nat.sub p 96)) (Nat.blt p 128)) (hc_74_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (hc_74_1 (Nat.sub p 32)) (hc_74_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)
def f_74 : Nat → Nat × Nat := unpackForestF 0xc5b98b6f98b639bb7d98a6f9aa449a47198a639927d9896f00c5797b5600b5b96c6d00b5795c6600b4f93d6793c6693b6600b4b91d6a91c6791b6a00b479026f902638fb6600b438ea548a45f8da448a45b8c6788c26c8a4578b2448a4538a25600a5b84c6d88c7c84b4f87b7c84b4b86d7084b478537c8536484b4300a5781c668335481b6b8247c81b6700a4f7cd67802447cc6b7f27c7cc677cc5b7cc577cb667ca6600a4b7756a774677a6787a36c7736b79570773677734b773477726a00a47762447246b7527c72467743557226672b5b72b577202400a43713546bd6b6e37e6e37c6e2726eb8c6e17f6bd676d46d6bb666c56a6bb5600a3f6aa546756b69a7c6756768c6d6726667d6a6725600a3b6645861d6b64c7264c7061d67635696335661c6a6236661c5a00a3760a545b56b5fa7c5b5675e46d5e4555b2665bd6a5bc6a5bc665b95f5b25600a330095b5246d58d7c58b7c5234b57a7c5224b56d705224754d7d54b7c54b565223f52a7c52a6452a5652233009574a46650b544a36b4fa544a26b4ec7c4a2674d5764d3544a23f4ad764bc664aa644aa544a2330094f4913440b6b4817c40b6740a66409664125b41257411564105b410574102f432664102b410274193441023408140094b3d36b3d26b3d2673d23f3da543d233009473c13439b6b3b17c39b673a25539966009433827f3827332d673726632a6b3657d32a6734b7634a7632a5b3367a3327a32a570093f319342fb6b3097c2fb672f9660093b284722b23f2db4c2b23b2b2372c23c2bb442b233284702a4802827f28d8028a5c282731c567273561c46a263661c45a24a6624a5c1c26b2357d234701c26720d7a20b7620a7620a5c1c25b1ce7a1cc7a1db6b1e57c1db671cc601ca7a1c257009371b1341436b1a17c14367192551416614a5b14a571485b148571482f1482b148271482314014009331327c0e567122440e46b112440e45b1046d0e2660ed6a0eb6b0e2560092f0d1660092b0c3480a4730b4710a3720a37003d6708c6608b4803c6b074760734803c5b05c5b05a5603b6a0446b0426603b5a00927011660185b0185701014009230003f 9 11
def ch_74 : Nat → Bool := dagCheckNodeV5 fullMask g_74 ep_74 5 31 bds_74 315 (dagTraceF fullMask rootStock 11 f_74) cur_74 nh_74
set_option maxHeartbeats 0 in
theorem rc_74 : dagCheckRootsV5 fullMask g_74 ep_74 5 31 315 bds_74 (dagTraceF fullMask rootStock 11 f_74) (cur_74 0) (nh_74 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_74_0 : treeBlockF 0 32 ch_74 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_74_1 : treeBlockF 32 64 ch_74 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_74_2 : treeBlockF 64 96 ch_74 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_74_3 : treeBlockF 96 128 ch_74 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_74_4 : treeBlockF 128 160 ch_74 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_74_5 : treeBlockF 160 192 ch_74 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_74_6 : treeBlockF 192 224 ch_74 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_74_7 : treeBlockF 224 256 ch_74 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_74_8 : treeBlockF 256 288 ch_74 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_74_9 : treeBlockF 288 315 ch_74 = true := by decide +kernel
theorem nj_74_1 : ∀ i, 0 ≤ i → i < 64 → ch_74 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_74_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_74_1 h1 h2)
theorem nj_74_2 : ∀ i, 0 ≤ i → i < 96 → ch_74 i = true := block_join nj_74_1 (fun _ h1 h2 => treeBlockF_at nb_74_2 h1 h2)
theorem nj_74_3 : ∀ i, 0 ≤ i → i < 128 → ch_74 i = true := block_join nj_74_2 (fun _ h1 h2 => treeBlockF_at nb_74_3 h1 h2)
theorem nj_74_4 : ∀ i, 0 ≤ i → i < 160 → ch_74 i = true := block_join nj_74_3 (fun _ h1 h2 => treeBlockF_at nb_74_4 h1 h2)
theorem nj_74_5 : ∀ i, 0 ≤ i → i < 192 → ch_74 i = true := block_join nj_74_4 (fun _ h1 h2 => treeBlockF_at nb_74_5 h1 h2)
theorem nj_74_6 : ∀ i, 0 ≤ i → i < 224 → ch_74 i = true := block_join nj_74_5 (fun _ h1 h2 => treeBlockF_at nb_74_6 h1 h2)
theorem nj_74_7 : ∀ i, 0 ≤ i → i < 256 → ch_74 i = true := block_join nj_74_6 (fun _ h1 h2 => treeBlockF_at nb_74_7 h1 h2)
theorem nj_74_8 : ∀ i, 0 ≤ i → i < 288 → ch_74 i = true := block_join nj_74_7 (fun _ h1 h2 => treeBlockF_at nb_74_8 h1 h2)
theorem nj_74_9 : ∀ i, 0 ≤ i → i < 315 → ch_74 i = true := block_join nj_74_8 (fun _ h1 h2 => treeBlockF_at nb_74_9 h1 h2)
theorem nc_74 : ∀ i, 0 ≤ i → i < 315 → ch_74 i = true := nj_74_9
theorem lb_74 : LowerBin fullMask rootStock g_74 12 :=
  lowerDagV5 (kn_cons lb_49 (kn_cons lb_73 (kn_cons lb_70 (kn_cons lb_43 (kn_cons lb_69 (kn_cons lb_71 (kn_cons lb_68 (kn_cons lb_66 (kn_cons lb_45 (kn_cons lb_67 (kn_cons lb_61 (kn_cons lb_3 (kn_cons lb_72 (kn_cons lb_46 (kn_cons lb_21 (kn_cons lb_34 (kn_cons lb_64 (kn_cons lb_30 (kn_cons lb_37 (kn_cons lb_60 (kn_cons lb_22 (kn_cons lb_44 (kn_cons lb_50 (kn_cons lb_47 (kn_cons lb_36 (kn_cons lb_63 (kn_cons lb_52 (kn_cons lb_58 (kn_cons lb_31 (kn_cons lb_17 (kn_cons lb_48 (kn_cons lb_57 (kn_nil))))))))))))))))))))))))))))))))) rc_74 nc_74 (by decide +kernel)

def wg : List Gate := [⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.and, [3, 8]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.and, [5, 10]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [4, 11]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.or, [1, 14]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.or, [12, 16]⟩, ⟨GateOp.and, [15, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4008241280 * 2 ^ 32 + 3902851200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4008241280 * 2 ^ 32 + 3902851200)) (13 - 1) := by
  rw [show canon fullMask (4008241280 * 2 ^ 32 + 3902851200) = g_74 by decide]
  exact lb_74

end PEqualNP.Outside.L_meta_48949

theorem PEqualNP.Outside.L_meta_48949 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241280 * 2 ^ 32 + 3902851200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241280 * 2 ^ 32 + 3902851200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_48949.table2_from_lowerBin (4008241280 * 2 ^ 32 + 3902851200) 13 PEqualNP.Outside.L_meta_48949.root_lb PEqualNP.Outside.L_meta_48949.wg 18 rfl PEqualNP.Outside.L_meta_48949.wfits PEqualNP.Outside.L_meta_48949.weval

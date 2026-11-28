import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48352

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

def m_0 : Nat := 0x5050505000000000
def s_0 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_0 : Nat := 0x10105000000000
def ep_0 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
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

def m_1 : Nat := 0x5500550000000000
def s_1 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_1 : Nat := 0x100150000000000
def ep_1 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
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

def m_2 : Nat := 0xf0f0
def s_2 : List Nat := [0x5050, 0x3030, 0xf0]
def g_2 : Nat := 0x1070
def ep_2 : Nat := 0x60000000000000000000000000000010200000000000001040
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

def m_3 : Nat := 0xff0000
def s_3 : List Nat := [0x550000, 0x330000, 0xf0000]
def g_3 : Nat := 0x170000
def ep_3 : Nat := 0x6000000000000001200000000000000140000
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

def m_4 : Nat := 0x4444444400000000
def s_4 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_4 : Nat := 0x4044400000000
def ep_4 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_5 : Nat := 0x3333000000000000
def s_5 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_5 : Nat := 0x113000000000000
def ep_5 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
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

def m_6 : Nat := 0x5555000000000000
def s_6 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_6 : Nat := 0x115000000000000
def ep_6 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
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

def m_7 : Nat := 0x222200002222
def s_7 : List Nat := [0x20200000202, 0x2200000022, 0x2222]
def g_7 : Nat := 0x200000222
def ep_7 : Nat := 0x22000000000000000000000000200000020000000020000020000000000000000000000000000000000
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

def m_8 : Nat := 0xaa000000aa
def s_8 : List Nat := [0x2200000022, 0xa0000000a, 0xaa]
def g_8 : Nat := 0x20000002a
def ep_8 : Nat := 0x2800000000000000000000000000000000000000020000000800000002000000200000000000000000
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

def m_9 : Nat := 0xff000000000000
def s_9 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_9 : Nat := 0x17000000000000
def ep_9 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_10 : Nat := 0xf000f0
def s_10 : List Nat := [0x500050, 0x300030, 0xf0]
def g_10 : Nat := 0x100070
def ep_10 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040
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

def m_11 : Nat := 0xf0f000000000000
def s_11 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_11 : Nat := 0x107000000000000
def ep_11 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_12 : Nat := 0x3300000033000000
def s_12 : List Nat := [0x1100000011000000, 0x300000003000000, 0x33000000]
def g_12 : Nat := 0x100000013000000
def ep_12 : Nat := 0x1200000000000000000000000000000000000000010000000200000000000000000000000100000010000000
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

def m_13 : Nat := 0x44444444
def s_13 : List Nat := [0x4040404, 0x440044, 0x4444]
def g_13 : Nat := 0x40444
def ep_13 : Nat := 0x4400000000000040040000000000004040000000000000000000000000000000000
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

def m_14 : Nat := 0xaa00aa
def s_14 : List Nat := [0x220022, 0xa000a, 0xaa]
def g_14 : Nat := 0x2002a
def ep_14 : Nat := 0x280000000000000000000000000002000800000000000200200000000000000000
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

def m_15 : Nat := 0xcc00cc
def s_15 : List Nat := [0x440044, 0xc000c, 0xcc]
def g_15 : Nat := 0x4004c
def ep_15 : Nat := 0x480000000000000000000000000004000800000000000000000000000000040040
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

def m_16 : Nat := 0xcc330000cc33
def s_16 : List Nat := [0x441100004411, 0x3300000033, 0xc0300000c03, 0xcc33]
def g_16 : Nat := 0x41300000c33
def ep_16 : Nat := 0x820000000000000000000000000000000000000040200000c0000000000000000000000041000000000
def bds_16 : List (Nat × List Nat × Nat × Nat) := []
def cur_16 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xba5d37b3a7b2d4e80f 7 127 3 7 6 63 9 511
def nh_16 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_16 : Nat → Nat × Nat := unpackForestF 0x1f6e87a3b1d4e80f 3 6
def ch_16 : Nat → Bool := dagCheckNodeV5 m_16 g_16 ep_16 1 1 bds_16 7 (dagTraceF m_16 s_16 4 f_16) cur_16 nh_16
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV5 m_16 g_16 ep_16 1 1 7 bds_16 (dagTraceF m_16 s_16 4 f_16) (cur_16 0) (nh_16 0) s_16 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16 : treeBlockF 0 7 ch_16 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 7 → ch_16 i = true := fun _ h1 h2 => treeBlockF_at nb_16 h1 h2
theorem lb_16 : LowerBin m_16 s_16 g_16 5 :=
  lowerDagV5 (kn_nil) rc_16 nc_16 (by decide +kernel)

def m_17 : Nat := 0x3c003c003c003c00
def s_17 : List Nat := [0x1400140014001400, 0xc000c000c000c00, 0x3c0000003c00, 0x3c003c00]
def g_17 : Nat := 0x140010001c00
def ep_17 : Nat := 0x100008000000140000000c000000000000000000000000000000000000000000000000000000140010001000
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
def cur_17 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xa9610f 4 15 2 3 6 63 8 255
def nh_17 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_17 : Nat → Nat × Nat := unpackForestF 0x1a708f 1 6
def ch_17 : Nat → Bool := dagCheckNodeV5 m_17 g_17 ep_17 1 1 bds_17 3 (dagTraceF m_17 s_17 4 f_17) cur_17 nh_17
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV5 m_17 g_17 ep_17 1 1 3 bds_17 (dagTraceF m_17 s_17 4 f_17) (cur_17 0) (nh_17 0) s_17 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17 : treeBlockF 0 3 ch_17 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 3 → ch_17 i = true := fun _ h1 h2 => treeBlockF_at nb_17 h1 h2
theorem lb_17 : LowerBin m_17 s_17 g_17 5 :=
  lowerDagV5 (kn_nil) rc_17 nc_17 (by decide +kernel)

def m_18 : Nat := 0x3c3c3c3c
def s_18 : List Nat := [0x14141414, 0xc0c0c0c, 0x3c003c, 0x3c3c]
def g_18 : Nat := 0x10141c3c
def ep_18 : Nat := 0xc280000000000040020000000000000000000000000000000000000000010141000
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
def cur_18 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x14b59280f 4 15 2 3 9 511 11 2047
def nh_18 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_18 : Nat → Nat × Nat := unpackForestF 0x32dc940f 1 9
def ch_18 : Nat → Bool := dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 3 (dagTraceF m_18 s_18 4 f_18) cur_18 nh_18
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 3 bds_18 (dagTraceF m_18 s_18 4 f_18) (cur_18 0) (nh_18 0) s_18 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18 : treeBlockF 0 3 ch_18 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 3 → ch_18 i = true := fun _ h1 h2 => treeBlockF_at nb_18 h1 h2
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagV5 (kn_nil) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0xaa0000aaaa0000aa
def s_19 : List Nat := [0x2200002222000022, 0xa00000a0a00000a, 0xaa000000aa, 0xaa0000aa]
def g_19 : Nat := 0x20200002a
def ep_19 : Nat := 0x200002800000000000000000000000000000000000000020200000800000002020000200000000000000000
def bds_19 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cc_19_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xf41e83d0762e83d0390f20e41b8b22e40c8180b00600c0170ad0da0b03602c054294b282504628c09c019001 0x65300b860160c0331805e300b2601c9303720069400c260150c0261e0483405a60090c0101002e3004c60084801da403740062600a4800e100144c02088289084b190914e11284214f83e990092d0f09c1d1282823044420807c0f0e80c1b00c320105b7c8fee91dd7e379fc67384ee5499c752b81a46ff0fde61db78375a066a90bd30159ec27200462b07c02098000f 11 2047 5 31 10 1023 19 524287
def cc_19_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb46d0a5290a4290a068091240902409022284610841f27850e400f12d0b028464180510c83008402 0xc830f93cf534692cc440b820e14cdd44312cb430c93c592cc548b93c212cb538fd4ef14aed46e942e53ed93ad536d132092dcc4ec042bc3eb0320821a9208d40a524604468249d30813099242834302458248e405444202482301c34 10 1023 4 15 10 1023 16 65535
def cc_19_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xdc5b83706a2d41a83506a0a5948290501985302414808c31823042270ae01b0b60682d01a0340604b840b800 0x17e3010965d8e2e461923ec71ce28cb0c638230bc972d4a6da456921b290580bab85b3430a2984f0c28c6130309f184d8c262614e40a5185050270812c309216424d21c602120849a7ad3bbe85da39e718f253b7285193d829d6a4db326b593458971f48aa89d504a94234810a387d183d8a170308a203d041d 11 2047 5 31 10 1023 17 131071
def cc_19_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xf03d8781c56843081f1364682d01812c254290d20202308600c0180246480901201863004104208000800000 0x10c1c08071fb407d8c1081c96d3a574a93d264b488ed1a37428bd062b407c8f9123d874f8d939844ca0d31824c1fc3e470f5fc2e7c0a5a822660855820644f10e3079481c540784d14844530d0b52c754c02120204c1d124648f10d344d0d13c14438c1c12071d01bd344b11138146dd01b1306b0f1a740688c19c3c438f19528438f175305f4f17130 11 2047 5 31 10 1023 18 262143
def cc_19_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x9038e18e08648608416125e15835805614e44e04e04e04e04644414403862e52e02c12442212011651410a5081061003 0x287409f0b1381c91932334894d003130420810934a8d3a9f42a68e69631a44fa8d3d7c4d50532a213a784a9d11a70429b0d9f0359a0b83c2299079041d65082534c974e19020430c2524c895321940630c2334c9193241408f13188307ed32324c885321540811318430810f9f8396d0c9a431600c17c3089d2223400c4f178205d0c1703086d2217407d8f2003c5b0816830800b9f4296c089a021590810e3c084b20740424b20030 12 4095 5 31 10 1023 18 262143
def cc_19_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x8a18a08628608227857807807427214574404213c33a13a03a03813803423210f20c10a10a00a0081061060022020001 0xb6512ed304f0c2ee30700825340bc902e9304e0c1bc204d8c05930b65137749dad076649d6906f94db552b4946ce5170144aa4f9b932304b88922bf13af84dbd0fa703ab90d92032b80b84422b707ad41dac0c14e3cb24a2ac408f1323d344d8f2b128ab922ce4eb192ac246af90a663e468f6b92934486b44eaa10a903aa30e5fc36460c5fc269b094bc1e2104a4434a1121ac24670d2802c4f0728230 12 4095 5 31 10 1023 18 262143
def cc_19_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x9ad286504627c8f05e0382684d01a03405c6b81702e050690901200400800e11c0380608c018030060006000 0xdfd3adf4df293bc64df0932c6498e917be42ee907b640ea538f149e750b9941e5503884ebf137883edf0e74832ce0c70030ab4f13630dc481c540db4d2f044940d0c52cd84c05920234c35d24d59035140d31334740d09033c4c4d8f31d30c94f31930168f32530c78f31a30cd8faae39cc8cb2e31ca8c3213e314e71532c44c70d30c20fb043d 11 2047 5 31 10 1023 18 262143
def cc_19_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x8e18c18c08c08a18818048007e17e07c15925045005004464213853803612e42c12a12051e11451211010a3081061003 0x8c0d28448d30d33c44919314e401a502d8308cd22d944fed27f741fc927ee41fa53be54ddf516d542f811b7c45f70fa783af60d95032f50b87422f407ad41d53933b14ce95033430e1d32464ceb533a140e41333030cb103903ee10e75432d10c72830c90c06a4cec533ad40c80c31c30c60c3834ce9933a240e31331430c41038c3ee00e75032d00c70c304d8f05a3cb68f39140e3101341c160738740e0902d81c 12 4095 5 31 10 1023 18 262143
def cc_19_8 : Nat → List (Nat × Nat) := unpackCursorV5 0x9a07ee7e07a27817807616e46e06e06a26a0681661660660660622585580580542540540540502465270260241240012 0x4a74e94685088ca4ea74894a90a8d2050a1096a98393b062360763e0cc7815078231a90228a244d248c8411ad02311a4454489249134c21e1844e30870610f8c21c984523089281114c2202643440858310a050ea1809c20832910550018901d030130411cd3a37a145e42844751653a2aa54314684a85084b54a1c9cc3112842340760e0cc1015018228f131e9a72fb4d4b47b028e6031aabe31802723a4c5f4253e4497108cbe105c41b3e0355685c72088660f09012 12 4095 5 31 10 1023 19 524287
def cc_19_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xe41c0780700e01c02a7540a05402614c0981209f2be07c0f81d1305220400708e01442804088000800000000 0x499489f6933dd065f214f13e912753b4da2a994bd2d7e092d9104780ece8199c82a1d04635204d14489a61320c26518465209a481124c230904cc3c98860d80c054104b538962601a481ae200a4209be9336d065f2545e329aa7d204ea609b4253297a5afb125ac208a0211d03b2e066560a8441193291134b24a0c4963093681124b2480c48c14 11 2047 5 31 10 1023 19 524287
def cc_19_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xf01e03c0723e41c83906c3d81b0341642c8190320602c01802e15c0b8113220421840f89e0bc0780e0972817 0xaf4995d502b82056a4caca8158102271e53830a80794d0c09f1e54030a72794d4c2ad1f5563daa27d264e6a69954931a8a614f0f9421cd3032a58634a0c28ba244d302786145d11b8181e4204a480538c2829036c403c06147d3689a556f46abe8b49d12912751e4da347d448f67aa4cd941942731b4c68694c25217e892da1054e1c9dc315785b420a6801292021 11 2047 5 31 10 1023 19 524287
def cc_19_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xde0dc1b92b61b41ac4aa1aa0aa0a818527e37837046656416216015655605414c44c04c04a14813c63a13813612c5016 0x918f2f1a751f4dbdc957a926e72351e41b9c6d798d6fe9cc813194a531c4852c1edf839be86a9c0c550149e821af4695a9128b1844940478984e1028ba223248bde9d7ad36e5a2d1342bcc8d72916f11f5123d9f29337506ee94c55217f092dd1056216dd829ba84a540868b1e5b940b1081458f2daa0584408969954482d62659840b6e996e932a7185a84cb288152d02271e44e3cb747d6d8e6bb1956631a8c61504809da653d20b58996a1029c9053630b0e996293299185994cb2a808f13297a013e3c27c79628fac31cd7232ac4634a8c2e5a751b4db9c9d48936e71f5ca39adc65578c693185c54e912937050adea0db140b489d68136ce26278494708b6410ac620d8040 12 4095 5 31 10 1023 19 524287
def cur_19 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec ([]) (cc_19_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (cc_19_10 (Nat.sub p 320)) (cc_19_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (cc_19_8 (Nat.sub p 256)) (cc_19_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_19_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_19_5 (Nat.sub p 160)) (cc_19_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_19_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_19_2 (Nat.sub p 64)) (cc_19_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_19_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def hc_19_0 : Nat → Nat := unpackHintV5 0x8031f827e01f027c01f007a09e807a01e026e29b806e01b0260317825e017025c017005a096805a016024e293804e0130246189a00290002 0x55551551555515510451450040514515115 14 16383 6 63
def hc_19_1 : Nat → Nat := unpackHintV5 0xc003000c002c10ae0a88ca202880a202490900a18a86021027a29c0a7001b8264290244000f823428d003208a0a221878414283860a1000a 0x555155555545545555515555555104501551551414414144 14 16383 6 63
def hc_19_2 : Nat → Nat := unpackHintV5 0xf80be00f803d82f40bb08e03350cbc62a149c327009a0a680980a600980260098025828c2a3007a49b0e603178250394004c1100c0cd000c 0x155555555555555555555555545555545555551555555545555555551455555 14 16383 6 63
def hc_19_3 : Nat → Nat := unpackHintV5 0xec03b00e61b026b432d00b20a890982a600960a30a8031d0c7401c82624168858094084628f883c08d082a28a80261088416304060040000 0x51541515555555555555555055555555555555555555555555555555555 14 16383 6 63
def hc_19_4 : Nat → Nat := unpackHintV5 0xea1b70ed033286c80ae1086ca1808019c107001b04546150054015004e18f903e00e84226088022008802200880200878206601800600006 0x455555551555555555555545155155555555555155555555555455555551 14 16383 6 63
def hc_19_5 : Nat → Nat := unpackHintV5 0xa51936526814d009905282a4c1460e8a090831a9a31106200be19607290c510496312c02484431854c89060f0c19142c18406050c022000100000000 0x15455555545555555554555555555145555554555555555555555555515455555555555551155555555555 15 32767 6 63
def hc_19_6 : Nat → Nat := unpackHintV5 0x6f4cd231a4034026020b6296c02d025514a2214012608471486210811f0839146e10d03170c26204c009411280250048088c10f88191826301cc000e 0x5455555555555555555541555555555555555555555555555555555555555555 15 32767 6 63
def hc_19_7 : Nat → Nat := unpackHintV5 0x8e1910320c540067a18e831c433490621cc20964820323e086c40a8c1404202028605000a0014002800500098212040c601800300030c06000c00006 0x55555555115555551555555555555555555555145555555555555555555555551555555454 15 32767 6 63
def hc_19_8 : Nat → Nat := unpackHintV5 0x7a20d091943300a5e08bc017412c0a5218a209401280050009e093c027804f009c092452480490090091431f8c3f007c08e4514a0212034386410032 0x15555505101551541015555551155115551545440014555555555551545555555 15 32767 6 63
def hc_19_9 : Nat → Nat := unpackHintV5 0x87150429f063a106e18cc4151228864c148c31141228045008808fc51e0636186c00d41180a20403628585080c0f041e003c007800f000e40181000c 0x5455555515555551555051550155154155551544555455440140515455555545555555 15 32767 6 63
def hc_19_10 : Nat → Nat := unpackHintV5 0x9111200a304438a83110409f843c8a7318da31b0135826a04cc2198032046400c8018432d8c53208e610071d0c331c6210ac6150220283e086850034 0x155555555555555555555555555555555555555555515555555155555554555555554551555 15 32767 6 63
def hc_19_11 : Nat → Nat := unpackHintV5 0xb321583a4d9468c87190819f083d827320d8394d928064d0c9a0130125824b009600fcc1f803f007a10d481498290052009c20f901f003e004cc0026 0x1555555555515455555555555545555555555555555555154555514455555555555555555555555555554151555555 15 32767 6 63
def hc_19_12 : Nat → Nat := unpackHintV5 0x2 0x1 4 15 2 3
def nh_19 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_19_12 (Nat.sub p 384)) (hc_19_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (hc_19_10 (Nat.sub p 320)) (hc_19_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (hc_19_8 (Nat.sub p 256)) (hc_19_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_19_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_19_5 (Nat.sub p 160)) (hc_19_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_19_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_19_2 (Nat.sub p 64)) (hc_19_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_19_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_19 : Nat → Nat × Nat := unpackForestF 0xbea737d0e6fa1a8063fbae9d75d36eb235d63ebaa53750a6ea128063bb047d608e6c0a758142b02836d8fadb1cd8140b50996a102c0275804db009965532caa058042b0083618fac31cd804000c6f5c932b8a057040a068d58932b0a056040a068b4a8fa951ed293ea52654a4c6949854030a507d4d4f29a9852832a50634a0c281a25024ea049b408fa8ba25023da0253400a682905002500c6739d2673a0ce53e9ca6d39066720a8053b95e932bd06569f4c64098879328c262184ad3695a5b2b066589c4b1309582a014ce3da747b428f29d23d024b1848c18918291e52a3ca3479428f0331e0540295c134e8268518d02321046234824850453a08a54363089c610d5021a984344c874610e4c21a2041146850310a05208a14112d82033055220aa04101500a47008e6011ac01390087ef4d25e9a0bd2497a482f4539e8a6bd0467a07cf40d9e8173d01e00876df939bf26b7e4c6fc84df905bf203ad4c75a80df539d1263a2406fa84df505bea038d4071880df0f9c1a0382406f872010dd6ba4b71206da68b5d056b24b61306ba48b5905a72034d4069898b55199fa033e4067898b5515831f3063260c62c18c192983053e63478c68c182993053160a60c10f9821ead5445a89cb51356a1f2ea405dc60ba4c16a1b2d42e5a83cb65116a0e804335549cb24a155252aa4655484aa4a554272b12855c90aa1080217a674e4ce84998e53318a653e4ca7a991393fa0282304f858991293223264424c86c990b9320f0042b4ba707cd38f9a52524c3e6927cd211f2623d40478987cd18f9a12324c3e6827cd0111a4223403e27c85d210ba01f1323e2627c4c101a0200303e05c7dd00fb181f0290084e41d38f2901e13420e84418e4ea981d12420c6241538dfa01c12037a6841508d7a01ad3035878414d8cfa019e3033878414d4ca9415e3e2bc72578c8af1895e302fc60574b8b91c172302ba4457484ae9015c2e2b85a414d082271044a25c804b8c0a31812d4027c604b10099181313025860411189216104422087c410f482171041e21c60424d0820e804231629c3d4f07a9a0b14a1628c2c508589f0dd4c1ba882c4e8589b0b1321609c324f062a40b0421607c2e4f05a9c0b0320083e2a480529200a4213a602649005190094e11c8002508049f08230012640213804250564c0ac80155003318055300b460164c02a180084609078120d004210083e0107407d200fa001d3005c600748011180212003840020d808260104401064020b402098000f 9 10
def ch_19 : Nat → Bool := dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 384 (dagTraceF m_19 s_19 6 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 384 bds_19 (dagTraceF m_19 s_19 6 f_19) (cur_19 0) (nh_19 0) s_19 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_0 : treeBlockF 0 32 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_1 : treeBlockF 32 64 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_2 : treeBlockF 64 96 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_3 : treeBlockF 96 128 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_4 : treeBlockF 128 160 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_5 : treeBlockF 160 192 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_6 : treeBlockF 192 224 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_7 : treeBlockF 224 256 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_8 : treeBlockF 256 288 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_9 : treeBlockF 288 320 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_10 : treeBlockF 320 352 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_11 : treeBlockF 352 384 ch_19 = true := by decide +kernel
theorem nj_19_1 : ∀ i, 0 ≤ i → i < 64 → ch_19 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_19_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_19_1 h1 h2)
theorem nj_19_2 : ∀ i, 0 ≤ i → i < 96 → ch_19 i = true := block_join nj_19_1 (fun _ h1 h2 => treeBlockF_at nb_19_2 h1 h2)
theorem nj_19_3 : ∀ i, 0 ≤ i → i < 128 → ch_19 i = true := block_join nj_19_2 (fun _ h1 h2 => treeBlockF_at nb_19_3 h1 h2)
theorem nj_19_4 : ∀ i, 0 ≤ i → i < 160 → ch_19 i = true := block_join nj_19_3 (fun _ h1 h2 => treeBlockF_at nb_19_4 h1 h2)
theorem nj_19_5 : ∀ i, 0 ≤ i → i < 192 → ch_19 i = true := block_join nj_19_4 (fun _ h1 h2 => treeBlockF_at nb_19_5 h1 h2)
theorem nj_19_6 : ∀ i, 0 ≤ i → i < 224 → ch_19 i = true := block_join nj_19_5 (fun _ h1 h2 => treeBlockF_at nb_19_6 h1 h2)
theorem nj_19_7 : ∀ i, 0 ≤ i → i < 256 → ch_19 i = true := block_join nj_19_6 (fun _ h1 h2 => treeBlockF_at nb_19_7 h1 h2)
theorem nj_19_8 : ∀ i, 0 ≤ i → i < 288 → ch_19 i = true := block_join nj_19_7 (fun _ h1 h2 => treeBlockF_at nb_19_8 h1 h2)
theorem nj_19_9 : ∀ i, 0 ≤ i → i < 320 → ch_19 i = true := block_join nj_19_8 (fun _ h1 h2 => treeBlockF_at nb_19_9 h1 h2)
theorem nj_19_10 : ∀ i, 0 ≤ i → i < 352 → ch_19 i = true := block_join nj_19_9 (fun _ h1 h2 => treeBlockF_at nb_19_10 h1 h2)
theorem nj_19_11 : ∀ i, 0 ≤ i → i < 384 → ch_19 i = true := block_join nj_19_10 (fun _ h1 h2 => treeBlockF_at nb_19_11 h1 h2)
theorem nc_19 : ∀ i, 0 ≤ i → i < 384 → ch_19 i = true := nj_19_11
theorem lb_19 : LowerBin m_19 s_19 g_19 7 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0xff00ff0000000000
def s_20 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_20 : Nat := 0x100150000000000
def ep_20 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000100150000000000
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_20 : Nat → List (Nat × Nat) := fun _ => []
def nh_20 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_20 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 0 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) (nh_20 0) s_20 4 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 0 (dagTraceF m_20 s_20 4 f_20) cur_20 nh_20 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xffff000000000000
def s_21 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_21 : Nat := 0x117000000000000
def ep_21 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11), (m_9, s_9, 4, g_9), (m_6, s_6, 4, g_6), (m_5, s_5, 4, g_5)]
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
  lowerDagV5 (kn_cons lb_11 (kn_cons lb_9 (kn_cons lb_6 (kn_cons lb_5 (kn_nil))))) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xffff00000000
def s_22 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_22 : Nat := 0x155700000000
def ep_22 : Nat := 0x4200000000000004020000000000001002000000000000155400000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := []
def cc_22_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_22_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_22 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_22_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_22_0 p) (Nat.blt p 32)
def hc_22_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_22_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_22_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_22 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_22_2 (Nat.sub p 64)) (hc_22_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_22_0 p) (Nat.blt p 32)
def f_22 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
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

def m_23 : Nat := 0xff00ff00000000
def s_23 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_23 : Nat := 0x17005700000000
def ep_23 : Nat := 0x40000000000000000000000000000600020000000000120002000000000014005400000000
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_23 : Nat → List (Nat × Nat) := fun _ => []
def nh_23 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 0 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) (nh_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 0 (dagTraceF m_23 s_23 4 f_23) cur_23 nh_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0xf0f0f0f000000000
def s_24 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_24 : Nat := 0x10105000000000
def ep_24 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000010105000000000
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def nh_24 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0xf0f0f0f00000000
def s_25 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_25 : Nat := 0x107050700000000
def ep_25 : Nat := 0x400000000000006000200000000000000000000000001020002000000000104050400000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def nh_25 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) (nh_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 nh_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0xcccccccc00000000
def s_26 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_26 : Nat := 0x4044400000000
def ep_26 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def nh_26 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) (nh_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 nh_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0x3333333300000000
def s_27 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_27 : Nat := 0x113111300000000
def ep_27 : Nat := 0x1000000000000012000200000000010200020000000000000000000000000110111000000000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def nh_27 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) (nh_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 nh_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0x5050505050505050
def s_28 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_28 : Nat := 0x10105010101050
def ep_28 : Nat := 0x1000000000001040000000400010004000000040000000000000000000101000101010000000000000000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_28 : Nat → List (Nat × Nat) := fun _ => []
def nh_28 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 0 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) (nh_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 0 (dagTraceF m_28 s_28 4 f_28) cur_28 nh_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0x66666666
def s_29 : List Nat := [0x22222222, 0x6060606, 0x660066, 0x6666]
def g_29 : Nat := 0x2060666
def ep_29 : Nat := 0x4600000000000040060000000000206060000000000000000000000000000000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_29 : Nat → List (Nat × Nat) := fun _ => []
def nh_29 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 0 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) (nh_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 0 (dagTraceF m_29 s_29 4 f_29) cur_29 nh_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0x5555555500000000
def s_30 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_30 : Nat := 0x115155500000000
def ep_30 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_6, s_6, 4, g_6), (m_0, s_0, 4, g_0), (m_4, s_4, 4, g_4)]
def cc_30_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_30_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_30 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_30_1 (Nat.sub p 32)) (cc_30_0 p) (Nat.blt p 32)
def hc_30_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_30_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_30 : Nat → Nat := fun p => Bool.rec (hc_30_1 (Nat.sub p 32)) (hc_30_0 p) (Nat.blt p 32)
def f_30 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_30 : Nat → Bool := dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 43 (dagTraceF m_30 s_30 6 f_30) cur_30 nh_30
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 43 bds_30 (dagTraceF m_30 s_30 6 f_30) (cur_30 0) (nh_30 0) s_30 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_0 : treeBlockF 0 32 ch_30 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_1 : treeBlockF 32 43 ch_30 = true := by decide +kernel
theorem nj_30_1 : ∀ i, 0 ≤ i → i < 43 → ch_30 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_30_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_30_1 h1 h2)
theorem nc_30 : ∀ i, 0 ≤ i → i < 43 → ch_30 i = true := nj_30_1
theorem lb_30 : LowerBin m_30 s_30 g_30 7 :=
  lowerDagV5 (kn_cons lb_1 (kn_cons lb_6 (kn_cons lb_0 (kn_cons lb_4 (kn_nil))))) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0x3030303030303030
def s_31 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_31 : Nat := 0x10101010101030
def ep_31 : Nat := 0x1000002000001000000000200010000000000020000000000000000000000000000000000010101010101000
def bds_31 : List (Nat × List Nat × Nat × Nat) := []
def cc_31_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_31_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_31 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_31_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_31_0 p) (Nat.blt p 32)
def hc_31_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_31_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_31_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_31 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_31_2 (Nat.sub p 64)) (hc_31_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_31_0 p) (Nat.blt p 32)
def f_31 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_31 : Nat → Bool := dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 64 (dagTraceF m_31 s_31 5 f_31) cur_31 nh_31
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 64 bds_31 (dagTraceF m_31 s_31 5 f_31) (cur_31 0) (nh_31 0) s_31 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_0 : treeBlockF 0 32 ch_31 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_1 : treeBlockF 32 64 ch_31 = true := by decide +kernel
theorem nj_31_1 : ∀ i, 0 ≤ i → i < 64 → ch_31 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_31_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_31_1 h1 h2)
theorem nc_31 : ∀ i, 0 ≤ i → i < 64 → ch_31 i = true := nj_31_1
theorem lb_31 : LowerBin m_31 s_31 g_31 6 :=
  lowerDagV5 (kn_nil) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0xcccc0000cccc
def s_32 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_32 : Nat := 0x44400000c4c
def ep_32 : Nat := 0x808000000000000000000000040000000400000040000000c0800000000000000000000044400000040
def bds_32 : List (Nat × List Nat × Nat × Nat) := []
def cur_32 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_32 : Nat → Nat := fun _ => 0
def f_32 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_32 : Nat → Bool := dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 1 (dagTraceF m_32 s_32 3 f_32) cur_32 nh_32
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 1 bds_32 (dagTraceF m_32 s_32 3 f_32) (cur_32 0) (nh_32 0) s_32 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32 : treeBlockF 0 1 ch_32 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 1 → ch_32 i = true := fun _ h1 h2 => treeBlockF_at nb_32 h1 h2
theorem lb_32 : LowerBin m_32 s_32 g_32 4 :=
  lowerDagV5 (kn_nil) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0x3333000033330000
def s_33 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_33 : Nat := 0x113000013130000
def ep_33 : Nat := 0x1200000000000000000000000012000000000000010200000202000000000000000000000110000010100000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def nh_33 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) (nh_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 nh_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0x5555000055550000
def s_34 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_34 : Nat := 0x115000011150000
def ep_34 : Nat := 0x1000000000000000000000000014000000040000010400000004000001100000111000000000000000000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def nh_34 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) (nh_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 nh_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0x5500550055005500
def s_35 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_35 : Nat := 0x100150011001500
def ep_35 : Nat := 0x1000000000001400000004000000000000000000010004000000040001001000110010000000000000000000
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def nh_35 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) (nh_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 nh_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0xff000000ff00
def s_36 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_36 : Nat := 0x150000001f00
def ep_36 : Nat := 0xa00000000000000000000000000000000000000040000000e0000001000000010000000150000001000
def bds_36 : List (Nat × List Nat × Nat × Nat) := []
def cur_36 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_36 : Nat → Nat := fun _ => 0
def f_36 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_36 : Nat → Bool := dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 1 (dagTraceF m_36 s_36 3 f_36) cur_36 nh_36
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 1 bds_36 (dagTraceF m_36 s_36 3 f_36) (cur_36 0) (nh_36 0) s_36 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36 : treeBlockF 0 1 ch_36 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 1 → ch_36 i = true := fun _ h1 h2 => treeBlockF_at nb_36 h1 h2
theorem lb_36 : LowerBin m_36 s_36 g_36 4 :=
  lowerDagV5 (kn_nil) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0xff000000ff
def s_37 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_37 : Nat := 0x570000007f
def ep_37 : Nat := 0x2800000000000000000000000000000000000000020000000800000002000000200000005400000040
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def nh_37 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) (nh_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 nh_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0xf0f00000f0f0
def s_38 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_38 : Nat := 0x105000001070
def ep_38 : Nat := 0x2000000000000000000000004000000060000000000000000000001000000010200000105000001040
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def nh_38 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0x333300003333
def s_39 : List Nat := [0x111100001111, 0x30300000303, 0x3300000033, 0x3333]
def g_39 : Nat := 0x111300001333
def ep_39 : Nat := 0x22000000000000000000000000200000020000000020000020000000000000000000000111000001000
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def nh_39 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) (nh_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 nh_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xaaaa0000aaaa
def s_40 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_40 : Nat := 0x200000a2a
def ep_40 : Nat := 0xa28000000000000000000000002000000200000000200000a0800000002000000200000000000000000
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def nh_40 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0x3300330033003300
def s_41 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_41 : Nat := 0x100110013001300
def ep_41 : Nat := 0x1200020000001000000000000000000000000000010000000200020000000000000000000100110010001000
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0xcc00cc00cc00cc
def s_42 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_42 : Nat := 0x400440004004c
def ep_42 : Nat := 0x800000040000000480000000000000000000400000004000800000000000000000004004400040040
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def nh_42 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) (nh_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 nh_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xffff0000
def s_43 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_43 : Nat := 0x13170000
def ep_43 : Nat := 0x40000000000000206000000000000131200000000000010140000
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def nh_43 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) (nh_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 nh_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xffff
def s_44 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_44 : Nat := 0x1f7f
def ep_44 : Nat := 0x600000000000000e0800000000000010200000000000001040
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def nh_44 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) (nh_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 nh_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0xff00ff00
def s_45 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_45 : Nat := 0x13001f00
def ep_45 : Nat := 0xc0000000000000000000000000002000e0000000000130010000000000010001000
def bds_45 : List (Nat × List Nat × Nat × Nat) := []
def cur_45 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_45 : Nat → Nat := fun _ => 0
def f_45 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_45 : Nat → Bool := dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 1 (dagTraceF m_45 s_45 3 f_45) cur_45 nh_45
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 1 bds_45 (dagTraceF m_45 s_45 3 f_45) (cur_45 0) (nh_45 0) s_45 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45 : treeBlockF 0 1 ch_45 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 1 → ch_45 i = true := fun _ h1 h2 => treeBlockF_at nb_45 h1 h2
theorem lb_45 : LowerBin m_45 s_45 g_45 4 :=
  lowerDagV5 (kn_nil) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xff00ff
def s_46 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_46 : Nat := 0x17007f
def ep_46 : Nat := 0x680000000000000000000000000006000800000000001200200000000000140040
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_10, s_10, 4, g_10), (m_15, s_15, 4, g_15), (m_14, s_14, 4, g_14)]
def cc_46_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_46_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_46 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_46_1 (Nat.sub p 32)) (cc_46_0 p) (Nat.blt p 32)
def hc_46_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_46_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_46 : Nat → Nat := fun p => Bool.rec (hc_46_1 (Nat.sub p 32)) (hc_46_0 p) (Nat.blt p 32)
def f_46 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_46 : Nat → Bool := dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 43 (dagTraceF m_46 s_46 6 f_46) cur_46 nh_46
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 43 bds_46 (dagTraceF m_46 s_46 6 f_46) (cur_46 0) (nh_46 0) s_46 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_0 : treeBlockF 0 32 ch_46 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_1 : treeBlockF 32 43 ch_46 = true := by decide +kernel
theorem nj_46_1 : ∀ i, 0 ≤ i → i < 43 → ch_46 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_46_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_46_1 h1 h2)
theorem nc_46 : ∀ i, 0 ≤ i → i < 43 → ch_46 i = true := nj_46_1
theorem lb_46 : LowerBin m_46 s_46 g_46 7 :=
  lowerDagV5 (kn_cons lb_3 (kn_cons lb_10 (kn_cons lb_15 (kn_cons lb_14 (kn_nil))))) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0xf0f0f0f0
def s_47 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_47 : Nat := 0x10101070
def ep_47 : Nat := 0x600000000000000060000000000000000000000000101010200000000010101040
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def nh_47 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) (nh_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 nh_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0xcccccccc
def s_48 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_48 : Nat := 0x40c4c
def ep_48 : Nat := 0xc4800000000000400400000000000040c0800000000000000000000000000040040
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def nh_48 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xaaaaaaaa
def s_49 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_49 : Nat := 0x2020a2a
def ep_49 : Nat := 0x82800000000000000200000000002020a0800000000020200200000000000000000
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def nh_49 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) (nh_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 nh_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0x55555555
def s_50 : List Nat := [0x11111111, 0x5050505, 0x550055, 0x5555]
def g_50 : Nat := 0x11151555
def ep_50 : Nat := 0x4400000000000040040000000000004040000000000111010000000000000000000
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def nh_50 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) (nh_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 nh_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0xff000000ff000000
def s_51 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_51 : Nat := 0x100000013000000
def ep_51 : Nat := 0x1200000000000000000000000000000000000000010000000200000001000000130000000100000010000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def nh_51 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 0 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) (nh_51 0) s_51 4 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 0 (dagTraceF m_51 s_51 4 f_51) cur_51 nh_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0xf000f000f000f0
def s_52 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_52 : Nat := 0x10005000100070
def ep_52 : Nat := 0x2000000040000000600000000000000000000000000000000000100000001000200010005000100040
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def nh_52 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 0 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) (nh_52 0) s_52 4 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 0 (dagTraceF m_52 s_52 4 f_52) cur_52 nh_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0xf0f00000f0f0000
def s_53 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_53 : Nat := 0x107000003070000
def ep_53 : Nat := 0x200000000000000000000000006000000040000000000000000000001020000030200000104000000040000
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def nh_53 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 0 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) (nh_53 0) s_53 4 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 0 (dagTraceF m_53 s_53 4 f_53) cur_53 nh_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0x5050a0a05050a0a0
def s_54 : List Nat := [0xa0a00000a0a0, 0x1010202010102020, 0x5000a0005000a0, 0x5050a0a0]
def g_54 : Nat := 0x10000010100020
def ep_54 : Nat := 0x1000002000000000000000000010000000000020000000000000000000100000101000200000000000000000
def bds_54 : List (Nat × List Nat × Nat × Nat) := []
def cur_54 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1d3c30c1d3020c0e3024f263e88c993e54c903e10c800f 7 127 3 7 10 1023 14 16383
def nh_54 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_54 : Nat → Nat × Nat := unpackForestF 0xc7c632e9814f8a6443e51824f086400f 3 10
def ch_54 : Nat → Bool := dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 10 (dagTraceF m_54 s_54 4 f_54) cur_54 nh_54
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 10 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) (nh_54 0) s_54 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54 : treeBlockF 0 10 ch_54 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 10 → ch_54 i = true := fun _ h1 h2 => treeBlockF_at nb_54 h1 h2
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV5 (kn_nil) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0x2222222222222222
def s_55 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_55 : Nat := 0x2000202020222
def ep_55 : Nat := 0x200022000000000000000200002000200000020000200020202020000000000000000000000000000000000
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_55 : Nat → List (Nat × Nat) := fun _ => []
def nh_55 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_55 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 1 1 0 bds_55 (dagTraceF m_55 s_55 4 f_55) (cur_55 0) (nh_55 0) s_55 4 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_55 g_55 ep_55 1 1 bds_55 0 (dagTraceF m_55 s_55 4 f_55) cur_55 nh_55 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_55 : LowerBin m_55 s_55 g_55 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0xa0a0a0a0a0a0a0a
def s_56 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_56 : Nat := 0x2000202020a0a
def ep_56 : Nat := 0x2000a0800000000000008080002000200000000000000000000000000020002020200000000000000000000
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

def m_57 : Nat := 0x5a5a00005a5a
def s_57 : List Nat := [0xa0a00000a0a, 0x121200001212, 0x5a0000005a, 0x5a5a]
def g_57 : Nat := 0x105200001a5a
def ep_57 : Nat := 0xa0800000000000000000000004200000040000000000000000000001002000010000000000000000000
def bds_57 : List (Nat × List Nat × Nat × Nat) := []
def cc_57_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xec1d07a0686d0198720e40c4388300d65ac148a905209c5382704e0944f99f03e07c0f81f03e07c0d901d001 0x1e4d104747e3634970e4b4e85a7025340e100f078582c2c1c9e17130b088542c28120f0b060283c34160a0c0d05858483d221a900b8705a341d140a8513020880c3c041a498fe34770e378519c14fe0276fd376e99b44bd7a56b1275691aa0fd4876a0374619a20bcd85c642b30139308c4844201f0e0d8605c0826000f 11 2047 5 31 10 1023 17 131071
def cc_57_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xc2c0b9b8b8b8b18d88816b686868684c48483330303030303030301409080100 0xf52ce414f534e534fa44f13ced34e818e014782cda4cd644743ccd4cc944c418c014b83cb430702c9c3c9834942c902438308414 8 255 3 7 10 1023 16 65535
def cc_57_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x183060c112039468100b1020401 0x9b38993496389434422c91288f24403c8a4c88403e2c7d30 7 127 3 7 9 511 16 65535
def cur_57 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_57_2 (Nat.sub p 64)) (cc_57_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_57_0 p) (Nat.blt p 32)
def hc_57_0 : Nat → Nat := unpackHintV5 0xb40590ac054caa414f1a60d28492147123050c684142020850407e23e09f00f807c0354962494e3891a10b8c5822820f280b8002 0x0 13 8191 5 31
def hc_57_1 : Nat → Nat := unpackHintV5 0xd866a13311904c425e22c194109844b0a3911448243f11e88e0a6c23411810aca4491b389244421e20d1050c14a0430200084002 0x0 13 8191 5 31
def hc_57_2 : Nat → Nat := unpackHintV5 0x4311f90f447623629910c425a42b11488948405155852c014 0x0 13 8191 5 31
def nh_57 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_57_2 (Nat.sub p 64)) (hc_57_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_57_0 p) (Nat.blt p 32)
def f_57 : Nat → Nat × Nat := unpackForestF 0x252712934941c4a0d00c7f1d288e92018ee20991040031b818cc0a7e053b029bb8911ea68e13c709a38061ca68e0140299b5931ac88052f60a6305118030c0140295ad0f1686005270291810fc08760437481e240d1205890240219810bd0828723a391b1e4d0e05a702502171a07008560427282614110a058502402118a0f4506a282e1e1a0a0b4503a2c3416160a0540844041f020d8105c10980844041e020d00826000f 7 10
def ch_57 : Nat → Bool := dagCheckNodeV5 m_57 g_57 ep_57 1 1 bds_57 78 (dagTraceF m_57 s_57 5 f_57) cur_57 nh_57
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 1 1 78 bds_57 (dagTraceF m_57 s_57 5 f_57) (cur_57 0) (nh_57 0) s_57 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_0 : treeBlockF 0 32 ch_57 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_1 : treeBlockF 32 64 ch_57 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_2 : treeBlockF 64 78 ch_57 = true := by decide +kernel
theorem nj_57_1 : ∀ i, 0 ≤ i → i < 64 → ch_57 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_57_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_57_1 h1 h2)
theorem nj_57_2 : ∀ i, 0 ≤ i → i < 78 → ch_57 i = true := block_join nj_57_1 (fun _ h1 h2 => treeBlockF_at nb_57_2 h1 h2)
theorem nc_57 : ∀ i, 0 ≤ i → i < 78 → ch_57 i = true := nj_57_2
theorem lb_57 : LowerBin m_57 s_57 g_57 6 :=
  lowerDagV5 (kn_nil) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0x5a005a005a005a00
def s_58 : List Nat := [0xa000a000a000a00, 0x1200120012001200, 0x5a0000005a00, 0x5a005a00]
def g_58 : Nat := 0x100012001a00
def ep_58 : Nat := 0x12000a0000001000000008000000000000000000000000000000000000001000120010000000000000000000
def bds_58 : List (Nat × List Nat × Nat × Nat) := []
def cur_58 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x14a59080f 4 15 2 3 9 511 11 2047
def nh_58 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_58 : Nat → Nat × Nat := unpackForestF 0x329c840f 1 9
def ch_58 : Nat → Bool := dagCheckNodeV5 m_58 g_58 ep_58 1 1 bds_58 3 (dagTraceF m_58 s_58 4 f_58) cur_58 nh_58
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 1 1 3 bds_58 (dagTraceF m_58 s_58 4 f_58) (cur_58 0) (nh_58 0) s_58 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58 : treeBlockF 0 3 ch_58 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 3 → ch_58 i = true := fun _ h1 h2 => treeBlockF_at nb_58 h1 h2
theorem lb_58 : LowerBin m_58 s_58 g_58 5 :=
  lowerDagV5 (kn_nil) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0xc0c0c0c0c0c0c0c
def s_59 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_59 : Nat := 0x4040400040c0c
def ep_59 : Nat := 0x8080000040000000c080004000000040000000000000000000000000000000000000004040400040000
def bds_59 : List (Nat × List Nat × Nat × Nat) := []
def cur_59 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_59 : Nat → Nat := fun _ => 0
def f_59 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_59 : Nat → Bool := dagCheckNodeV5 m_59 g_59 ep_59 1 1 bds_59 1 (dagTraceF m_59 s_59 3 f_59) cur_59 nh_59
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 1 1 1 bds_59 (dagTraceF m_59 s_59 3 f_59) (cur_59 0) (nh_59 0) s_59 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59 : treeBlockF 0 1 ch_59 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 1 → ch_59 i = true := fun _ h1 h2 => treeBlockF_at nb_59 h1 h2
theorem lb_59 : LowerBin m_59 s_59 g_59 4 :=
  lowerDagV5 (kn_nil) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0x1122112211221122
def s_60 : List Nat := [0x22002200220022, 0x102010201020102, 0x112200001122, 0x11221122]
def g_60 : Nat := 0x102110211021122
def ep_60 : Nat := 0x1000002000001000000000200000000000000000010200020002000000000000000000000000000000000000
def bds_60 : List (Nat × List Nat × Nat × Nat) := []
def cur_60 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x193430d19282090d28209263a88d9d3a54d903a10d800f 7 127 3 7 10 1023 14 16383
def nh_60 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_60 : Nat → Nat × Nat := unpackForestF 0xc7463629d64a0a6c43a494209086c00f 3 10
def ch_60 : Nat → Bool := dagCheckNodeV5 m_60 g_60 ep_60 1 1 bds_60 10 (dagTraceF m_60 s_60 4 f_60) cur_60 nh_60
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 1 1 10 bds_60 (dagTraceF m_60 s_60 4 f_60) (cur_60 0) (nh_60 0) s_60 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60 : treeBlockF 0 10 ch_60 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 10 → ch_60 i = true := fun _ h1 h2 => treeBlockF_at nb_60 h1 h2
theorem lb_60 : LowerBin m_60 s_60 g_60 5 :=
  lowerDagV5 (kn_nil) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0x5555555555555555
def s_61 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_61 : Nat := 0x115155511151555
def ep_61 : Nat := 0x1000000000001440000004400014004000040040010404000004040001101000111010000000000000000000
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_30, s_30, 7, g_30)]
def cur_61 : Nat → List (Nat × Nat) := fun _ => []
def nh_61 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_61 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 1 1 0 bds_61 (dagTraceF m_61 s_61 7 f_61) (cur_61 0) (nh_61 0) s_61 7 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_61 g_61 ep_61 1 1 bds_61 0 (dagTraceF m_61 s_61 7 f_61) cur_61 nh_61 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_61 : LowerBin m_61 s_61 g_61 8 :=
  lowerDagV5 (kn_cons lb_30 (kn_nil)) rc_61 nc_61 (by decide +kernel)

def m_62 : Nat := 0xff00ff00ff00ff00
def s_62 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_62 : Nat := 0x100150013001f00
def ep_62 : Nat := 0x12000a000000140000000c0000000000000000000100040002000e0001001000130010000100150010001000
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_51, s_51, 5, g_51), (m_12, s_12, 4, g_12), (m_20, s_20, 5, g_20), (m_45, s_45, 4, g_45), (m_1, s_1, 4, g_1), (m_36, s_36, 4, g_36), (m_17, s_17, 5, g_17), (m_58, s_58, 5, g_58)]
def cc_62_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x886208821178de0781c26c5b06c1a15cd705c15254141501314c13044910405003c4f03c0d207001 0x38091c682f45175273609196bcc352509228d0968a4aa5e4c9222925048a725e31a9148e4946a3a4e15a1068e824650b437d27b490d747e92333ca79a4bcb24e403f18178809c102e001f 10 1023 4 15 11 2047 17 131071
def cc_62_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x38e15402 0x7a515a41623d8e398a3583496341 6 63 3 7 10 1023 16 65535
def cur_62 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_62_1 (Nat.sub p 32)) (cc_62_0 p) (Nat.blt p 32)
def hc_62_0 : Nat → Nat := unpackHintV5 0xfa867d403e50be796da33ec21f61018f43c3c7e1e030a0b7e8daba7d5c029d2329ca94c040349fa0edb446d80350395b9aad80402d9f21cac9a4f0e27800955000940000 0x2f76e799e19e6739ee79abce758b2867a98e8673af5baf554401c3af73dd7a2bd5b9cef5ea0a0f41c38f71c0aab585ce1c15838741ceb5505881758b070e170d673aa80ac58171c3963738ce3618d121add94701c671a8e862c1c3aae3874316338ce35a583218e1d57bd706719d546315910c70105d3a73a871100f1e5a88 17 131071 7 127
def hc_62_1 : Nat → Nat := unpackHintV5 0x6a00b53ec54d6c3805b 0x4f7bac1c9d6ea9cebc1510e761c3859e6a73dcf339d62c39c70ea 15 32767 7 127
def nh_62 : Nat → Nat := fun p => Bool.rec (hc_62_1 (Nat.sub p 32)) (hc_62_0 p) (Nat.blt p 32)
def f_62 : Nat → Nat × Nat := unpackForestF 0x891cc48d4168703490527b7145b49ce3416c120290d86bcc352051fa714934bca3424c92028cd0492824504a79c978125e63520493928e4946a083f1d27020bc56840827091d048c8102e001f 6 11
def ch_62 : Nat → Bool := dagCheckNodeV5 m_62 g_62 ep_62 3 7 bds_62 36 (dagTraceF m_62 s_62 7 f_62) cur_62 nh_62
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 m_62 g_62 ep_62 3 7 36 bds_62 (dagTraceF m_62 s_62 7 f_62) (cur_62 0) (nh_62 0) s_62 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_0 : treeBlockF 0 32 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_1 : treeBlockF 32 36 ch_62 = true := by decide +kernel
theorem nj_62_1 : ∀ i, 0 ≤ i → i < 36 → ch_62 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_62_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_62_1 h1 h2)
theorem nc_62 : ∀ i, 0 ≤ i → i < 36 → ch_62 i = true := nj_62_1
theorem lb_62 : LowerBin m_62 s_62 g_62 8 :=
  lowerDagV5 (kn_cons lb_51 (kn_cons lb_12 (kn_cons lb_20 (kn_cons lb_45 (kn_cons lb_1 (kn_cons lb_36 (kn_cons lb_17 (kn_cons lb_58 (kn_nil))))))))) rc_62 nc_62 (by decide +kernel)

def m_63 : Nat := 0xf0f0f0f0f0f0f0f0
def s_63 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_63 : Nat := 0x10105010101070
def ep_63 : Nat := 0x1000002000001040000000600010004000000060000000000000000000101000101010200010105010101040
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_31, s_31, 6, g_31), (m_52, s_52, 5, g_52), (m_47, s_47, 5, g_47), (m_38, s_38, 5, g_38), (m_24, s_24, 5, g_24), (m_54, s_54, 5, g_54), (m_28, s_28, 5, g_28), (m_10, s_10, 4, g_10), (m_0, s_0, 4, g_0)]
def cur_63 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x113184a4e3264f9352394895e790d543148c01f 6 63 2 3 10 1023 14 16383
def nh_63 : Nat → Nat := unpackHintV5 0xdf00ac66ac0070786791620b62003658006c0000 0x17aec14017a31ac13d739e74701ac63d80c6300558d6033cb39d7471ec73b640603557bd6008d426a3c7005e800de3001ac78e00129e1c7 16 65535 7 127
def f_63 : Nat → Nat × Nat := unpackForestF 0x2129190d93e150cb52294895e148c01f 4 10
def ch_63 : Nat → Bool := dagCheckNodeV5 m_63 g_63 ep_63 3 7 bds_63 9 (dagTraceF m_63 s_63 7 f_63) cur_63 nh_63
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV5 m_63 g_63 ep_63 3 7 9 bds_63 (dagTraceF m_63 s_63 7 f_63) (cur_63 0) (nh_63 0) s_63 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63 : treeBlockF 0 9 ch_63 = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 9 → ch_63 i = true := fun _ h1 h2 => treeBlockF_at nb_63 h1 h2
theorem lb_63 : LowerBin m_63 s_63 g_63 8 :=
  lowerDagV5 (kn_cons lb_31 (kn_cons lb_52 (kn_cons lb_47 (kn_cons lb_38 (kn_cons lb_24 (kn_cons lb_54 (kn_cons lb_28 (kn_cons lb_10 (kn_cons lb_0 (kn_nil)))))))))) rc_63 nc_63 (by decide +kernel)

def m_64 : Nat := 0x3333333333333333
def s_64 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_64 : Nat := 0x113111313131333
def ep_64 : Nat := 0x1200022000001000000000200012000200000020010200020202020000000000000000000110111010101000
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_31, s_31, 6, g_31), (m_27, s_27, 5, g_27), (m_41, s_41, 5, g_41), (m_33, s_33, 5, g_33), (m_39, s_39, 5, g_39), (m_55, s_55, 5, g_55), (m_60, s_60, 5, g_60), (m_5, s_5, 4, g_5), (m_7, s_7, 4, g_7)]
def cur_64 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x205d3095a5d209935a3958856791d447109c01f 6 63 2 3 10 1023 14 16383
def nh_64 : Nat → Nat := unpackHintV5 0xda80a669a60071e971806a8e638e365b006c0000 0x14000b9756c1e738cef18c23af650009f5ce719e63182d5abb053bb1b6e1adeb008140e338c72132a8d005d001c671800433cb5009469d 16 65535 7 127
def f_64 : Nat → Nat × Nat := unpackForestF 0x205d191da5d111cb5a2958856109c01f 4 10
def ch_64 : Nat → Bool := dagCheckNodeV5 m_64 g_64 ep_64 3 7 bds_64 9 (dagTraceF m_64 s_64 7 f_64) cur_64 nh_64
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV5 m_64 g_64 ep_64 3 7 9 bds_64 (dagTraceF m_64 s_64 7 f_64) (cur_64 0) (nh_64 0) s_64 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64 : treeBlockF 0 9 ch_64 = true := by decide +kernel
theorem nc_64 : ∀ i, 0 ≤ i → i < 9 → ch_64 i = true := fun _ h1 h2 => treeBlockF_at nb_64 h1 h2
theorem lb_64 : LowerBin m_64 s_64 g_64 8 :=
  lowerDagV5 (kn_cons lb_31 (kn_cons lb_27 (kn_cons lb_41 (kn_cons lb_33 (kn_cons lb_39 (kn_cons lb_55 (kn_cons lb_60 (kn_cons lb_5 (kn_cons lb_7 (kn_nil)))))))))) rc_64 nc_64 (by decide +kernel)

def m_65 : Nat := 0xff00ff00ff00ff
def s_65 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_65 : Nat := 0x1700570017007f
def ep_65 : Nat := 0x2800000040000000680000000000000000000600020006000800120002001200200014005400140040
def bds_65 : List (Nat × List Nat × Nat × Nat) := [(m_46, s_46, 7, g_46)]
def cur_65 : Nat → List (Nat × Nat) := fun _ => []
def nh_65 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_65 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV5 m_65 g_65 ep_65 1 1 0 bds_65 (dagTraceF m_65 s_65 7 f_65) (cur_65 0) (nh_65 0) s_65 7 = true := by decide +kernel
theorem nc_65 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_65 g_65 ep_65 1 1 bds_65 0 (dagTraceF m_65 s_65 7 f_65) cur_65 nh_65 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_65 : LowerBin m_65 s_65 g_65 8 :=
  lowerDagV5 (kn_cons lb_46 (kn_nil)) rc_65 nc_65 (by decide +kernel)

def m_66 : Nat := 0xffffffff00000000
def s_66 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_66 : Nat := 0x117155700000000
def ep_66 : Nat := 0x1440000000000016004200000000010604020000000001121002000000000114155400000000
def bds_66 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 7, g_21), (m_30, s_30, 7, g_30), (m_20, s_20, 5, g_20), (m_24, s_24, 5, g_24), (m_27, s_27, 5, g_27), (m_26, s_26, 5, g_26), (m_25, s_25, 5, g_25), (m_23, s_23, 5, g_23), (m_22, s_22, 6, g_22)]
def cur_66 : Nat → List (Nat × Nat) := unpackCursorV5 0x13098486411188442030078bc1e0e1703443801 0x3230cd11d30791092028d3e3fe8ef637b8ce93f94ee13764cd52f44acd27148c01f 9 511 4 15 10 1023 14 16383
def nh_66 : Nat → Nat := unpackHintV5 0xab9f09c9f08e2e785f83762fd687db5d0b74fed24906e3cfc12f4db23db716bd20fd6e03cc10003c00000 0xaaaaaa318d554671ece718ce73aaace75ad6b9735c37bc62000000000000aaaaa338f6318c6aaaa338c631aa9ce738c6318c638731c2000000000000aaaaaa318d54e759ce318ce3553ccf1ce78e739c6f78c400000000000155554671ed54e739c6318c40000006002aaaaa8c6318ce355551ac6318d55673ac6318c631c398e1000000000065c001555556a5559ceb5ad635bd635558f6ce7a39cf3a708000000000002aaaa9ce73aac7b75554aaab1e8753eaa1000000000000555555a954ef38ce738ce739d54e759cf51e9d38400000000000155554e739d563dbaa10000000085555559ceb555aa8f552aaacba1d4faa84000000000008b82aaa8c631aaaa8d6318ce31d4aab3a743b631d0c6f10000000000005555578de355aa876ea955565d47a9f542000000000000aaaaaaf5bcef3bd6aaf1bc752ace9c318c63a8708000000000002aaaabdef7aad54fb62000000010aaaaa318c6aab55550e55559751ea1d50800000000001170555555100000000 20 1048575 8 255
def f_66 : Nat → Nat × Nat := unpackForestF 0x18fc63b18df34418cc53f14ec537791053314bc52b149ca34148c01f 4 10
def ch_66 : Nat → Bool := dagCheckNodeV5 m_66 g_66 ep_66 3 7 bds_66 16 (dagTraceF m_66 s_66 8 f_66) cur_66 nh_66
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV5 m_66 g_66 ep_66 3 7 16 bds_66 (dagTraceF m_66 s_66 8 f_66) (cur_66 0) (nh_66 0) s_66 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66 : treeBlockF 0 16 ch_66 = true := by decide +kernel
theorem nc_66 : ∀ i, 0 ≤ i → i < 16 → ch_66 i = true := fun _ h1 h2 => treeBlockF_at nb_66 h1 h2
theorem lb_66 : LowerBin m_66 s_66 g_66 9 :=
  lowerDagV5 (kn_cons lb_21 (kn_cons lb_30 (kn_cons lb_20 (kn_cons lb_24 (kn_cons lb_27 (kn_cons lb_26 (kn_cons lb_25 (kn_cons lb_23 (kn_cons lb_22 (kn_nil)))))))))) rc_66 nc_66 (by decide +kernel)

def m_67 : Nat := 0xffffffff
def s_67 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_67 : Nat := 0x13171f7f
def ep_67 : Nat := 0xc6800000000000400600000000002060e0800000000131210200000000010141040
def bds_67 : List (Nat × List Nat × Nat × Nat) := [(m_46, s_46, 7, g_46), (m_43, s_43, 5, g_43), (m_10, s_10, 4, g_10), (m_49, s_49, 5, g_49), (m_48, s_48, 5, g_48), (m_44, s_44, 5, g_44), (m_50, s_50, 5, g_50), (m_13, s_13, 4, g_13), (m_2, s_2, 4, g_2), (m_45, s_45, 4, g_45), (m_18, s_18, 5, g_18), (m_14, s_14, 4, g_14)]
def cc_67_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x7c27a17a07057007007007007007006c26c06826046006006006005c25c05c05825045005005005004e146432a038001 0xb088080b04c220f3441d4902415070220182c0e4b82a5402d1a09938176bc2cd6851ab093520e4b81a5402d1a051381069e1ed2c31a384b43044680ed3c19a582b47036864d17c922d8fc571b8a634170642a0c04c1108c10110081651b4fa169730d1e2da1c3a4f854970891e0921c0a3f7f476f68ddd519b984f71096de11d9821b203f5f076bc0dd7019a802f470564e09c04118001f 12 4095 5 31 11 2047 19 524287
def cc_67_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xacab099660982518ca308c23088620882028020080200801e256550504d72c8b020c711c05214005 0x1d24866481cb587ed21f2447a521893074d11dc5e73149a95c668d191345b16164506ed3db34b68d1d8b436053d79475c4fd5937520e949308d17e245b8115de45370d29513050128b8440e0b0b0544a110302c1c0d0a844440911b6c42981006c28110282c 10 1023 4 15 11 2047 18 262143
def cc_67_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xe0e0d9d8d8d1d0d0c2c0c0c0aba8858080808072707062443230222020190300 0xba0dad244b09b2b960aad12a244a6522dc5fb316eb457a514e8a469adb2626094d124a489f17e745b9715e445376d21b9308ad21b130844f21b6082581a130 8 255 3 7 11 2047 18 262143
def cc_67_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xe8e8e8c5c0c0c0c0c09d989190898881806b68685a58584a3330292821202004 0x3f453fa97f6853f810f083bf4973ca54f04a3b828ec093a345e40db8150dc1735844d00d3624dd68d74b4ad091b6b47d411b3836ca4e31854c4d7f0b47504db0036 8 255 3 7 11 2047 18 262143
def cc_67_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xd4350ccb30cc2a98de307d1f07c1f0749d06c9744d1304c09a2408120044100310c0300841104001 0x2783c9d0c22a4d9f4be7127570bd302b4109c84239b06e6817a0976264d99541582f4b0ad00271f08d542d4a0a4f8251e084eb48934c02c44910b2542f940ae48279008d4c2f490acf4271d08e5e38968d63e348e4e234388c0d1482f480acf0271b08e295089d5623457d8dd883b864a20e46808d60246 10 1023 4 15 10 1023 18 262143
def cc_67_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x3c7054100 0x16c2f4f0ad18272608e8a35590bd382b4409c90234d0a48c21 7 127 3 7 10 1023 18 262143
def cur_67 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_67_5 (Nat.sub p 160)) (cc_67_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_67_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_67_2 (Nat.sub p 64)) (cc_67_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_67_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def hc_67_0 : Nat → Nat := unpackHintV5 0x7e034f3091d41237236624c0ac981293024a084880c91001160c22c004342471950e0031ba06374006e800d4091a8003500065848a328140062740c4b03896001141819890082b0001000000 0x270cf1c9c33c76e39d436c0e79e12e70cf1c35030c30eaaa800000155555000f3cf3eaaa80000015555500071c71eaaa800000155555002767679c2d9e12c33cf0d6aaa8000155558279e782d9e12eaaa8000001555556000279e79b9e6e4baaaaaaaa0255555401aaaa00000055555566700043553d54755559040001500000000 19 524287 8 255
def hc_67_1 : Nat → Nat := unpackHintV5 0xec0739e12d80fb540cd5003480cbd152ee06b803ae000b5032d400b381ab816ac81aac06a783a9e00a78029806879ea120c758f0dcfa2b0c0a20a1e0a86c0c19818481e0d8480036 0x3c39d278db9e73c31c32c3812e79cb9cb5d70cf3c32cb96002cb999e74b9db9e79b4b9db9c2e75e5e5e5e6db6db102d2d2d2cb691a00b64f2c71d40b0b4b64b0cb3cb2cb0cb1cb2cb2c75e5e5e5e54000000002c002d2d2d2cb6aa5667009e70cf0d4d1c9d679c33c71d49cf9e70cf1db59c6e782d9d3d0cf1c 18 262143 8 255
def hc_67_2 : Nat → Nat := unpackHintV5 0xa3d509606e7b4d676428764007381673800714126bc2c6b0066940e688066442259c54438b24001c3b8243a00c394063542033c0c330062e028168bc1102c110000a83408014080000680c0242200012 0xb0cb3cb2cb0d31d31d55d34d72d72e2cb2e1d75d75c700000000002d4cb2d1c71c71d51d9cb572cb400033cf0c7a1d34c71d400147675551c71c74d34d31c71c70000005555476755004354f547595500005670cf0e4e9e71ea70cf9e78f833c2d9e70d9e79e0e84b9c33cf0ea66800b4b4b2e82aaaa0ea3ea1eaa540000000000b4b4b4b599e968b0009e70d4d9d2e71d5d9cb9e789d74f670e79e12e70d5d5e5e5e5e00000055555d66755004354f54755754b4000159c34cb0c7279cf0c72c712e79c6e76e79cb3cb09e1b9d 20 1048575 9 511
def hc_67_3 : Nat → Nat := unpackHintV5 0xf221377010baf845b3922d1c4064a2230510176860b30425233aa748e91492e84c2c3b7379a79a0aa94a554002910c948800a1c144b62c25b001298208a4543886516231061a7c30c00156180940b8360a0000d8 0xd33d39e1cf0c31cf0c77e73e79d5d72c79f0d33d33c34c74c7aa4d34e1c71c71ea1e9c000000000174d35cb7d5cb475d75c7975e000c30c3aaa80000000c30c31c71c7aa001c71c7aaaa1c0000003cf3cf1c71c7aa001c71c7aaa8aa02024d34d31c71c7aaaa1c71c7aaa8000000555555001c71c7aaaa82cb2cb1c71c7aa000000001c71c7aaaa87a783aa3ea87aa00000002000134d34c71c71eaaa9a2e400343430c30d797834c00b4b430cb2d50c30c30c30c70c30c30c30d70c30c3835c3935d74c00000000010d9c30d430cb2d2d2d2d008b2e1d34c73cf5005535550cf3c30cf3c34d34d3000000436755554d55004b51d54d595500005433cf0c35cf3cf0d34d34c4134d34d75d75c344b532cb4b4b430152d32c72cb2c70cf3c32d72e2cb2e0d73cf3c34d34d300000b000000030c30c3543672d4cb2d2d2d003c39e72d5f4783679c30c30c30d67e4c0010d55676743a0c77c70c35d4001555430c30c30c30d35d30000005543675555004351d556554000151c71c74d34d31c71c74d34d3015d75d72d2d11c71d2d2d2c01c71c71c31c71cf1c35534d34c71c71d71c71c7875c78000001c000002d2d47671c751c72cb4b40274d2e70cf0d672d9e4b4b9f0cf3c38b2e5df50055554c74c74d35c75c7000000554d4767555540010d53d52d655400015 21 2097151 9 511
def hc_67_4 : Nat → Nat := unpackHintV5 0xf92007c9003e300df0c06f80037652db6327da207cc844663f01b1e00d8f000c5e0d62f00311035740a4ae45e5341f26f1590d1548500c402131e70d0ce12c5ec422813a8ecaa06886e26e6b0a04b8378c4000de 0x279db0c71c0c70cf3cf0c74d31c1c00c1b6c33cf0c74d31db6c71c70c30c30c71c30c79cf3e3cf3e0cf3cf0c74d31c00003c0000003cb3d3cb3d0cf3c31d34c7000c30caaaa0000000c30c31c71c7aa000c70e831e870c30c31c71c70c3000002d2d9e73c31c9e70cf1c0c30c31c0c30c31c71c700000000c30c31c71c7000c30c0c30c31c71c70030078db8db0c30c31c71c76e38db0c30c0c30c31c71c7000000555555000c30c0c30c31c71c70c30c31c71c72cb2cb000000000c30c30c31e70c30c31c30c30c31c71c70c30c3830c380000000c000000c30c31c71c70c30c3430cb0d001c30cf3c30c31c3a0cf03c2cb0e0e0c30c33e3e0c34df002d2da830c30c30c30c70c30e0e9c30e830cf4e80000000000030c30d70c30c3432c3535d3975e000cf3c3a2aaa20aa020cf3c34d34d3aaaa0cf3c383a7aaaa4e8fa1ea4eaa00000002000033cf0d34d34eaaa62e402a3d33c73cf3c70d33cf3c30c30c30ea0e9d3934d3800000000000f2cf4f2cf435cf3cf0d34d34e5d780030c30c30ea83a7aaa0002d2d4d70c30c3aa83a7aa83a1eaaa8000000000030c30d35d74eaaa62e40071c71c70c71c73c70ea4e4e87a71c7a1c700000000004d34d31c71c75c71c71d1cb1d975e000cf3c30931e1ca9c00b4b475d31d31ea93a1e9eaa0ea3eaaa00000000005d34d71d75c7aaa98b900 21 2097151 9 511
def hc_67_5 : Nat → Nat := unpackHintV5 0x41140670d8354c80e2e0000e 0xc30c30c79c30c30c30cf0c30c34c30c30e0d30e1d34c700000000000c30c30c30d0cb0d1d34c7001c78f3e0e833cf1c71c70002d2d0c31e71c70c31cf1c30c30cf3c31c71c71c71e1c780000000000033cf0c71c71c71c7472c740078783838f3cf3d34c00b4b43e7 19 524287 9 511
def nh_67 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (hc_67_5 (Nat.sub p 160)) (hc_67_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_67_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_67_2 (Nat.sub p 64)) (hc_67_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_67_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_67 : Nat → Nat × Nat := unpackForestF 0x169f448d405a5cca5d9a25f3a0f274184d1279a0373405e64a800b478c471188d64017c802b932612009e4416480238c469184e2301c46034016871454221aac43450149f0c4a0052580a478348c0290c051fc024601476f914df12fbe0430146eec971d92a3b12876050ec0900519ba3450109ee40d80425b81500108edc1719da3b5a4d6b46ace119a1a5342466706c0210d949c0083f630a8c0d7d81a3b003601076020dd741b00833518beb4911462daba6c572c0a315d4da229a4453290a314d45230082f488be9116d31b626260488ae92d11252424453010565117d15a41445b416c0844f104b0144573d6907a910f4a414453398bc74d10e6291434a2b69e56d2cd4ae15b4732468644d0ada19594f2b28e564fcb22c164502b26e504c0a4981404a0104e0517c94220145b206d84409081301006c028ae38d1071240e044028a604170082a0104c126bc24d6854a8093561327024d48082304b4f096961a97034a804b470a468144e025a1810440369e06d2c0da38223403686040b004118001f 8 11
def ch_67 : Nat → Bool := dagCheckNodeV5 m_67 g_67 ep_67 4 15 bds_67 164 (dagTraceF m_67 s_67 8 f_67) cur_67 nh_67
set_option maxHeartbeats 0 in
theorem rc_67 : dagCheckRootsV5 m_67 g_67 ep_67 4 15 164 bds_67 (dagTraceF m_67 s_67 8 f_67) (cur_67 0) (nh_67 0) s_67 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_0 : treeBlockF 0 32 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_1 : treeBlockF 32 64 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_2 : treeBlockF 64 96 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_3 : treeBlockF 96 128 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_4 : treeBlockF 128 160 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_5 : treeBlockF 160 164 ch_67 = true := by decide +kernel
theorem nj_67_1 : ∀ i, 0 ≤ i → i < 64 → ch_67 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_67_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_67_1 h1 h2)
theorem nj_67_2 : ∀ i, 0 ≤ i → i < 96 → ch_67 i = true := block_join nj_67_1 (fun _ h1 h2 => treeBlockF_at nb_67_2 h1 h2)
theorem nj_67_3 : ∀ i, 0 ≤ i → i < 128 → ch_67 i = true := block_join nj_67_2 (fun _ h1 h2 => treeBlockF_at nb_67_3 h1 h2)
theorem nj_67_4 : ∀ i, 0 ≤ i → i < 160 → ch_67 i = true := block_join nj_67_3 (fun _ h1 h2 => treeBlockF_at nb_67_4 h1 h2)
theorem nj_67_5 : ∀ i, 0 ≤ i → i < 164 → ch_67 i = true := block_join nj_67_4 (fun _ h1 h2 => treeBlockF_at nb_67_5 h1 h2)
theorem nc_67 : ∀ i, 0 ≤ i → i < 164 → ch_67 i = true := nj_67_5
theorem lb_67 : LowerBin m_67 s_67 g_67 9 :=
  lowerDagV5 (kn_cons lb_46 (kn_cons lb_43 (kn_cons lb_10 (kn_cons lb_49 (kn_cons lb_48 (kn_cons lb_44 (kn_cons lb_50 (kn_cons lb_13 (kn_cons lb_2 (kn_cons lb_45 (kn_cons lb_18 (kn_cons lb_14 (kn_nil))))))))))))) rc_67 nc_67 (by decide +kernel)

def m_68 : Nat := 0xffff0000ffff0000
def s_68 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_68 : Nat := 0x117000013170000
def ep_68 : Nat := 0x1200000000000000000000000016000000040000010600000206000001120000131200000114000010140000
def bds_68 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 7, g_21)]
def cur_68 : Nat → List (Nat × Nat) := fun _ => []
def nh_68 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_68 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_68 : dagCheckRootsV5 m_68 g_68 ep_68 1 1 0 bds_68 (dagTraceF m_68 s_68 7 f_68) (cur_68 0) (nh_68 0) s_68 7 = true := by decide +kernel
theorem nc_68 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_68 g_68 ep_68 1 1 bds_68 0 (dagTraceF m_68 s_68 7 f_68) cur_68 nh_68 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_68 : LowerBin m_68 s_68 g_68 8 :=
  lowerDagV5 (kn_cons lb_21 (kn_nil)) rc_68 nc_68 (by decide +kernel)

def m_69 : Nat := 0xffff0000ffff
def s_69 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_69 : Nat := 0x155700001f7f
def ep_69 : Nat := 0xa28000000000000000000000042000000600000040200000e0800001002000010200000155400001040
def bds_69 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_37, s_37, 5, g_37), (m_40, s_40, 5, g_40), (m_8, s_8, 4, g_8), (m_22, s_22, 6, g_22), (m_39, s_39, 5, g_39), (m_7, s_7, 4, g_7), (m_36, s_36, 4, g_36), (m_32, s_32, 4, g_32), (m_57, s_57, 6, g_57), (m_16, s_16, 5, g_16)]
def cc_69_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9a04d02489240900c8023831c08e04312103080820c101f06f807c03e01d86b0f5802c01504a805402a0140490448023040c4001 0x1015c0f9540f14c0e9340db480c94c0bb500b3400a140071300993c099440a2540914c0893407a5e07246069561b45f1ac5b18c571645315b5a143421315f1295b109570e1530d14f0c14b0a94708143061310496c0314c0345602b560545b04457039560214e01242b3b4fb334bae347a9b43a8a4fa724ba5a47a2a439b23f9923b97a37952339394f9214b89947851438413f8193b80937711336f12f6092b5a127551235484f4b84a48847388463483f338371c02f058270181f008170001f 13 8191 6 63 11 2047 20 1048575
def cc_69_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x90e408c6308c20347d103c8f03c0f03c0c3300c0300c0210802008014c500c8300c0300c00300000 0x20a5480511f9347ad41e25676939d156cb17f245bc115edc53b495ab24ea857e995b9e55e51539053e294b8651df143724a5bb5854d01a360665b1916060d217a445c5216944551794a562c5153b581e4c1246c471811360 10 1023 4 15 11 2047 18 262143
def cc_69_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xd0d0d0b4b0b0a9a8939089888881806460606060444032303022190a08010000 0xbed12f244ba522e144b2542c456aed5a3949aa951e928a51b28c60a09b1e1289c572695498512593492911d9288ed72313484502225c82502124c 8 255 3 7 11 2047 18 262143
def cc_69_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xb02c0b0284a0280989bb6c1a1681a05ccf83c0f03c0d2340d02c8741c06118051140501404101000 0x7e8c9f52d7c0c9d81a7a941e54487d4a1645848f60d52754aa085e80149fc457b111cc2a78099d844754c9d03e730ca3e438e4f635378c4d6292f8810ddc237206dbb6c6c4e1b2566b559c3566f56db5576a4e5a14166951664c639b1624c625b18560 10 1023 4 15 10 1023 18 262143
def cc_69_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x84210841e3781d17415854150541504c903400d3340d0304c024c9018c5114032084110401000400 0x27a429d53a71429a53aa24ba791e963fa38ce7d339b4ae65239811a516c935525b51955464933870c64029800861423840c62c29730860d32890fa00327e112185c79091f4447c1120424 10 1023 4 15 10 1023 18 262143
def cc_69_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x91482412082402010075ba17cb85c28d40994c26106802b1249048240cc6029140a04204 0x2e4a85f948bd6a178d02eca85c140b949b70916dc9ee0342be49f7491ead1edb142b5079645b2c0aa5714cb068b5d15ab5ab4d05ab38b76315ebcab5614eab25d3216a602251141a6273384c69094d083ca269b3c8ea709d50136 9 511 3 7 11 2047 19 524287
def cc_69_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xb07602c0542a81486714e09c1382704a294110e2042184108200b656c0d81b03606c0d8162ac04c614401000 0x1c293b81266fa44dc2d98e533392866a40c5299aa8eb511b6b351d36a1a4577409abb044ce69b9ad1730ab4f05a750ad8f15b19ab62a459d0b4e815af49b4e05a730adbb16f6e2bed357d969fb0d1f5d2d68a56cf49d9690b28abe4956c829f8853b0ca3e11429b0b4e415af1a2dea36 11 2047 5 31 11 2047 19 524287
def cc_69_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x8417c47257206c36825c65c05a15a05814e54e04c14824804424404213e23e03c13c03c03a12a82a0281014000000000 0x21844fe5b3d554e94d21454ce8eae636f455a885a8415b363ab88dbed4df24b7bd25f98f7c52fee49d042f1409f90177f151f444f5917d23dcc4aa4c457b113cb4cf1952f534ef933b43ced513ba54ec131e444e7153aa5ae995a805a7815ba03ee60c9002d110979354ffd6ff757fcd37eb45f89132e3ab68dbdd5af655fcd56f04ff093aeb4df95369f16a485777158f83f100df8c17 12 4095 5 31 10 1023 18 262143
def cc_69_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xe0b80c9b20c8320c0b00c0300b4e3a849f27c1d2741d06c9b04e130394e0344d0304751842408002 0x1a89447c4c904771e8dda695474372885e2309e35b6465388bcd9169522a9448f5c90ea31cd42372ec623f8a466d14a8da1f93c2f1084e4e0bc40139342f0f84e4c0b43a12c382f8684f1253222a24413c87a6d0c4d0941f870378582904d3a131ab3d2a2405e1a09e0ea32f5368369b054da08971143f0c06ef95020526be1302185e1509dd4a240134 10 1023 4 15 10 1023 19 524287
def cc_69_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xec7d83b0760ec1d8362ec0963282504a088700a00346642c81902c340c80100184300600538620c008800800 0xa1b5da11519f9508ca565fa369c9565305a45856a245a9f4569eb579e3569da579315b8c157831497e1419d13b9c1399b937611316c92b5f1275285a450569a9299a128999245da365e93696a4d989417d1316c12b5d1279804c8b1458aa56961565205a9725696a4e9295b8a157959295185a94a45940442a02f130279334f92b436ba3a7b9423784f2983f128372902f12027912356b12a6a938 11 2047 5 31 11 2047 20 1048575
def cc_69_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xd42f696a508ca308c2127c9d274158541324c1303d0f03c0781c0701c0701c025080200802008002 0x4fe3db0a5f5f49cc2178c827af02f659767d1ed915cb12a35d541b695ac5233005e3109c100f97c2d1784b590beb0139742f1704e5c07c5a0bd6e38ad46b578d2ac9c55534aa0685b0bc5813a3854a908950939fea1d3d29540b54dd46771fd31517ea66da4ad4e2523446460894a932932252128a3a49460928296d0125 10 1023 4 15 10 1023 19 524287
def cc_69_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x9090743f382a281a111002 0x2d322da0443285e3609e8926bdd316ea56b348cc8178d4270503e6207c660bd0b4db1a6d41d3281265803c 8 255 3 7 10 1023 19 524287
def cur_69 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_69_11 (Nat.sub p 352)) (cc_69_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_69_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (cc_69_8 (Nat.sub p 256)) (cc_69_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_69_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_69_5 (Nat.sub p 160)) (cc_69_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_69_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_69_2 (Nat.sub p 64)) (cc_69_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_69_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def hc_69_0 : Nat → Nat := unpackHintV5 0x9b4153284253124a0069043d1f01a2f0f45e008b00d110521909432008640109832060d40a028080cfc051cd2b314865d850ba809631225a6c4a80c94808fd2c13ac01d4a00c2e8001800000 0x23a538e353088c7232d70638e38d4c0b8d310b638d38c78c13231c132d7234d3093972cb4c00070000000200b0000000100000070000000023008d72d70f2363530b0b8c0b5cb5c010d0c30c00c80030011357978000134d1d1c070000030c00010d0d4d4c000800002c000001c01c000000123000030c1420c38001543000030c30c000000c0802c00000555500004030000000001231c71c71c71c7 19 524287 8 255
def hc_69_1 : Nat → Nat := unpackHintV5 0xb68bada00b6802da00b680288527ca59f00274081b41c6b819a806688198c16608296e145a01956124b8a0d25c34008c0101c938700215070381c0c8182c0609818141203818000e 0x5cb4d04c8c1d34c24e5cb2d30001c0000000200000b0000001001c000070230000001e8c22c7238c3c5e38e38e30b23238b5e8e32d78e32d7081c8c0172cb5c014d4c1c00001c823535c25e0005d4d4c70000106347238c304e38e38c48e38d4e3 18 262143 8 255
def hc_69_2 : Nat → Nat := unpackHintV5 0xf90af606f306e51caf6caf00af00af008a4a89027c1a662c63065f085f00511c4e064b064806430a351c3500271c27002700152415000b140b00040e01060002 0xa8e38e3201c8c0b5cb5c0014d4c1c8007001c01d79780001753531c000508c7238d344c323078d8c48d078e38e3a8e3088c7108d1c8cb8c2c8c704078d8e31c 16 65535 7 127
def hc_69_3 : Nat → Nat := unpackHintV5 0xb18056280ac20352e56a44194701a890549a789280d2183a430047e0883cc0e91e99e343182462c04bd88178032ee0252cb071b40b330088de10c041b0681e1803c0006c0c0a830031200006 0x14b1c7833db6cf8f0d2c3430e31e326c70cfa0cf0e92c3430c20e0c394032cb2e326c0c00030c308d0020c38b2c4071c73c23cf80200f030830e0cf0c0c087873cf0005353072001c01c08d344c3234b5c48d8d74135d30938751c000700000b3cb3c800070000000000f3d72cb5c0100001c007230000000000f3cb2c23cf91c740007000003c08b2cb2c070000000003cf3cf1000b2cb2c00070000007230000a3807238d72d70f01e38cb8e30b0b078e3 19 524287 8 255
def hc_69_4 : Nat → Nat := unpackHintV5 0xdbc1db78036f006726cce4018b912e63152aa2964f10e9e21c01414247a484b93b9720028460450b869a088b481160016cc02d8002b30050060a0000d86816050220a0341006800080500010 0x2e3030c318d20c38b2d40070c71c71c06380c0b003001c70200aa000000000aa0c30c3008f3ea3cf830e0cf0c30c71c71c71c71c71c70c31cf3e1c780000f5d4d4c701c2307000030c34c10c3572cb4c00030042310001e38c31e32d7530c13878c1c1c070b0023cf8000000000400830e0cf0c000007072230070070000003007072c08cf3c2e1c78000000f50802a80080000aa0c30c30000022cf2cf8f3e808808c3d0d0e0c380c000f6cf6c008000003c0db0db000cf0c00301c0f3c023cf8000232c2c3d40c010230c30c050c38b2c00103c30db1232c07a1c0e4b 19 524287 8 255
def hc_69_5 : Nat → Nat := unpackHintV5 0xe4865c70238b0371006dd44db802b6e026d408cf0b9841a28e7a4f4289e4053309a5c0a44a6e87c190f009f72738c625c1588a2e0e52f152782a400379d06f0009a44120142400045030008a 0xb5d2d4e36307078e34b4b101c1d234630c364b5430d4c30d500c3500c30c3000c00000000555500000c30c35435654b543030c3015435555001418c0c3030c1c1c45051c7000418e35cb5c3c63538c2c8b238e302d72d70c0010d0c30c06300030234d5e5e00004d3535300000354c234830e5cb2d3100c0000c300004343535300063200000b000000000000000022a803c2c0000000002a800c4030c30c0088c00000000088c03e0f0b000c0d001c1c700b3cb3ea2233cf43430c31c700071cf3e3cf80b232c2cb3d4071c71c71c0b2383c3c01001c71231e8fa4b0d0c3830e500cb0c71c71c31c71c7 19 524287 8 255
def hc_69_6 : Nat → Nat := unpackHintV5 0xaf9854f8fa9e0150a329bc592b8c23e19416667fc30ff801ff003de207b00ce80e1cf013584669818d0829970a2c66854c408e9b10c11212064200481030d52d188222947c19398062c0000c 0x30c30c003000800c0002c001555418c00100c000000000008c3538d72d73cf4d8d4c38cb2d32e3538d0da6d234d8d72d2d4e3538d2d4cb07838d38b2d5434c0e30c82030c232cb3e8b3d430e343541a2cb500c3430d0d3428b2d50c3048c6318e32c30e932cb4cb54d44e34c2c0b00538e4c3530cb5cb5d1036d1030d41c1c30d348d34cb4d8c75e5e4d35d1134d1071c1c1d138d72d3936e5d34d34c1c1c30c30043435353063500e4db0e4cb2d35400703070700040701c701c70c35e0c3944c5110c307078c7 19 524287 8 255
def hc_69_7 : Nat → Nat := unpackHintV5 0xeb400e3042d6864d5808c6878c102caa0b89948692c348e0268b814734c27340070c146c4246c4006901a684066840062430624005fc145f0065f0005ec025246450c0c4f00e289341b8680e06c00070 0xb5e33d4c30d36d38a2cb3cf575d574105e35c2cb063a3cf2d73cf4b2d4f3cb02cb3cf2cb0a50c37df0c35560c30c355430c30c30d5f8d34c30c30c30d5471d31c7a5cfa4b0d0d30c34c30c4db033c30c1c1e434b3c3930d2c8e33e30c38cb8d4c3a60d63e0e36c6c0cf90d3c32e0e0e34b0d0c307070c30df638d74b4cb531f634c78d2d72d4c4d31d7a34c726db90575d34c2c2d34c07071e31c7070c33cb0c30c35cb2d74f0d0cf52cb4b54d4c3930e544d30b2cb0c70d71cb1c71d351d3071c1c70c30c3830e00000555500c00000c30c30000555500000c00000000c30c3000c0055550000c0000000 20 1048575 9 511
def hc_69_8 : Nat → Nat := unpackHintV5 0xce00a66d01b119297b46cbd8015e901aea05574c02b920a5c3032d9045500e49f0484a82823d0b90c09485a03426039eb140ea05c64c822e62012da2c9600645e291e3260d38f0399821543c0204500e01000038 0x5cb478e0c3a0c3975d5594f5555830c30e5c71c71d540c30b5cb5c30d511430c1c1c71d5cb5d578e33d48e38d78cb5e3128d50d4b555830e51520c38f3d55566353d55551511e0c30c3873c71c755a9aa3cf3cf6643434343aaa3c73c71c70d436aaa2cb2cb69a430d0cb4343aaa2c72c71c70d43aa000066434300080000000413cb2cfaa3cf3cfaa0cf03034343a07071c78d4e3aa6a3cf3cf69a430d0cf4343aaa3c73c71c70d43aa000066434300080000000aaaa3cf3cf5a663430d0cf4343563ea8baa2aa883aaa8f1cf1c71c350e2871e8a830e0c313170c355d744550c307071c70c30c30c36543550c30c35cb2d75451550d2d8d55555430c30c30d71cb1d11d1471d54ba2cb3cf52cf2c172cf3c23cf850f3cb2cb2cf3cb2c4c4d34cf3c1c1c71c30d72d0d2d54d830e51312c30c1c1c30cb2c30c33cf0cb2cb2cb433d3c34b6352cb53530e2cb2cf0e54b0b2cb2c2cb0c73cf3c32c72c71c74d472c1c72c1c70c3830e0b2c2cb50d52d4450c30707543560c30c30c352c30c30d4542cb2cb50d555552d550c30c30c3454472c72c71c755078cf5cb0c34d04c 21 2097151 9 511
def hc_69_9 : Nat → Nat := unpackHintV5 0xdbc266ca0a3480e99d038cc61166200b188c588022b368555b2028a919374708d4734361a1f9110ce97060a352d01a967804aa04e4945e21a180f80a8608dc2c61f15109058284190980b8080072a80001c00000 0x2cf2e80b2cb2cb503cf0b5e5cf8cb5cf883cf2c2c3db2cb535307073cf2d78f2e9b8e32c8d75d32c54d74d3938502cb134c71c1c1cb138d7572cf2cf3e5db3e00f00b232cb02cb2cf3d72cb5d755c01c1c0701c071c071c001c1c0f3cf3cb2cb2c023cf92cb4000f00000b2cb2c00000f3cf3cb2cb2c000f0000000030c30c0030015554000300000000b2cb2c00f02c8c00803c02c00f3cf3cb2cb2c00001003c000000000003cf2cb4e3cf9044c2cb3cf0707003c2cb2cb000000003cf3cf002cb2cb002e2cf2cb2e2cb3cb2cb00f0f3cf0b2cb2c02c8cf3cf3cb4b2cb4b2cb2cb2c01cf0f1c2c1c701cb1c701c0700070708f8f3cf00002c8d4d4cf000f00f2e3cf80232c2c2d753533c0004135d30939754c0000002cf2cf00000b232000003cf5cb2d7000040000000000000222cf2cf5a3cf4494f50707a080aa000000005500550066a953d2d6a95143cf3cf6635555553d56aa91471d453c73c71c7558e33d34b5c34c34e38d344c320c3a0c38f3d98d690cf430d0d0c35430c32c30c30c0db0c30caa0c30c3873c71c70d430c0c30c0c7830e830e2cb2cb555555830c30e2c72c71c7555707830e830e55cf3d75c192d3d552d55430d71cf1c1c1e33d 21 2097151 9 511
def hc_69_10 : Nat → Nat := unpackHintV5 0xf620374934348ae197c64c2a4a61201b048256b4b8ab254519202738c91651c84e323b03b9bb0e8cf0745b06428c261211286c5222fe3214b1a08c8c83b458172340543280e8dc06806024080120000900000024 0x8e8b2ea3cf8b2cb2cb8f3e0c38b2cb4d3873cf3e2c72c71c74c71cb2cfaa8b2e8b8cb2c2cb2c8f3e2cb2cb2c32d2cb0d2cb830e0c32c30cb0c32c1c72c1c7873cf3e2c72c71c70c31ea80002a830c30c00200000002a08f03ea8f2cb3e830d0d0c30c30e81c1c71e32d78eaaaa8f2cb3ea830c30c30c30c30eaa8f1cb1c71c30c30eaaa8f2cb3ea830c30c30c30eaa8f1cb1c71c30c30eaa955556a8f2cb3d56aa8f1cb1d5471ea820000000002a830c30c0002aa8b8ea8faa8f2cb3ea8a8aa0c30c30c39a0e9a0c30c3aaa3c72c78a1c7a2871c30c30c202a800000002a80030c30c000aaa8f8ba223a0a6cf0f2aa60e6830c30c0c3028882871c8a07070003033cf8f3e008cb000b03d753533c0000c30d308d10c3572cb4c00400c0008f3e22300003c1b000b0020c3833c3000c00400000000000003cf823d75cb2cf8e2c3e83d753533cf1c707070c30d3530d8d0572cb4c68380d30c30c7070700f2db6cf2db8f3eaa8088c3cf3c0d6db0d6e0c3833c3030c30071c071c07081c1c000c1ea80002a830c30c00200000002a802002a830c30c00200000002a80002a830c30c00200000002a802001555400200000002a8000002000002a830c30c0002a80088c0080f002c002a830c30c000030402000000001c00008f8d78b2e082cb3c8cf14f5cf3c2350e3a2cb433cf 21 2097151 9 511
def hc_69_11 : Nat → Nat := unpackHintV5 0x9dc6c914646ed144196a33074200981d81404cc6028120280000014 0x20a8b0b2a8b2d0d0c30c30e81c1c202a800000002a80030c30c02aa2e3aaa2eaaa282cb2cbaa9839a0c30c30c30c30c3aaa8a1c7a28b1cb1c71c30c30e8b8cb2e8b2cbaa3cf8f2cb3cf3db3c3cf3c830e0c32c30cf0d3cf0d3c30e1cf3cf8f1cb1cf071cf071c71c30c73c3c882cb3cf2cb535307073cf1c75555830e55830e2cb2cb55830c30e2c72c71c72d307a2e0c383432c3432c34c34d0c35683913032c30d30c31c1c1c32e34b4c7 20 1048575 9 511
def nh_69 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_69_11 (Nat.sub p 352)) (hc_69_10 (Nat.sub p 320)) (Nat.blt p 352)) (hc_69_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (hc_69_8 (Nat.sub p 256)) (hc_69_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_69_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_69_5 (Nat.sub p 160)) (hc_69_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_69_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_69_2 (Nat.sub p 64)) (hc_69_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_69_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_69 : Nat → Nat × Nat := unpackForestF 0xb4245b404400b4f00b4baea5dae95cb1936ae951af12fb003caf127af017ae95000b47aa238aa235ac02fac027aa234aa138aa134aa03400b43a904400a4fa7a4ea792900a4ba6351a615100a47a324ca3244a3128a3124a302400a439bc5a9fb5d9f951a012da01259f9509bc569bb579bb569ba579b93b9c9569b9399b93700a3f99929999289992400a3b981419804c00a3795a5695a4e961569592900a3394245940440094f92b4f92b430094b8a35c912358a3518ea3b8f84c8ea378e8378a3508a25d8cb6c8c9388a23f8aa6c8aa548a9288a233009478594c859448593c859368682f8682785934858140094384a350093f839468234d821368212e0093b8124d009378013471b5b7f16c71b5771b4d7d94d71b457ca3d71a447195a719577a2457a23d719567934c78a547193f77a4c76254769447604c719377325a732567303e7385473032719367235471817009336fa4e6fa4c6fa440092f6145b6e16c61457613576134f613476125a693516a23a6a236693506915d61256681356124e6634d66345661566124261157611566114f62c5662b5662a456114e61147611420092b5ab425f9485aa4f5db505db405d9505aa475ba4d5ba455b93d5a9425a83c0092755c5b5916c55c57583455595656c5656b565594e5592e009230084f4c24b4c247531394c23f521294c2335034d5083c501364c1334e2424e14e4e1424c12b4d14e4c1234c0460084a49351491514996c49954491330084748029392433913d3913739135458293912f4483e390433c3524305c3c2453c23d3c1523c05e408243c0523c0453e2323e12d3e0323c0443ca503c9443c026390233b044399323983e398323901b00846353563515b3736c3515735a5635956351390083f3414100837332541cc5f1cc5b30a6c3096c309601cc572e3442e2442e1482e1441cc531ca562c9502bc562bb561ca4e2aa541c95f1c95b2846c284602826c1c9572595c2595425944259341c95324a441c94f2335c231341c94b2225c1c9472124c1fa541f9441f9341c9431eb501d2561d24e1d1561c9290082f1bb580645f0645b193601916c191600645716b4816a441694816944064530635a14c5e14a560634213b580615f0615b1146c1146011360061570e95c0e9540e94c0e934061530db480614f0c94c0614b0b3500b3400614708a54099440894c089340614306a5e06a460695606131008270245b0496c024570215602c5602b560214e0081f01242008170001f 9 11
def ch_69 : Nat → Bool := dagCheckNodeV5 m_69 g_69 ep_69 4 15 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69 nh_69
set_option maxHeartbeats 0 in
theorem rc_69 : dagCheckRootsV5 m_69 g_69 ep_69 4 15 362 bds_69 (dagTraceF m_69 s_69 8 f_69) (cur_69 0) (nh_69 0) s_69 8 = true := by decide +kernel
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
theorem nb_69_5 : treeBlockF 160 192 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_6 : treeBlockF 192 224 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_7 : treeBlockF 224 256 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_8 : treeBlockF 256 288 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_9 : treeBlockF 288 320 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_10 : treeBlockF 320 352 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_11 : treeBlockF 352 362 ch_69 = true := by decide +kernel
theorem nj_69_1 : ∀ i, 0 ≤ i → i < 64 → ch_69 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_69_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_69_1 h1 h2)
theorem nj_69_2 : ∀ i, 0 ≤ i → i < 96 → ch_69 i = true := block_join nj_69_1 (fun _ h1 h2 => treeBlockF_at nb_69_2 h1 h2)
theorem nj_69_3 : ∀ i, 0 ≤ i → i < 128 → ch_69 i = true := block_join nj_69_2 (fun _ h1 h2 => treeBlockF_at nb_69_3 h1 h2)
theorem nj_69_4 : ∀ i, 0 ≤ i → i < 160 → ch_69 i = true := block_join nj_69_3 (fun _ h1 h2 => treeBlockF_at nb_69_4 h1 h2)
theorem nj_69_5 : ∀ i, 0 ≤ i → i < 192 → ch_69 i = true := block_join nj_69_4 (fun _ h1 h2 => treeBlockF_at nb_69_5 h1 h2)
theorem nj_69_6 : ∀ i, 0 ≤ i → i < 224 → ch_69 i = true := block_join nj_69_5 (fun _ h1 h2 => treeBlockF_at nb_69_6 h1 h2)
theorem nj_69_7 : ∀ i, 0 ≤ i → i < 256 → ch_69 i = true := block_join nj_69_6 (fun _ h1 h2 => treeBlockF_at nb_69_7 h1 h2)
theorem nj_69_8 : ∀ i, 0 ≤ i → i < 288 → ch_69 i = true := block_join nj_69_7 (fun _ h1 h2 => treeBlockF_at nb_69_8 h1 h2)
theorem nj_69_9 : ∀ i, 0 ≤ i → i < 320 → ch_69 i = true := block_join nj_69_8 (fun _ h1 h2 => treeBlockF_at nb_69_9 h1 h2)
theorem nj_69_10 : ∀ i, 0 ≤ i → i < 352 → ch_69 i = true := block_join nj_69_9 (fun _ h1 h2 => treeBlockF_at nb_69_10 h1 h2)
theorem nj_69_11 : ∀ i, 0 ≤ i → i < 362 → ch_69 i = true := block_join nj_69_10 (fun _ h1 h2 => treeBlockF_at nb_69_11 h1 h2)
theorem nc_69 : ∀ i, 0 ≤ i → i < 362 → ch_69 i = true := nj_69_11
theorem lb_69 : LowerBin m_69 s_69 g_69 9 :=
  lowerDagV5 (kn_cons lb_2 (kn_cons lb_37 (kn_cons lb_40 (kn_cons lb_8 (kn_cons lb_22 (kn_cons lb_39 (kn_cons lb_7 (kn_cons lb_36 (kn_cons lb_32 (kn_cons lb_57 (kn_cons lb_16 (kn_nil)))))))))))) rc_69 nc_69 (by decide +kernel)

def g_70 : Nat := 0x117155713171f7f
def ep_70 : Nat := 0x12000a280000144000000c6800160042000400600106040202060e0801121002131210200114155410141040
def bds_70 : List (Nat × List Nat × Nat × Nat) := [(m_65, s_65, 8, g_65), (m_69, s_69, 9, g_69), (m_63, s_63, 8, g_63), (m_66, s_66, 9, g_66), (m_67, s_67, 9, g_67), (m_62, s_62, 8, g_62), (m_61, s_61, 8, g_61), (m_68, s_68, 8, g_68), (m_53, s_53, 5, g_53), (m_8, s_8, 4, g_8), (m_4, s_4, 4, g_4), (m_64, s_64, 8, g_64), (m_19, s_19, 7, g_19), (m_12, s_12, 4, g_12), (m_31, s_31, 6, g_31), (m_55, s_55, 5, g_55), (m_42, s_42, 5, g_42), (m_59, s_59, 4, g_59), (m_7, s_7, 4, g_7), (m_52, s_52, 5, g_52), (m_28, s_28, 5, g_28), (m_38, s_38, 5, g_38), (m_34, s_34, 5, g_34), (m_56, s_56, 4, g_56), (m_54, s_54, 5, g_54), (m_57, s_57, 6, g_57), (m_35, s_35, 5, g_35), (m_58, s_58, 5, g_58)]
def cc_70_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x92049023851428a044062010c1860410a0810408204101e88f407a03d01c88e407203805c00e007003801c00e00604213c0c0001 0xf46e074a20245f8082b80d144060b60225f8162880a45904daa824d3c1168607d6a03ab3010d340d68a0547002eb581359c088bc03c5b01a2980b148046d401b660bab78595ac2aace14563096378451ac1f8ce0e46306e2f83316c178ae0ac53040b70185780228d3d45f9de2dce715e628a72d35f961adca8d5e516a720b4f8fda5c6ed1e2b6870ea5f8392dbf095de24a6e424f6fd25b6a91d92486c423f5b51daa48dd484669315b3c8a99b052ca72863613b138998604ac012460003f 13 8191 6 63 11 2047 21 2097151
def cc_70_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x9c2709c2708d2308c2307d1f07c1f07c1b442d003c4f030cc024c902048020062180600cc300c003 0x1f4597ad55e34f76d0dcb5d70d559b4d6ed15ad6b6959d9c5e6514a656b9559e446b8d19e2c5f8716e0c577f14dd16e6c57989465e590796c5a5505946565f0715c1251949544f5a53164491b82154465110d71405f01944 10 1023 4 15 11 2047 18 262143
def cc_70_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x942328c2218821184210841c5701c0689a0681823a8e0308c0288a02449020453140411002208002 0x2fd71bc5f2e134b4552c47eaedfa997ea05b2b134a91669a43a35aa8251d55af3d63c8dbf136bbad9edb63b2d7eab53a45ba795e9a551a946965f1a14692512397c785f9c96c665722144845b1c15c765fa0144 10 1023 4 15 11 2047 18 262143
def cc_70_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d0524a4138a704e0945282504a094109210420840f0caa140204400800c21803003186008210020002 0x3f47e7d6fce65f9f09a3d37e722fcf15c9deb13ac597469ee690dc91db836f6f6badcd5696b7d156b9dacf3558e6237cb467958bf2715e41b7c736b8a6cf10d8e19afc1b5b7f6aef6d4de5a5bb347712dcda57944b635954692acd05519ab4ac352652c8c64d184ab30154 11 2047 5 31 11 2047 19 524287
def cc_70_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xe0c4c0c0b2b0a2a09983807270705b58515050503b3831302928281a18181803 0xa18f940df27db84f17c9c2ad3655266b4b815e97ae318dddd0bf3796c94ce4dc5724ab4bf352912c91e4d236b8c645f8b2f9124d21caa42b7e84269059ca06364016c 8 255 3 7 11 2047 19 524287
def cc_70_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0150aa0521a4138a704e09c1382324608c1182304608c110620440881101850941001082004000400000000 0xb62fd7c4d2f0ae5a97eba269711a6ddaadb23bb54675d1c2cdb559366b16bd60d4abd35d6a67ac4bf5694ea927d4a43d7ad7ad58f5237e946bcf8cf9b18f322fe5c53c96df8edaf15b3e1b63c26bf82d4efda7deb4bbb68f72d0ed0b754146a4cfd4c59292b751954 11 2047 5 31 11 2047 19 524287
def cc_70_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x84a1084210841d44e92148120445103c8f03c0c3300b128491240812006218042100310841104001 0x1c0d577d1deea6fdc4d7b699f6931f846fed8cfd6dbfa5b5f3b67e56c7c6d2f85a3ef16ed928d705f354b259954d3289a35c340be59144ce28962512c0aa65164af2ad904d318be56946c42695851aacab60144 10 1023 4 15 11 2047 19 524287
def cc_70_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xb02c0b02c0ac6b0a86a0a82a0a81ce3b8e0344d0340b22c092240721c052140320c0120400100000 0x7dc607ca5c8245e81c5b8145380c527fb5a7f3567ea5f7e25b7d2577c2537ba4f7b2437aa3d7a23592c5f91c5b90c578f4538e35f8d35b8c3578b35389b4f88b4b86b4785b438295e799467896477d707717c761646e9466e156751347417c6d9466d156731346f97e721347115c 10 1023 4 15 11 2047 20 1048575
def cc_70_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xd1d0bbb8aaa893908280806b686160595843403938383838380e080808080801 0x8f9448396c8e9547e9467e1568d9348c96c8315c7d1467c1568b9348ac6e7a9548a144891348814487d628715c7a144861348535d84b558234d8434583a5d832558034e 8 255 3 7 11 2047 20 1048575
def cc_70_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xa068098a60982429021384201801f17c1e1781d1741d074194641906416323862180421001304001 0x9f9549696c9e9349de709d16c9616c941569c1349b1449a1349915c981349534d9734596a59962519545e94c5294253a3c5fa2c5ba1457a04539f35f9e35b9cb579bb539ab4f99b4b98b4797b439595e939468516c8215c7f954921449116c8495c7f14490237 10 1023 4 15 11 2047 20 1048575
def cc_70_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xbc2f09a660946509064090222882114bd2040900400e2380d1340c115c41100310c0300481000400 0xb056eafd62adc6fab45daa455af347879633b94bae93badc52acc60abc72ab460aa450b5d6fb4d6bb3d67b2563b0c62ae452ad36fac367aab5fa9b579896b869637095b5d9533b13ba526ca8a54a7a56a7254a6459a556aa856ba6d63a5a6ea4a5e9796b859635c9539515ca3144a2670a196ca0944 10 1023 4 15 11 2047 20 1048575
def cc_70_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xb82b3ac292a427294a508ca308c2307d1f07c1f070cdf340b22c092240812008014c501400500000 0xc0356bfa56bf254be569b8a5ebd571ba26cb9a7eb826cbbe72b7a5cbac59ba365b9b4f3d13bb8b6fb835db7b55c356fc1d6bc0d67bed63bdc6fbcc67bc45fbb457b926eb725e9996b889637195b5e9533c94bb6468b0450b1c70b5458b4470afc60b3458b2b54b1d69acc65abc5fb135e3c14b 10 1023 4 15 11 2047 20 1048575
def cc_70_12 : Nat → List (Nat × Nat) := unpackCursorV5 0xb4b682d05a0b41682c0d80ac3582b04494a090110a20402800e11c0342604538a00c41803002204000400000 0xd0c69d0365cfb553e93b2b933ccb4ecbc60ced6bce563cdc6bcd463af453cc36acb366cab5eca352d9d6bd8d63d7c6fd6c6bd5467d3463d2c5fd1c53d136ecf26ec9a469b96b8b163609533d94b2a943c8b54c7b4ec7454c6b54c5c598a963c856bc6563c536ec4b5e9a96b899635f953c2e7ec3a64c2d6ec2254c127c 11 2047 5 31 11 2047 20 1048575
def cc_70_13 : Nat → List (Nat × Nat) := unpackCursorV5 0x9444e210984421f4f174add609b4c2291081401c8d268229008039150844012010000000 0xdf3459d9694113bde568dd14bdc943dc57040939ded62ddb6fdbb67db35d9c96b8c1633f93bda455d0a7ccea46d9455ce246d8264cc254d7244cba44d6570d4c7dd5a7cd026ccb244d413bd4c7ed3a44caa44ca254d21483f13b2c133 9 511 3 7 11 2047 20 1048575
def cc_70_14 : Nat → List (Nat × Nat) := unpackCursorV5 0xa85502a0502a01386704c1981286504a08c51062040280100200400708e00c81802c2580b012224038870007 0xe6b55efb45eec69ee355ed464ec354eb47cea36ce9b54e6354e5c54e8138e746be6c63e634ee5b42f056bef563edc6eecb6febb6beab67e9363e8b5fe7b53e5345e4a629f16b8e163611534313b2c933e3a64e2d70e227ce13554293be346fe1c67e0a6ee02469e16b8d1634194b 11 2047 5 31 11 2047 20 1048575
def cc_70_15 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8720c8320c82e492a2288202801c4701c0701936419064154541505415054141500e60ec3000c00 0x3ff5c1fdae0fe37c7edb63f44e2088c30336d811a7c00d2dfe68efcb4339ca598a50c8a2762e9337b9363d4971e54a8fb2447ca36be89b1ed4b8f22447ca373e2911f0290f735d7b5aabd4d35ec68af334e7aa2f3d316de88a6f3c52795ad3c8d59f78befac5b7ce2bbdf14dc96bcf5a5e78d231ca56cc32a64414b16ca1bbb5f1ce6aaf0b45 10 1023 4 15 11 2047 21 2097151
def cc_70_16 : Nat → List (Nat × Nat) := unpackCursorV5 0xc4a6b9465090640902228822080a00789e0781c24a91144110441011e470148500c8300842000800 0x440d921f27114c5989daac4ad3e2369710b47879a1b44908eb296649432409d8c84ce114b90da44867384309b2164890a948845a6c26d16118bd084528722fc3516e178af0a4538492f41e918e92b663953238a58c450e0a2b305459809acbfad460569b06b4b831a3c16d16092964693b17c99c0f166058a302c702309dc06d5a02ae100b7c 10 1023 4 15 11 2047 21 2097151
def cc_70_17 : Nat → List (Nat × Nat) := unpackCursorV5 0x7c67c07a17a07a07a074356f5604e44e04a24a04a04434214204203281301200a40a0062060041040021020001000000 0x8e9b2c76d16194d2bba3b510b49284ee3d8d11dd708eab04731c23eac51e36f8e1b3c5ed76214df0ba6b7f933be698d76476a9a37508b5a4258c932762092b05c91c6d152326f918b548b89c4691522d271194698c62cbf6995f24c71745b8b629c3e97e154b6fd2577c129ba093da44871ad6b8ceb1c60dba2f6bd0f26f85135bf299def4c6e7a5f68d29a805ad1e2c6659538b09c07e4ac152471334d8a9a29244ec66267134698a230c4d1a2246c911568 12 4095 5 31 11 2047 21 2097151
def cc_70_18 : Nat → List (Nat × Nat) := unpackCursorV5 0xe40e40e21e20bd3ba1ae6ae0ae096c78f7427026466216016006005c25c05825425405215205014c2482442139120009 0x25d8c330c5b9822ccbf15e498a323b4f8f1a3cbc96e5c4aeeca4f71925b7691daf486bda3b5691bcb656cf02966a1432609d84a48c242472cb5e75d2fb5a94cd22a62412b08891c8cd76396ab2bb478eda2b8a965ac4a2bd23b3bcac9a2546562964b93b08491cab186536db22b4f8e1a3baa93dc3496dba476a921af28ed5846e7694b33ca192c4ec462560f9238c62cb5290dd44ba0f12394db74a4d79d24bed3253334a983848e4d68925b4491a3649ad12488d925b448c62f476d1648ad12357055a36398d11704d8caa441bcb616251250ad727d6393a374991ae4a8c724c6291db7c8ad9e254df0e26b81133bee98dd14bed2a5391127c8690d78476aaa3751cb5a4a58ccc2a7211432549d88a4ac1b2472036e88d37c349ae004cefaa63514b5a4658c432560c923 12 4095 5 31 11 2047 21 2097151
def cc_70_19 : Nat → List (Nat × Nat) := unpackCursorV5 0xb20a66a0396578f7617417216285c35a15a05245205204094004003c23c03c03a13433403210d30c0025001 0x13cd6e9edaab0c8ed6b46e5293b0b891c76d15854765213b8c62949ad7a366a4f0a5f6d129cf317a506bf1ab539e1a2bc097db34a6c823f60d1dad28dd504666b9532889d8d44cc4c256161232849c9404ac9f2773b36d9d5364e898181476b3a372749d8944ac2a2471db549ad2ccc8566676a938a539a924ccc916702a72bc5392daf468d49df4bed92539b927cda90d8e47ab2a359ae2ccd5156674a53435d999a2b008ea648b327b5f8cda9c92d367269737b479b1a2bbc97db14a734a4b99523b188fd7d476b2237535199ac54e632964d13b19c9985048e486bb1eb555f11d9324ec2724718d7c 12 4095 5 31 11 2047 21 2097151
def cur_70 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_70_19 (Nat.sub p 608)) (cc_70_18 (Nat.sub p 576)) (Nat.blt p 608)) (cc_70_17 (Nat.sub p 544)) (Nat.blt p 576)) (Bool.rec (cc_70_16 (Nat.sub p 512)) (cc_70_15 (Nat.sub p 480)) (Nat.blt p 512)) (Nat.blt p 544)) (Bool.rec (Bool.rec (Bool.rec (cc_70_14 (Nat.sub p 448)) (cc_70_13 (Nat.sub p 416)) (Nat.blt p 448)) (cc_70_12 (Nat.sub p 384)) (Nat.blt p 416)) (Bool.rec (cc_70_11 (Nat.sub p 352)) (cc_70_10 (Nat.sub p 320)) (Nat.blt p 352)) (Nat.blt p 384)) (Nat.blt p 480)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_70_9 (Nat.sub p 288)) (cc_70_8 (Nat.sub p 256)) (Nat.blt p 288)) (cc_70_7 (Nat.sub p 224)) (Nat.blt p 256)) (Bool.rec (cc_70_6 (Nat.sub p 192)) (cc_70_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 224)) (Bool.rec (Bool.rec (Bool.rec (cc_70_4 (Nat.sub p 128)) (cc_70_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_70_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_70_1 (Nat.sub p 32)) (cc_70_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)) (Nat.blt p 320)
def hc_70_0 : Nat → Nat := unpackHintV5 0xd5b95bceb1c2c55657b9230db269aea93a4ca205cd94a3598dd1b4848a527c560d74c1e56f954b6b411563bde15bd9f954ddbf4d49e5458def3f219b3c4cb536597d2f9daf2a754a25055c1d21f917a55f0fa9ff08c1ba02499e000092000000 0x6cd971e3cbd555002c16aaa839cd8b1e2cd8b362cd8b362cd8b362c58b362cd8b162ea9403830e0c3830e0cd8f1e6ea87b545cb8b162c58b166cd9b466cd9b3f55540b0582c16440a0aaaaaaaa0a8a00e743830e0c3830e0ea8387060c387060c380355363c79baa87d9eaa2f5523aa8160b0582c8821614aaaaaaaaaaa00e7166c58b163c58b166c58b166c58baaaaaaa162e85d52a007061c187061c1d555030741c3d07006aa1c383061c383068dba36e5cd971e5c7972f5178bd23b3972f45cb970582c160b0162c058b0592aaaaaaaaaa8039c58b162c78b162cf8b162d18b162cb8b162c58b165c5af162c58ba162c597a5400e0c3830e0c3830e1c1830e1c183818783803550e1c1830e1c183366cd9baa9a366cd8f363cd9b162c58b2e5c58baaaa0582c160b22050555555550545050e0c3830e0c383aa0e1c1830e1c1830e00d551a3468eaa4767aa8dd43ea2f540b0582c164410b0a5555555555500738b662c58b1e2c58b462c58b462c5d5555550b1742ea95003830e0c3830e0eaaa0707a0e00d54387060c387060cb972e3cb8f2e6cd9b366e858b170b165e2f172f42c5d1798160b05050582c164aaa8a0aaaa821c187061c383061c383061c18707030f07006aa5cb971e5c797368d1a3475178bc5cb972e5ea47670582c2e02c580b162c582c160b255555549a4d5555401ce2d98b162c78b162cb8b162c58b165c5a3162c58b168c58b168c58ba162c597a5400e0c3830e5c387060c387065c1830e0c383818783803550e1c1830e1c183366cd9baaa9366cd8f363cd9b2e5c58b162c58baaaa0582c160b2205055555555015510043830e0c3830e0ea8387060c387060c38035546dd1b7aaaa91d9e3750fa8bd502c160b0591042c295555555926aaaa00e7162c58b1e2c58b3e2c58b462c5d5555550b1742ea95003830e0c3830e0eaaa0707a0e00d54387060c387060cd9b163cd9b162c58b1e3c58b366cd9b1e3cd9f3e7cf9f2e7e3e5cfc0b0582c1602c580b160b05aaaaaaaaaaa087061c187061c1870e0c1870e0c187061c187006ab42c58b858b2e8cb972e5cb9f363c79b2e5cb972f0b8d978bc02c580b160b0582c160b25555555555410e1c1830e1c1830e0c3830e0c38381878380355162d19f467cd8f1e5cd97365cb974e5d7972e5e8bc5e47672f172e2c58882c16a88aa1c187061c187062c5a33e8cfd5523b39b8dc3e1f1b8dd49e9f517a858b110592a2324d543830e0e061e162c59b1e3cd9b469d3a3369cd8f1e6cda74f273733660b160b160a0a0b0582c16aaaa8a0aaaa821c187061c383061c383061c187061c187061c01aa8f1e6f38b1e3c78f1e3c78f1e2c58b162c58b1e3c78f366cd9b1e3c78f0582c44162c162c160b555451ee75555410e0c3830e0c3830e0c3830e0c3830e00d5478f1e3c79b1e3c78b1e3c78f1e3c78f1e3cd9b366c1e2c582c58b160b058882c16aaaaaa8aa821c187061c187061c187061c187061c01aa972e5c7971e5cd9b3e7cdd0b162e162cbc5e2e5cb972f0b8f82c1602c580b160b0582c95555555555043830e0c387060c387060c3830e0e061e0e00d54d9f3e6cda7363cd8f369c58b166cf9f367d1a33e6d5cacdc0b0582c582c5828282c16aaaaaa8a0aa821c187061c187061c383061c383061c187061c01aa8f379c78f1e3cd8f1e3c78f1e3cda7368cd9f1e3c78f36cc7972e3c78f1e3c7c5e162c160b11162d1e93554450e0c3830e0c3831e3c79bce3c78f1e3c797366cbc2c5c0b05aaa87061c18f1e3cd8f1e3cde71e5cb8f1e3c78f1e3cd8f1e3c79b466cf9787c3c78b163c0582c58b11162d551143830e0c3830e0cd9b366cb9b2e3cb8f2e5cb9f2e5e2f0b8bc5cb970582c160b05050592aaaaa282aa087061c187061c1870e0c1870e0c1c0c3c1c01aa9b365cd97365cb972e5cba3365cb97162cd8f1e6cb972e8cfc2c5c222c582c168aaaa1c187061c187066cd97365cd972e5d1972e5cd972e5c58b363c79b2e5cba3470b17088b160b05a2aa4d26aa1c187061c187066cd9f3e6cd978bc5cbc5cbc6cd9f1e7c79b365cb97a162c58ba0582c160b05900b1602c5aaaaaaaa4d555410e0c3830e0c38381878387060c387060c3803551e3c78f1e3c58f1e3cb9b2e6e1f5546e0582c160b1121652aaaa2aaaa087061c187061c187061c1d507006ab50f1e3c78f1e3c78f1e2c58b162c58b1e3c78f163c797ce5cb972e0f162c162c5e70582c160b115551ee7555545410e0c3830e0c3830e0c3830e0c3830e00d54d9b2e9cd8f2e3cda72e8cba32f178bc5e162c582c160b05828282c590b55555054555410e0c3830e0c3830e1c1830e1c183818783803550582c160b0582d555555401ce2c58b163c58b162c58b462c58b858b162e5400e0c3830e0c3830e0c3830e00d54387060c387060d55543830e0c3830e0c3830e0c3830e0c3a83 24 16777215 10 1023
def hc_70_1 : Nat → Nat := unpackHintV5 0xf095b2ea4594e5912de1e8eadb69a0d5bd6bd02167c971acc281bcbd7d41b83153b21587ab95a0a5658ca0e91f988e178adf6c82ba0974fb706cae135edb7556422649035042f5833b89db2f570d2a793723d1aa1a9250144d910d19cd000346 0x1b360f366c0078f0366cd9b1e3cd9f3e7cf9f2e7e3e5cfc0000000000aaaaaaaaaaa001c187061c187061c383061c383061c1870600ab40005d1972e5cb973e6c78f365cb972e5e2365e2f00000000002aaaaaaaaaa80070e0c1870e0c187061c187061c1c0c3c00aa08cfa33e6c78f2e6cb9b2e5cba72ebcb972f45e2f23b3978b9700000555550e0c3830e0c3830467d19faaa4767370f8dc6ea4f4fa8bd400000aaac93550e0c383818780363c79b368d3a7466d39b1e3cd9b4e9e4e6e66cc0000000000155555555554003830e0c387060c387060c3830e0c3830e0c0154f9f3e7cb9b2e5cb97a0000bc5e23f672e5e8b972e000000000aaaaaaaaa001c187061c187061c18707030f002a972e5cb97367cf9f3e5cbab2f178b972e5e8a000000000555555555000e0c3830e5c187065c3830e0e061e00552e5cb8f2e3cb9b3e7cf9fa0002f178b972e5cbc47c00000000015555555554003830e0c3970e1c1830e1c197060c3830e0e061e00553e9cf9f3e9cfa73e3cf8f3e9c04e7cfa73e8d19f3eae567e0000000000055555555555000e0c3830e0c3830e1c1830e1c1830e0c38300551e8f38f1e3c79b1e3c78f1e7d1a33e3c78f1eed98f2e5c78f1e3e2f0000002aaaa87061c187061c18f1e3cd8f1e3d1e71e5cb8f1e3c78f1e3e1c31e3c78f3e8d19f2f0f80001e0b000555550e0c3830e0c3833e7cf9f2e6cb8f2e3cb972e7cb978bc45e2e5cb80000000002aaaaaaaaa8007061c187061c1870e0c1870e0c1c0c3c00aa7cf9f3e5e2f172f172e1f367c79f1e7cd972e5e80000000000001555555526aaa8007061c187061c1c0c3c1c383061c3830600aa9d3974f0c7971e9d397868cba3865e2f178bc0000000000002aaaaaaaaaa8007061c187061c1870e0c1870e0c1c0c3c00aa9d3a74e000000aaaaaa0e700001e0008c08000040e0c3830e0c3830e0c383005500181c0d9b162c58b162d1e3c78f362c58b163c78b166c78f366cb9b8d97371f3e7cf82c160a0a0b0582c16aaa0a8aaaa821c187061c383061c383061c187061c187061c01aa9b366c78f479c78f366c78f1e6c78f366cb9b8d973723468d182c1602c580b160b0582c16aaaaaaaaaaa00e7166c58b163c58b166c5a3162c58b166c58b162c58b362c58b362c58b858b166c5ca801c187061c383360c187361c383061c187061c187061c01aa870e0c1870e0c18f478f162c58b1e3c58b366c58b162c58b1e3c78f668d1b3365cdc6cb9b8160b0582c1414160b5555505455410e0c3830e0c3830e1c1830e1c1830e0c3830e00d5478f479c78f1e3c78f1e3cd8f1e3c78f6e8d1b71e3c7c3cb8f8160b0582c058b0162c160b5555547a4d55555401ce2c78b162c78b162cf8b162c5a3168c58b163c58f162c58b163c58b162c58b858b162e5400e0c3830e0c3830e1c1830e1c1830e0c3830e00d54387060c387060c78f162c58b162cd9b162c58b162c78f479b2e6e365cdc3c78f1e8d1a34620a0a82c160b0582c16a8a0aaaaaaa0a1c383061c383061c187061c187061c187061c01aa8f1e3c78f363c78f1e3c7a3ce3cb8f878f1f0f1e3c7a3468d183c058b0162c58b0582c160b0582d5555555555401ce2c78b162c58b163c58f162c58b163c58b163c58b167c58b162d18b462c58b858b162e5400e1c1830e1c1830e0c3830e0c3830e0c3830e00d54387060c387060cd8f1e3c7a6cd8b162c58b163c78b162c58b166c78f36dd1a36e6cb9b8d973702c160b05828282c16aaaaa0a8aaa00e743830e0c3830e0c387060c387060c3830e0c380355366c78f1e3d1e7366cd8f1e3cd8f1e6dba346dcd97371b2e6e0582c160b0162c058b0582d5555555555401ce2cd8b162c78b162cd8b162cd8b162cd8b4e2c58b162cd8b162c58b170b162cd8b95003830e0c3830e0c387060c387060c3830e0c3803550e1c1830e1c183366e1e3e2e5cb971f0f8160b49a4d550739b163c59b166c59b166c59b166c58b166c59b162c5c2cbca01c187061c1870742c58b162e363c79b2e5cb9b2e6cb9761e3c7c2c5d0f1f45e2f02c160a0a0b0582c95541515555043830e0c387060c387060c3830e0e061e0e00d56a363c79b2e5cb97465cbc3ece3c7d0f1e3cbc5e0582c058b0162c160b0592aaaaaaaaaa8039c59b162c58f162c597169c58b162c597162c58b162cd8b162cd8b1742c58b2f4a801c187061c383061c383061c18707030f07006aa1c383061c383063c78f1e3c7d55502c16aa839c78b1e2cf8b462cf8b362c58b5e2cd8b162ea9403830e0c3830e0c78f1e3e6aa858b162c78f162cd9b368cd9b367eaaa8160b0582c8814155555554151043830e0c3830e0ea8387060c387060c3803551e3c78f87d9eaaaa1f5523aa8160b0582c8821614aaaaaaaaaaa00e7163c58b163c58b167c58b168c58baaaa1755542c5d0baa5400e0c3830e0c383aaa81c1e83803550e1c1830e1c1831e3c7d0f1e3cb972f17858b0582d5550738f163c59f162c5a3162c59f166c58b16dc59b162c5c2cbca00c187061c187061c1d0b162e162cb9b2e5cb972e6c78f1e3cb97a162e87cc5e2f028282c160b0582c9514155555504387060c387060c3830e0c3830e0e061e0e00d56a1e8c78f1e3c78f1e3c78f1e5c78fa87d9cbc5e0780b1602c58b160b0582c160b2555547a4d555555401ce2c78b162c58b163c58f162c58b163c58b163c58b167c58b168c58ba170b162cb8ba5400e1c1830e1c1830e0c3830e0c383818783803550e1c1830e1c183 24 16777215 10 1023
def hc_70_2 : Nat → Nat := unpackHintV5 0xd7816ed035d3c96db2bfe662ba0d76b2b5d6afe8b3ab9116a5658b9c42499589ae8f997c88a9bc81fdab7be1877481d86fe926690db75f965e58a1bd4ee27049296e4229c03bfd8b32d64a29e63c240d761d0dc016e18b0d1e710719810001c6 0x58baaa568e19f568e19f1e3c78f0005aaaa00000000000005555554000e1c1830e1c1830e0c3830e0c383aa00550162300078f1e3c800aaaa80000799c00001400126aaaaacae7000800002a1f50fa8fd48e9508580002c07000187061c187061c1d5002ad40e0f46c78f3755540b160f4562c162c882aa159f568d5a3567d695458b00a555556573a82aaaa1c187061c18707541c01870e0c1870e0c1aa9b1e3cdd55500b160f338ac582c591002d58b162d18b1755542c58b555556573a0aaaac6ea1f52ba91d2b0b00a85c2eaa17552c1c187061c18707541c01870e0c583061c5870e0c1aad40e0f46d5a3366cdab1eac79b362c5d5555550280000000000002aaa82802ca0007061c187061c1870e0c1870e0c1d5002a9b568cd8ac01e00b2aaa8088000562333800000aaaa0220acae7008dd43ea3f523a000a0801508580002c1c187061c1870600303855002ad40e0f42c118b1e0b065ce6e1f0015f0fc7e4723945c2e68187858b566c783caaa162c160b5565ce6e370f87c6e3751b8fd47e4728b0983830e0e061e46ad1abaaaa0582c16244acdab1eac7ab361550b4aa2c58052aaaacaa0aaaa87061c187061c1d5070061c383061c38306aa8d5a35755540b058b0162c466722162c58b1e2c58155542c58b555556573a0aaaad50fa8fd52391d2b0b85804542e17550baa960e0c3830e0c383aa0e00c387060c387060d56a0707a366e1e6cdd50f1f46cd9b6aaaaaaa363c79b367cd9f361f166c3e2ea95555555555543830e0c3830e0c387060c387060ea83830e0d568d9f466e964d8b3602c162c582cd99cd8b362c78b1e2cd8b362c58b362e38b162c2a858b555550e1c3830e0c3830e0ea363c79b368d3a7466d3b552ad2d51b1e3cd9b0d8b361b166d79baa55555555555550e1c1870e0c387060c387060c3830e0ea83830e0d5478f3f9e1e3c78f1e3c78f1f555552cd550f1e3c79f3e7cf8f1e2c78f1754aaaaaaaaaaa1c187061c187061c3830e1c1d507061c1aa9f3e7cfd52c87c582c580b161f33c442c58b163c5855055542c58b555555415550e0c3830e0c383aa0e00c387061c383553e7cfaf3e7d39f1e7c79f4f5553552ad2b73e7d59f46bd19f3e2b16ac3e2ea955555555555543830e0c387061c3830e1c1830e1c183aa0e0c383555ebeaaa97afaa555556573aad50faaa474ac2e22960e0c3830e0c383aa0e0c38355a81c1e878f078f1e003c781b360003c78f1ecd1a366ccbb399976700000000002aaaaaaaaa80007061c187061c1870e0c1870e0c187061c1802a8f1e8f38f1e3c78f1e3c79b1e3c78f1edd1a36e3c78f87971f00000000002aaaaaaaaa839c001e00f00f808c01e0f000780040000207061c187061c1870e0c1870e0c187061c1802a800c0e03c78001b360003c78f078f565d5cacbab878f1e3d1a3468c0001100000055555555551000e1c1830e1c1830e0c3830e0c3830e0c38300551e3c78f1e6c78f1e3c78f479c7971f0f1e3e1e3c78f468d1a300000782c00000155555555541ce000f0001e0f0007803c03e02302000010387060c387060c3830e0c3830e0c3830e0c01540060701e3c78f8aaa001e3c219f5e8d7a3867e800000000000015555555554003830e0c3830e0ea8387060c387060c015478f1e3e1f67aaaa87d37a91d540000000000aaaaaaaaaa0e70007803c03e02302020220020000103830e0c3830e0eaaa0707a005500181c28000ba32e5cb972e7c78f1e3cb970001f1178bc0000000000aaaaaaaaaa0001c383061c383061c187061c18707030f002ad43d18f1e3c78f6e3c78f1e3c7971e3ea1f672f17800001e0b00000055555555550738003c000783c001e00f00f808c0802e00081c383061c383061c187061c18707030f002a800c0e08dba34e5cd971e5c7972f5178bd23b3972f45cb970000000000555555555507380000f00f802311805c000b8bc00802e00081c187061c187061c383061c38307030f002a800c0e08d1a347554549cdab1eac7a736005cb8500000000000002aaaaaaaaa88007061c187061c1d5070e0c1870e0c1802aa3468d1d548ecf551ba87d45ea8000000000155555555541ce0033007808c04604040440040000207061c187061c1d5540e0f400aa003038172e5c7971e5cda3468d1d000178bc5cb8001788000000000155555555540003830e0c387060c387060c3830e0e061e00552e5cb8f2e3cb9b468d1a3a8bc5e2e5cb972f523b380000005c160000aaaaaaaaaa0e70019803c02e0005c4600230046230200b800207061c1872e1c383061c3832e0c187061c1c0c3c00aa003038236e8d3d55542736dc7b71e9cd972e00140000000000000aaaaaaa8b55540003830e0c3830e0ea8387060c387060c01551b7469eaaaa47678dd43ea2f540000000000aaaaaaac9355507380000f00f808c0808088008000040e0c3830e0c383aaa81c1e80154006070 24 16777215 10 1023
def hc_70_3 : Nat → Nat := unpackHintV5 0xc53ccebf8d6cb859cdabbb28a6bd3f9b92cb96395690f95087fa407fb6117b8d0a76295972010a6a7de165fd205fbd905919a9510e034afd844459a93a9a7036acfb2fa5c2262e5e2248f91c4980155dbb0f4187062e45061406045c6e000117 0x2c118b1e0b026ae76169b1e3c9801f268c9a8b162c5b07061c18b16acd8f0786dd978bc2c582c16aa4d5cec6c78f266c99b264c99b267c993267c9a326a2c05b07061c187061c1a3568d5bb9dcae4702c160b10592b36ac7ab1eacd813264c9931556858b00162d5555550555543830e0c3830e0e061e0e00c387060c387060d551ab46addcee57238160b1602c588cce0b2162c58b1e2c58142c58b2f42c58b55526aab9d590551693555264c7931e4c9933e4c993464c9aa2c5800b162c58b162c593262c593162c58b583830e0c3830e0e061e0e00c387060c387060d54387060c387060c58b36ad19ba222f0b1644aa4d5cec6c78f266c99b264c99b272c0564d1935160b07061c187061c1ab56ad5d545ea8160b0582c8ce142c58b163c58b16ac58b168c58b02a55526aab9d590551693555264c7931e4c993564c993464c9aa2c58b16004c555004455583830e0c3830e0ea838030e1c1830e1c183550e1c1830e1c183766e81d9b466ea80009ab9d954d8f1e4db93464d4d93364c993364e58b162c01839b060cd870e0c3830e0cd9ba363c79b0aa000026ae7649a4d54d8f1e4cf93464d4f933e4c993764df8b162c0183830e0c3830e0cdbb566c01e0008c0aaaa080000000233aaa93541400126ae75600266c98f263c99326dc993268c9930500000162d50262c000160e0c3830e0c383038000ea80154387060c387060cd9b1e3cd9b264c78f1e3c993366cd9b87a7e3f1f2f47cbd1b1e3cd9b3e6cf9b0f8b361f172b372aaaaaaaaaaaa87061c187061c1870e0c1870e0c1c0c3c1c18706aa4c9a33e8cf9b1e3cbaaaa72ebd5aa65ace5e2f02c160b05aaaaa87061c187061c193266cfa3366ddb29b160b0582cd99cd8b1e2cd8b362c58b362e78b162c2165e162d555543830e0c3830e0c99336ad19ba650582e3391b163c5aaa9b170d5562d18b0a555550e0c3830e0c383264c99b1e3cd9b469d3a3369cda787db56956671b1e3cd9b0d8b361b166d99b8dcaaaaaaaaaaaaa1c187061c383061c383061c18707030f07061c1aad173e7cb9b1e3cdaaa973ead5264eb38f87d4ca0b0582c16aa4dceacca87061c187061c19f3e7cf972e5cbaaa8354d59d562f1f3e7cf9f3e7cf972e5cbd52aacaa9373aaaaaa87061c187061c187061c1d507061c1aa972e5cb9f3e7cf972eaeaa2f39e973b9d59f3eacb972e5cfab567ea955555655ceb9d550e0c3830e5c187065c3830e0ea83830e0d54f9f3e7cfa73e3cf8f3e9c993271f8fc8d5a556e7cfab3e8d19f3e2b16ac3e2e56de55526e755549b2aaaaaa1c187061c187061c383061c38307030f07061c1aad552aa93555ceacaa4c98f263c993264c993464c9aa4c5930984c5ac1c187061c18707030f07061c1aa870e0c1870e0c18f478faa1e3e979baaaaaaaa5551e3c78f568d1ab662b16cc562ea955555555655543830e0c3830e0c387060c387060ea83830e0d5478f479c78f1e3c78f1e3d78faaaaaaaa1e3c78f568d1ab1e0f163c1e2ea955555555595ceab0fa87d47ea91c8ea1f0faa87d54ac2e22960e0c3830e0c3830e1c1830e1c183aa0e0c38355a81c1e8d8f1e8f39ba87d46cd8f1e3ea95a60582cd9b366d555597387061c187061c19b1e3c78f4d9baaa1e3eaaaaaaa9554d8f1e6cda336acd8ac59b158baa5555555556573aaa1c187061c187061c383061c38307541c18706aa6d18f1e3c7a3ce6d1a31e3c7d55555551b1e3cd9b466d59b0d8b361b1754aaaaaaaaacae7558dd43ea3f523a8dc9eaaaa9585c452c1c187061c187061c383061c38307541c18706ab50383d1b362c78f16154000aacb9cdc3e3f1f91c8e3f1fa99ccea50060e0c3838187858baaa363c79b568e19f568e19faa0500aa01e000000017c015414015550003830e0c387060c387060c3830e0ea80154161b1e3cd80230aa0220aa0799c0000000154044155595ce011ba87d0005040137a91d2a0000b07061c1800c0e01c187075400ab50383d0f1e3c7d555082c160b22a80a366cda3366cd9f5a55162c0295555550555543830e0c3830e0ea838030e1c1830e1c183551e3c78faaaa0799c058b0582c88016ac58b168c58baaaa162c5aaaaab2b9d0555561f50fa8fd48e9585c2c022a170baa85d54b07061c187061c1d5070061c383061c38306ab50383d043c78f1e3c79054a802ac87061c18f1e3c58b1e15540f00055565ce3e1f1f8fc8e471f8fd554a42c006060c3830e0e061e 24 16777215 10 1023
def hc_70_4 : Nat → Nat := unpackHintV5 0x83390b3e25ddde82a40ebe20d6f29b2364254999b618c6619e5d2782ab85c395072ee9bbf1f4b3aa923f36a90d1ca07f59cd39738e9b2a63cd620cc6435b72d8d2394ec7688c9eb23fa5aa1afd358c125b051e3ac1c9b160b32c6840b63812a36e000254 0x78f1e3c78f1e3d19b264c993264c78f47ad2a8f87c8e472b158b562b163c78f1e8d1a3472b572aaaaaa935555954387060c387060c3830e0c3830e0e061e0e0c383551e3c78f1e8c78f1e3c78f479c78f2f43c7c3e87c3e4723878f078b1e0f1e2c78f1e3d1a3468e56ae555555526aab9d595478f263c78f1e3c78f1e3c793263c78f1e3c78f1e4cf93264d19326a93164c261316b070e0c1870e0c187061c187061c1c0c3c1c18706aa1c383061c383066c78f479cd8f1e4c793263cd9b1e3c99326ac6d7702c166cd9b36aaaaa1c187061c187066c78f4d9b1e3c78f264c78f264c993263cdc3e5f2395568d8f1e6cda336acd8ac59b158b959b955555555555543830e0c3830e0c387060c387060e061e0e0c38355368c78f1e3d1e7368d18f1e3cdc3e5f238d97a765e8d8f1e6cda336acd86c59b0d8b959b95549aaa9349aaaab9d595499b1e3c78f264c99f264c9a3264c99b269c993264c993264c9935498b2613098b583830e0c3830e0c387060c387060e061e0e0c383550e1c1830e1c183366e87c5cbd5502c164d49a4d5573b1b1e3d3e4d1933e4cf93264d993663c78f51602d83830e0c3830e0ea363c79b2e5cb97465cbd59e1f50fa2f546c78f365c2e2cb85c59b5e6ddd52aaa4d26aaaa4d5573ab2a93364d38f1e3c7931eaaa3c78f1eaaaa4c993268c9935498b2613098b583830e0c387060c387060c3830e0ea83830e0d54387060c387060c78f1f50f1e3eaaa5eec160b2693549a4d5573b0f478f3e4c993464c9933e4cf93264dd937e4c99351602d81830e0c3830e0c383a87a31e3c78f1e3c78f1f0fa1f555543c1e2c783c58f1e3c7bb5ebddd52aaaa3d26aaa4d5573ab2aaaaaaa8f1e4c98f1e4eda8f1e3c78f1e4cf93264d19326a93164c261316b070e0c1870e0c187061c187061c1d507061c1aa870e0c1870e0c1a35e8d7975e5c7971e5cbd517aaab3c5ea2f5356ad5a346acb85c5970b8ba2f52aa935552693555573ab2a93263c98f264c99f264c993464d1aaa93264c9aaaaaa4c5930984c5ac1c187061c187061c383061c38307541c18706aa1c383061c383066d1972e3eaa2f551b360b05a9355573b1b1e4c78f264c99f5193364cd93264cd93964c99351602d83830e0c3830e0cb972e3cb8f2e8d1a34755545e8bd559d5ab56acb85c5970b8b468d1a3aa55555549a4d49aaae7565526cc98f263c993555555264c993268c9a93464d19326a93164c261316b07061c1872e1c383061c3832e0c187061c1d507061c1aa870e0c1870e0c19b362c78f1605e2f0001352693555cec6c78f267c9a3267c99f264c9b326cc99326a00c1c187061c187062c58f1e3c793166c78f36ad1cb3ead1cb3e6e1f00284b95c0000000000aa0a00aa8a001c187061c383061c383061c18707030f002a82c363c79b004606e1f0105c29cae0799c0000000154044149aaae75600266c78f1e3c993000264c0980136e4c993464c9aa0000b07061c1800c0e01c18707030f002a870e0c1870e0c18f1e3c78f87cae57082c160b0590f1e3c01e3cd9b368cd9b367d556858b00162d5555550555543830e0c3830e0e061e0e00c387060c387060d5478f1e3c7c3e572b81e670162c160b059002d58b162d18b1742c58b2f42c58b55526aab9d5905555478f1e3c78f1e3c99f264c9a3264d5162c0058b162c58b162c993162c98b162c5ac1c187061c18707030f070061c383061c38306aa1c383061c383063c78f162c785178bc0f00049aa9349aaae761e3c78f3e4cf93464d1933e4cf93264dd93964c9935006060c3830e0c3830e0d78172f67ce4dcf2c099f46935162c78f1e2c78f568e59f568e59f1e3c78f50001f0fa5cae0000000000000555526aa8b00070e0c1870e0c187061c187061c1c0c3c00aa02c46000f1e3c785c0087c3e95c00003cce00002002aaa4d5573ab0001300000264c78f1e3c78f1e3c99f264c9a3264d50000580e00030e0c3830e0c383818780154387060c387060cd8f1e6cdc3e572b81620b0582c8078f1e3c98acfab46ad1ab3eaab42c5800b16aaa4d55554155550e0c3830e0c3838187838030e1c1830e1c18355363c79b370f95cae0162c1e67158b058b059002d58b162d18b1742c58b2f42c58b55526aab9d590551693555266c78f1e3c99326ac993268c9935458b00162c58b162c58b264c58b262c58b16b07061c187061c1c0c3c1c01870e0c583061c5870e0c1aa870e0c1870e0c19b568cd9b36ac7ab1e6cd8b164c993264c59b9dcae47002800000000002aaa8280228007061c187061c1870e0c1870e0c1c0c3c00aa6d5a3362b007802c373b95c8e020b8000ac46670000015549aa0093050573ab0013364c7931e4c9933e4c993464c9800132604c0150000583830e0c3830e0c006070818780154387060c387060c58b368c1e0f2f17858b0582cd8b5526ae76363c793364cd93264cd93964c9933e4d19351602d83830e0c3830e0d1a3468d7cbe47238160b10582c959b563d58f566c9932601326aab42c5800b16aaa4d5554155550e0c3830e0c3838187838030e1c1830e1c18355468d1a35f2f91c8e0582c46670162c1642c58b163c58b02858b165e858b16aaa4d5573ab20aaaa93664c7931e4c993464c993464c9aa2c5800b162c58b162c593262c593162c58b583830e0c3830e0e061e0e00c387060c387060d54387060c387060cda301e2c58fa2f17804600a4d49a4d5573b1b266c78f263c99f268c99b266c993266c9cb264c9a803070e1c187061c187066d1a3365cb972f0b2e5c0000015549aaa935738004c993264c993268c9a8000000b07061c187061c187061c1802a87061c19b36ac7ab1e6cd9b468cd8b164c993164c99b97ca0008e4700000000002a8002a9355458003830e0c387060c387060c3830e0e061e0055007806d1a33602cdcbe02e00148e470000002333802a8800a93555ceac004cd931e4c7932604c00000993268c993268c99354000160e0c383038000c3830e0e061e00550e1c1830e1c183 25 33554431 10 1023
def hc_70_5 : Nat → Nat := unpackHintV5 0xddd1b4d1dafecb8196c2464fbbc99fb2de3bab41e7a30e0d9e1d3c9a11039202048be986832a307bc1da74c5bf6f3d626d208769090664a5195f25605b190356313a4f0dc94881a3403a1232836e2cf16424ce09173f640f160a0879a700021e 0x46ad1ab2f178bc5e0582c160b122e6cb8f2e3cb975162d56898154002e5555554155550e0c3830e0c3838187838030e1c1830e1c1835546ad1ab2f178bc5e0582c160b233850b7e2c58b1e2c58b3e2c58b462c58152aaa4d5ceaa82aaaa4c98f263c993568993265e858b00162c58b162c58b264c58b262c58b16a4c3830e0c3830e0e061e0e00c387060c387060d54387060c387060cdb7466cb972e3cb8f2e6c0014bc5e2f17858ba262e800000000015550001554003830e0c3830e0c387060c387060e061e005536dd19b00780fc04601f2f178bc5e0160000000119d55526ae70500049aa8013364c7931e4c9aa04c00000993a264c997a00005261c187061c18706070001c0c3c00aa1c383061c383068d5a35755540b0582c1642acdab1eac7ab36b4aa15502c5800b16aaa4d5554155550e0c3830e0c383aa0e00c387060c387060d551ab46aeaaa8160b0582c288cf3fa87d47ea474042e55549ab9d550555549931e4c79326ad5550b16002c5d55132744ea94987061c187061c1d50700750383d2a870e0c1870e0c1b9dce8f1ee71e7c78f363cd9f3e6cf9f3e7c78f1e3cd9b366cd9f367c78f1e3cdab36ad55ceb9d55555550e0c3830e0c3830e0c3830e0c3830e0c38355a264c7c4c9971e5cb8f1e5cfa3c79b2e5cb972f0f8d978bc5c2e2cb85c59b1e3cd9b3e6cfc5cbcaaaaaaaaaaaa1c383061c383061c187061c18707030f07061c1aa9326acda8f4bc5e0582e3391b163c59b166c58b166c59f162c59f168c5852aaaa87061c187061c19326acda8f6a8160b28ce6e370f87c6e3751b8fd47e4700b9555543830e0e061e264c9a3c79b4eaa3c7a9b1e3cd9b4e7e3e6e3e8d19f363c79b361b166c362cda3367cd9b55555555555550e0c3830e1c1830e1c1830e0c3830e0c3830e0c383551e3c78f1e3c78f1e3d961f47eaa7f0f1e3c79f3e7cfbf2e5dfd52aa935555555543830e0c3830e0c3830e0ea83830e0d56a1e3c78f1e3c79fce3c78f1e3c78f1e3c78f264c78f1e3c78f1e5f3b28f1e3c78f1e3c79f3e7cf972e5cbaaa8f73aaa935555543830e0c3830e0c3830e0c3830e0c3830e0d54f9f3e7cb971e5c797a8b972e5dab3aaa88aa7cf9f3e7cf9f3e5cb972e5cb972eaaa4d5526e75555550e0c3830e0c3830e0c3830e0c3830e0c383553f9cf9f3f9cb9f2e7dcf4b9f3b543e8bd2b8f9f3e7cf9f3e7db972eaea955ce935cf9d555926aaaa1c187061c187061c18707541c18706aa3c78f1eca3c79f3e4c98f3382c160b03e2cf8b7e2cd8b162cb8b2e2c58b8597858b26aaaaa87061c187061c18f1e3c58b1e6e8d84c01e004d550e0c383059f03e172e0003f1e3c78f652e10f1e7cf9326003cce00824d5550e00c3830e0cf83c161b1e3cdb2802b562807cf9f3e45c264c3e7cce00004d0498a2aa80c381c187066c78f36ca7cf9f3e4c99f160b3e670582cf8b1e2c1d8b86aaaac2cbc2c5a4d73aaaa2d26aa1c187061c187065df9736cafcb976e4c9bf0787c8160b8260fcb85c00b804d555140e0c38301870bbf2efd95f972eac9937e2c162c5970b8b2efc58f167e85800b270b164d555550e0c3830e0c38346fd1bf2e9df8f2e3dfa75a552f178bcc4c9937efd1a30b8b2e0b8b9795549aaaaaaaaaaa1c187061c187061c383061c38307030f07061c1aaa3468d1a346aaa93573aaaa93263c98f264d52713264c9c4c5930984c5a930e0c3830e0c3830e0c3830e0c383550e1c1830e1c183366c78f1e3c993478f364c793263c793266e1f2aad1f8fc6c78f366c3e2cd87c59b3e6cfcacdcaaaaaaa4d555550e0c3830e1c1830e1c1830e0c383818783830e0d54da31e3d1e71e3cda31e3c79b87c6cbd232f48e471b1e3cd9b0d8b361b166d19b472b372aaaaaa93555ceacaa4cd8f1e3c793264cd93464c993264cf93264c993267c993268c9935498b2613098b583830e0c387068c1830e8c387060c3830e0e061e0e0c383550e1c1830e1c183368f1f9c79b52f178160b26a4d26aab9d878f1e3cf93464cd93364c993364e593264d4580b60e0c3830e0c3831e8f1e3c78f1e3c78f1eccd93264c993263e1f2f91caab43c78f1ead1a356cc562d98ac5caddcaaaaaaaaaaaa1c187061c187061c383061c38307030f07061c1aa8f1e8f38f1e3c78f1e3c78f1f0f97c8e1e3e8797a1e3c78f568d1ab1e0f163c1e2e56ee55526aaa3d26aaaae756551e3c78f1e3c78f267c993268c9931e3c78f1e3c9931e3c98f1e3c7aa4c5930984c5ac1c187061c187061c383061c38307030f07061c1aa870e0c1870e0c18f878f2f172e3c7a3cb972e5c78f1e3d1a3468d526ae755549aaaaa3c7aaa3c78f1e3c793264c9a3264c99326b07061c187061c187061c187061c1aa87060c3830600003c7a3c007c3e47238015549aaae75600001e3c78f1e3c78f267c993268c993556000e0c3830e0c3838187954387060c387060c78f478f87c8e470b162c58b162c5c2c5caaa4d5573ab28b5478f1e3c78f1e3c99f264c9a3264d5162c58b162c58b583830e0c3830e0e061e0e0c383550e1c1830e1c183 24 16777215 10 1023
def hc_70_6 : Nat → Nat := unpackHintV5 0x8dcf0945e83fe24ea970e9cf68412cf402d771f1dbe4eb476a6ea5bfb5547f9909e82c131c75baf3aabdb7f14f5be099cf784930eda21c9f0f8662071fe8d355ee8183c9ccb263e04bef512252e90eb49d464a44024a76b0d43440383c78105af000020b 0x4c993368c78f46a8f1eaa6c78f366d3a7939b91a3468cd8f1e6cd86c59b0d8b368cda3366d7aaaaaaaaaaaaa87061c1870e0c1870e0c187061c187061c187061c1aa8b0468c363c79b005ebc2e5c05622e23464c98f338008c0051554061c0e0c3831e3c78f56468c9931e670582c1608c5a316bc59b162c597165c58b170b2f0b16aaaaa1c187061c187060b4608c2e5c0005ebc78f1e3d58b848d19326003cce0082aaa1c0187061c19b1e3cdab23464c982c799d18b0582c118b462d78b5e2c58b2e2cb8b162e170b2e2cbc2c5aaaa2d26aa1c187061c583062c387068d1a3465d3af1e5c7af4eaab45e2f3232e8e264c9a3468d1af0b8b2e2f17172f2aaaaaaaaaaaa87061c187061c1870e0c1870e0c1c0c3c1c18706aa8d1a346bd7a3468d1a3468d1af5eaaae7549a9355549931e4c79326a938993264e262c984c262d4987061c187061c187061c187061c1aa870e0c1870e0c18f1e7f38f1e3c78f1e3c79f1e3c78f1e7cf9f3e3c78f87971f0f1e3c79f3e7cf8f078b1e0f16bd5b756aaa93573aa3d26aaaaaaa3c79351e3c78f1e3d5551e3c99355552713264df93898b2613098b5261c187061c187061c383061c383061c187061c18706aa1c383061c383066cf8f1e3c79fce6cf9f1e3c79b1e3cd9f3e8cf9f3e6cb9f8f97371b1e3cd9b3e6cf9b0d8b361b166d59b56aaa93573aa4d26aaaaaaa4cd934e3c78f1e4c7aaaaa3c78f1eaaaa4e264c9bf2713164c261316a4c3830e0c3830e0c387060c387060c3830e0c3830e0d54387060c387060e878f1e3c9c6c78f365cbaaab0f1e3e263e878fa2f178d8f1e6cb85c5970b8b368cd9f8b9795555555555543830e0c387060c387060c3830e0e061e0e0c38355a8d8f1e6cb972e7cba32e5e1f671e3e878f1e5e2f1b1e3cd970b8b2e17166d19b3f172f2aaaaaaa4d5ceaaaa4cd8f1e3c793264cb934e4c993264cb93264c993568993265e898b2613098b5261c187061c383061c383061c18707030f07061c1aa870e0c1870e0c18f1e3c7cd550f1e3c78f1e3c7ad2ad5550f1e3c79f3e7cfd51f0f8b3e1f16aaa4d5555555550e0c3830e0c383aa0e1c1830e1c1830e0c383551e3c78f87d9eaaaa1f47ea3f550f1e3c79f3e7cfd5442e2955526ae7555555551e3c78f1e3c78f56aaa89d555132744ea898b2613098b5261c187061c187075550383d07061c1aa870e0c1870e0c18f878f1f3178bc3c78f1e7cf9f3f172f2aaa4d5ceaaaa8f1e3c78f1ea3c7aab13264c997279e262c993262d4987061c187061c1c0c3c1c18706aa1c1830e0c1d0f1e3e1e3d5478f51e3c78f2e5e8993a1f3178bc5c2e2cb85c58f1e3c79f3e7cfc5cbcaaaaaaaaaaaa1c383061c383061c187061c18707030f07061c1aad43c79f463c78f1e3c79f1e3c78f1e3cb8f1f50fb3978bc3c1e2c783c58f1e3c79f3e7cfc5cbcaaaa8f49aaaa4d5ceaaaa3c7931e3c78f1e3c78f1e3c9931e3c78f1e3c78f5689c4c9932e4e898b2613098b5261c383061c383061c187061c18707030f07061c1aa870e0c1870e0c19b1e3cdd50f6a8b971e3c78f264d6956aaa8d8f1e6cda3367ea8d8fc59b1f8b55549ab9d555555550e0c3830e0c383aa0e1c1830e1c1830e0c38355363c79baa87d9eaa2f47ea47551b1e3cd9b466cfd5442e2955526ae755555555266c78f1e3c99356aaaaaa8993a27544c5930984c5a930e0c3830e0c383aaaa060e8387a0e0c383550e1c1830e1c1833e7cf9f2e7cb8f2e3cb97a8bc5e8fd9cb97a2e5cb9f3e7cf9f3e7cf970b8b2e1717172f2aaa4d5cea9349aaaaaaa933e4c7931e4c9aaab54aaab44e5265c9d13164c261316a4c3830e0c3830e0c387060c387060e061e0e0c383550e1c1830e1c1833e7cf9f3e7eaaaa3f678fd43ea2f547cf9f3e7cf9f3f5510b8a55549ab9d555926aaaaa4cf931e4c79326ad55513555a264d555498b2613098b5261c187061c187075550383d07061c1aa870e0c1870e0c18b163c78f1e4c59b1e3cd82801b1e3cdb72ede6e5dbc7d1a33e03c00000000f802a82802a2a8007061c1870e0c1870e0c187061c187061c1802a82c363c79b00f88c0d8f1e6c082e07d1a33e0f338000001f00550110549ab9d540099b1e3c78f264c00099302600a93899326fc9c0000a4c3830e0c0060700e0c3830e0c38300550e1c1830e1c1831e3c78f1e3c78f3e7cf9f10582c160b058f1e3c01e3d458b55371b2e6cb9b858b00162d5555550555543830e0c3830e0c3830e0c38030e1c1830e1c183551e3c78f1e3c78f3e7cf9f0799c058b0582c160b0059f162c59f162c5c2c58b2e2e162c5aaaa4d5ceaa82aaaa3c78f1e3c78f1ea938993264e162c58b00260b162c58b162c593262c593162c58b5261c187061c187061c187061c01870e0c1870e0c1aa870e0c1870e0c18b163c78f163c780028f1e3c79f2e7e3e5cfc3c78f1e7cf9f3e0000000000000aaaa935738aa001c383061c383061c187061c187061c1870600aa02c3e001f1e3c78f0b8010f1e3c79f3e7cf80000f3380000800aaaa4d5ceaa0004c000009931e3c78f1e3c78f549c4c99327013160000a4c0e00030e0c3830e0c3830e0c38300550e1c1830e1c183363c79b363c79b3e8d19f058b07a1f160b160b0580f1e3c7931458b55572b2eacbab858b00162d55526ae75550555543830e0c3830e0c3830e0c38030e1c1830e1c18355363c79b363c79b3e8d19f0162c1e670f8b058b0582c0167c58b168c58b170b162cb8b858b16aaa93573aaa0aaaa93363c78f1e4c9aa4e264c9bf270b16002c58b162c58b164c98b164c58b162d4987061c187061c187061c1870061c383160c187161c38306aa1c383061c383066cf9f361f007802c367cf9b3e7cf9f020b80007c3e6700000155526ae700498282a8013364c7931e4c9aa0002c58280138993264e0262c00014987061c187061c1800c0e01c1870600aa1c383061c383067cf9f3e7cf9f3e7cf9f3e1f160b1602c587cce0b058b3e2c58b1e2c5802e162c597170b162d55526ae75541545a4d55499f263c98f264d52713264c9c2c58b16004c5550044555261c187061c187061c187061c01870e0c1870e0c1aa870e0c1870e0c19b5e8cdd5551b36dc7b71e6cda800555500000000002aaa4d5ce2a82800007061c187061c1d5070e0c1870e0c1802a9b5e8cdd5550fc01e01f0118100000467000155526ae755011000266c98f263c99356aaa8000993026000000a4c3830e0c3830e0ea800607000550e1c1830e1c183 25 33554431 10 1023
def hc_70_7 : Nat → Nat := unpackHintV5 0xeafe39e6093de03974de088cd9e509d8346cd1ed92cdcd08c8954ec3f927bead53b7e5b2b01df2a839f99b134a93add98ba6027e2b5f7731be6d1687651dfe58134350e5cb4702793f0dfd30b79629c1bd1d4b1e16a9a80d365d04f21100013c 0x2e5c7971e5cd97ce8c78f47532972e4c993264c9932e5cb97265cf97ce9c78f4e5c2e5c2e8d1a3465cb972eaaaaa4d26aaaaaa1c187061cb830e0cb87061c187061c187061c1aa9b0782c653e8d19f0056ac2e5c0366d1a30a0b9709930da33380000ac16009314555018703830e0d94fa3467cd9b468c99346670582c1606c58f1615c5b7162c597165c58b170b8597165e162d555543830e0c3830e0d1a33746cb8b165c098008c0015543830e0c1e1b05b285cb80015cfa3467cd9b2e00123464c980233380020aaa870061c187066e8d85cb9131702c16aa1c18706ca7d1a33e6cda3464c9a7160b46677602c162c581b163c583b162c58b2e2cb8b162e170b2e2cbc2c5aaaaa87061c187061c1b297565db9736acb93266c876230582e009803b2e17000b800aaa281c18706030e3297565d59736acb9326ac582c58b2e1705970b9ba16ac5a3160002c98b270b16aaaaa1c187061c187066c78f36ca5d597ae1b0000460ac000000001515554100003830e0c3830e0c3830e0c000154d8f1e6c003608c0652e5cb97000098b000000000b99d515400049aa8007061c187061c18007061c1802aa71e3d3ad2a97465d1974f3272f178993269c78f4e17165c17172f2aaaaaaaaaaaa87061c187061c1870e0c1870e0c1c0c3c1c18706aa9c78f4e9c78f4e9c78f4ea8f573aaaaaaaa4c993268c9932713264c9c4c5930984c5a8f0e0c3830e0c3830e0c3830e0c3835541870e0c983061c9870e0c1d0f1e3c7938d8f1e6d554b9761f131f43c7d178bc6c78f365c2e2cb85c59b466d1c5cbcaaaaaaaaa4d5550e0c3830e1c1830e1c1830e0c383818783830e0d56a363c79b2e5cba32e8cb9787d9c78fa1e3c7978bc6c78f365c2e2cb85c59b466d1c5cbcaaaaaaae7549a93555499b1e3c78f264c997269c993264c997264c99326ad13264cbd13164c261316a4c3830e0c387060c387060c3830e0e061e0e0c383550e1c1830e1c1831f0f1e3e62f17878f1e3cfb76e7e2e5e55555526aaa8f1e3c78f1e4ed938993265e262c993262d4987061c187061c1c0c3c1c18706aa1c1830e0c1d0f1e3e1e3d478f551e3c78f2e5e8993a1f3178bc5c2e2cb85c58f1e3c79f468cfc5cbcaaaaaaaa93526aaa870e0c1870e0c187061c187061c1c0c3c1c18706ab50f1e8d18f1e3c78f1e8c78f1e3c78f2e3c7d43ece5e2f0f078b1e0f163c78f1e7d1a33f172f2aaaaaab9d526a4d5551e3c98f1e3c78f1e3c78f1e4c98f1e3c78f1e3c7ab44c9932f44c5930984c5a930e1c1830e1c1830e0c3830e0c383818783830e0d54387060c387060c58b1e3c78f262cd8f1e6c0140d8f1e6d9975f332ebe468d1a300000000005505004555000e0c3830e1c1830e1c1830e0c3830e0c38300550586c78f360231181b1e3cd8105c11a3468c1e670000004600aa0220ae7549a93540099b1e3c78f264c00099302600a938993264e0262c00014987061c1800c0e01c187061c1870600aa1c383061c383063c78f1e3c78f1e7d1a33e0f4162c160b0582c78f1e00f1eaaa2c59b8d97365cdc2c5800b16aaaaaa82aaaa1c187061c187061c187061c01870e0c1870e0c1aa8f1e3c78f1e3c79f468cf83cce02c582c160b05802d18b162d18b162e162c597170b162d555cea93526aa0aaaa8f1e3c78f1e3c7aa4e264c993858b00162c58b162c58b264c58b262c58b16a4c3830e0c3830e0c3830e0c38030e1c1830e1c183550e1c1830e1c183162c78f1e2c78f50001e3c78f9e5d7d3cbaf878f1e3cfa3467c0000001e0000000aaaa2aaa001c383061c383061c187061c187061c1870600aa02c4600231e3c78f0b8010f1e3c79f468cf80000f3380000280024d555cea93526a8001300000264c78f1e3c78f1e3d52713264c9c0000a4c0e00030e0c3830e0c3830e0c38300550e1c1830e1c183363c79b363c79b468d1a305882c160b0580f1e3c793155458b572b2eacbab858b00162d5555549aa82aaaa1c187061c187061c187061c01870e0c1870e0c1aa9b1e3cd9b1e3cda3468d180b160f3388c582c582c1600b462c58b462c58b858b165c5c2c58b55573aa4d49aa82a8b49aaa93363c78f1e4c9aa4e264c993858b162c00982c58b162c58b164c98b164c58b162d4987061c187061c187061c1870061c383160c187161c38306aa1c383061c383068d1a3465e2f178bc0b0582c16245cd971e5c7972eaaa2c5d1302a8005caaaaa4d54155550e0c3830e0c3838187838030e1c1830e1c18355468d1a32f178bc5e0582c160b233850b662c58b1e2c58b462c58b462c58152aab9d526a4d5415555264c7931e4c9ab44c9932f42c58b16004c162c58b162c58b264c58b262c58b16a4c3830e0c3830e0e061e0e00c387060c387060d54387060c387060cda3466cb972e3cb8f2e6c1400bc5e2f17858ba262e80000000001554526000aa4d5000e0c3830e0c3830e1c1830e1c183818780154da3466c01e033011808cbc5e2f178058000000046755573aa4c400549aa004cd931e4c79326a81300000264e8993265e8098b00005261c187061c18706070001c0c3c00aa1c383061c3830744c98f89932e8c78f2e5cb8f363c7a5cb972e5e1f1b2f178b85c5970b8b363c79b368cda38b9795555555555554387060c387060c3830e0c3830e0e061e0e0c38355264cda347a978bc0b05c672362c78b362cd8b162cd8b862c58b3e2d18b0a555550e0c3830e0c383 24 16777215 10 1023
def hc_70_8 : Nat → Nat := unpackHintV5 0xecbe9ce57dd0dab2b3d2e1f4c50b76be11beb30ec1aa6a299cb76d973d5e919d6888ce3481edb874eb4172c08a6d356366dd965ca28f55c5b74c2a6744d9d43da9cc3506292f81612a913c224a121adddb15655e0fa57006ee2e05e84100017a 0x1f1e3cfd55548ecf1ba87d45ea938f1e9cfa3467eaa21714a8f573aaaaab24d555555267c993268c993aaaaaaa264e89d513164c261316a3c3830e0c3830e0eaaa0707a0e0c3835541870e0c983061c9870e0c19b1e3cda8000b164c993264c59b1e3cd9f468cf9b2e6e365cdc001b04600000002a2a82802a8007061c187061c1870e0c1870e0c187061c1802a9b1e3cd86c01e00b0d8f1e6cfa3467c082e0001b1199c00000547ab9d5401260a0aa00a933e4c993268c9a3264c000993026004e264c993800014787061c187061c1800c0e01c1870600aa830e1c193060c3930e1c183363c79b363c79b468d1a30582c10160b05a8b16aa4c99300993572b2eacbab858b00162d5555550555543830e0c3830e0c3830e0c38030e1c1830e1c18355363c79b363c79b468d1a30582c46670162c160b166c58b163c58b005c2c58b2e2e162c5aa3d5ceaaaa82aaaaa93464c993464c9938993264e162c58b00260b162c58b162c593262c593162c58b51e1c187061c187061c187061c01870e0c1870e0c1aaa0c387064c1830e4c387060c0014d8f1e6c58b264c98b264cd8f1e6cd97371b2e6e468d1a300000000005400055555000e0c3830e1c1830e1c1830e0c3830e0c383005500783c03627363c79b0166c78f3617002468d1a3000000466700547ab9c40055554015026000004c993464c993268c9a3264c9c4c99327013160000a3c3830e0c0e00030e0c3830e0c383005541870e0c983061c9870e0c19b1e3cd9b1e3cd9f468cf89c582c580b162333a0b05a8b16aa04c993264c572b2eacbab858b00162d47aaaaaa82aaaa1c187061c187061c187061c01870e0c1870e0c1aaa0cd8f1e6cd8f1e6cfa3467c4e2c162c058b1199c160b166c58b163c58b005c2c58b2e2e162c5aa3d5ceaaaa82aaaaa933e4c993464c9938993264e162c0058b162c58b162c993162c98b162c5a8f0e0c3830e0c3830e0c3830e00c387060c387060d55061c383260c187261c383066c78f3615540008f5ceaaaa7c99f267c9a3267c99f264c99f26bc9932754008f0e0c3834187260c1930e1c19b1e3cdd55528001b3e6cd9b466cdd555000004000002a2aaa82800007061c187061c1d5070e0c1870e0c1802a9b1e3cdd55506c01e0008c0800002338000a8f573aaaa8088002a4db93264d1932755544e8000993026000000a3c3830e0c3830e0ea8006070005541870e0c983061c9870e0c19b1e3cd9787c5e2f02c160b0582128b16aa5cf972e5d1972f44c0aa00172aaaaaa0aaaa87061c187061c1c0c3c1c01870e0c1870e0c1aa9b1e3cd9787c5e2f02c160b05919c2859b162c58f162c5ab162c5a3162c0a951eae75555415555549ab264c9a3264e8993265e858b162c00982c58b162c58b164c98b164c58b162d4787061c187061c1c0c3c1c01870e0c1870e0c1aaa0c387064c1830e4c387060cd9b2e5d1ea1308b9780007aaa1c1870683366cb97363c79b0858b80011eb9d554f933e4e265e3e4cf93264cf93264c98023c3830e0d061c983064c387066c78f36000a5cb97465cb973e5e1f178bc2c5d131740000000000a8aa000aaa001c187061c187061c383061c38307030f002a9b1e3cd803c03602300bc3e2f1780580000000467547ab9d541400126aa00a936e4c993464c981300000264e89c4c9932e4e8098b000051e1c187061c18706070001c0c3c00aa830e1c193060c3930e1c183363c79baaaa0582c160b0a233ab4aaacfab46ad1ab3e15502c5800b16a3d555554155550e0c3830e0c383aa0e00c387060c387060d55066c78f3755540b0582c16144678dd43ea57523a02172a3d5ceaaaa82aaaaa93564c993464c9d5550b16002c5d55132744ea94787061c187061c1d50700750383d2aa0c387064c1830e4c387060d47a5cd8f1e5cbd13264c9d132f0f89c7ece5cbd172e5cf8f1e7cf9f3e7cb85cb85e2e5e555555555550e0c3830e0c3830e0c383818783830e0d54b971e3cb9b51e972eacbc3e2e5cb972f44e3f674e3c7a72e172e173ead59f8b979555555555543830e0c397061c1970e0c383818783830e0d54b971e3c78f2e6cfa3cfd13264e264cbc3e2e5cb972f138fa71e3d3970b8b2e17167d1a33f172f2aaaaaaaaaaa87061c1872e1c383061c3832e0c187061c1c0c3c1c18706aaa3d0d800004c161b1e3cd9f3e7cf80170003607cce000002a2a80e70055000e0c3830e0c383000e0c3830055000da8f4159b1e3cd85c00fab567c0000003e6700540015555000e0c383000e0c3830e0c38300553e9d1e7d3aa8f1ea4c9934e3c7a73e8d19f3eae567e4e3c7a73e8d19f3e2b16ac3e2dbab6ead55555555555543830e0c3830e0c387060c387060c3830e0c3830e0d54f8f1e7d5478f52e7cb97989c7cb978b972e7c78f3e7cf9f3e5c2e2cb85c5c5cbcaaaaaaaaaaaa1c187061c187061c383061c38307030f07061c1aab2972e5cb972e8cba72e4cb972e4c99ba365cb97467e264c99389cacb9756acb82c16aaaaa1c187061c18706ca5cb97465cb972e9cba32e5cb93266e8d972e5d1a391c4c99327372e5d5d72e0b05aaaa4d26aa1c187061c187067c78f3e5e62e5e3e5cf97cf1f3743e3e6cb972f47c993264c993a3e3c79f3e7cf9f8b978f87c59f0f8b555555549aaaaaa1c187061c18707030f070e0c1870e0c187061c1aa932e6e264d409a4d518f1e8d94b9f265d19f8dd545ea4e3c7a7468d1a3565cbab8a2555555555550e0c3830e0c3830e0c383aa0e0c38355 24 16777215 10 1023
def hc_70_9 : Nat → Nat := unpackHintV5 0x820b42bf077f9dd8eace8519d7084e935cd9d59eebe0c15f865de6b22ce882d59a368a0bf054d20cfa44e90915c32c81a64f3cb1089cb3694d62bdc62ce122dcce694d48489b4ad64619e31f72e68c3edec53e3841f8a9a0bad060201f540f40320001e8 0x78f1e3c1e00f00583c78f1e7cf9f3e04170000787cce000002b9d51eaa0220aa00a8f363c78f363c78000f1e03c007c3c78f363e01e2c00014787061c187061c1800c0e01c1870600aa1c383061c383063c78f1e3c78f1e7d1a33e0b0586d058b0582d55458b1e3c7803c79b8d97365cdc2c5800b16aaaaaa82aaaa1c187061c187061c187061c01870e0c1870e0c1aa8f1e3c78f1e3c79f468cf82c161f3380b160b058b1e2c58b1e2c5802e162c597170b162d5cea8f5555415555547a31e3c78f463d18f1e3e1e3c7bf1f0b16002c58b162c58b163c78b163c58b162d4787061c187061c187061c1870061c383061c38306aa1c383061c383063c58f1e7d1a33e6cd9b36001f00005551555001e3c78f363c79b1e3e1e3c7c000a3c3830e0c3830e0c3830e0c0154387061c38305001e3c78f162c78f1e2c78f1e3c78f365cdc6cb9b8fa3467c000000000f99c011400155554003830e0c387060c387060c3830e0c3830e0c015401e0f00783c78f1e02c78f1e3c2e0047d1a33e0000007cce00ae75478800aaaa802a03c0000078f1e6c78f1e6c78f1f0f1e3cd8f800014787061c181c00061c187061c1870600aa1c383061c383063c78f1e3c78f1e7cf9f3e0b0582c4160b555162c078f1e3c786e365cd97370b16002c5aaaaaaa0aaaa87061c187061c187061c1870061c383061c38306aa3c78f1e3c78f1e7cf9f3e0f160b1602c587cce0b058b1e2c58b1e2c5802e162c597170b162d5cea8f555541545a4d55551e7c78f1e3cf8f463c78f878f1e3e162c58b001e0b162c58b162c58f1e2c58f162c58b51e1c187061c187061c187061c01870e0c1870e0c1aa870e0c1870e0c18f1e3c7d55500281b366d19b366cfd555000000000022aaaa82800007061c187061c1d5070e0c1870e0c1802a8f1e3c7d55503c01e01f011810000046700015cea8f55550110005479b1e3c79b1e3eaaa800078f01e000000a3c3830e0c3830e0ea800607000550e1c1830e1c1831e3c78f1f0f8bc5e0582c160b12555162cb9b2e5cb9b2e5e878154002e5555554155550e0c3830e0c3838187838030e1c1830e1c183551e3c78f1f0f8bc5e0582c160b233850b1e2c58b1e2c58b3e2c58b462c58152b9d51eaaaa82aaaaa8f563c78f463c7d0f1e3cbd0b16002c58b162c58b163c78b163c58b162d4787061c187061c1c0c3c1c01870e0c1870e0c1aa870e0c1870e0c18f1e3c78280172e5cd972e5cd8f87c5e2f0b1743c5d000000000028a3d54001554003830e0c3830e0c387060c387060e061e00551e3c78f007803c04601f1f0f8bc5e0160000000119d5cea8f55100155005479b1e3c79b1e3c07800000f1f43c78f2f40000a3c3830e0c3830e0c0e0003818780154387060c387060c78f1e3eaaa8160b0582c855568d9b368cd9b367c2aa058b00162d5555550555543830e0c3830e0ea838030e1c1830e1c183551e3c78faaaa0582c160b0a233c3ea1f51fa91d010b95cea8f5555415649aaaaa3d58f1e3d18f1f55542c5800b175543c7d0faa51e1c187061c18707541c01d40e0f4aa1c383061c383063c78f1e3c78f1e3c78f6878f1f0f1e3e1f172e5cb9787c7c78f1e3cb85c5970b8b368cd9f8b97955555555555543830e0c387060c387060c3830e0e061e0e0c383551ea8f1e3c79b366cd82c1602c0582c162c58b163c58b362c58b162c58b16aaaaaa82aaa1c187061c187061c187061c0187061c1aa8f5478f1e3cd9b366c1e2c162c058b0d99c582c162c58b163c580b162c780b162c58b162c5aaaaaaa0a8b73aa87061c187061c187061c1870061c18706aa3c78f1e3d1e3d55478f1e3c78f1e7d1a33e6d5cacdc3c78f1e6d19b3e6c362cd86c59b566d5aaaaaaaaaaaaa87061c187061c1870e0c1870e0c187061c187061c1aa8f1e3c78f1eaaa5cf9761f0f8bc5cb971e3c78f366cd9b2e17165c2e2e2e5e5555555555550e0c3830e0c3830e1c1830e1c183818783830e0d5478f1e3c78f61f172f172f0f878f1e3e8b972f43c78f1f43c78f1e6cf9b3f172f1b0f8b361f16aaaaaaa935555543830e0c3830e0e061e0e1c1830e1c1830e0c3835556367cd9f1e3c78f1e2c166cce0b058f163c581b171c58b165c597162c5c2cbc2c5aaaa2d26aa1c187061c187063c78f1eaab45dfa32e8dfb0f1e3e2f17878f1e3c78f1e6df9b3617165c362e2e5e55555555555550e0c3830e0c3830e1c1830e1c183818783830e0d5478f1e3c78f1e3c78f1e3d5cea8f5555555478f1e3d18f1e3e1e3c78f878b1e0f078b51e1c187061c187061c187061c18706aa1c383061c383067c78f3e5cd8f1e3c7972f51787d23b3972f45cb974e3c7a73e8d19f2e17165c2e2e2e5e547ab9d55555555555267c993264d193464c9932e4c993264c99726bc993264e8993265e898b2613098b51e1c187061c187061c383061c38307030f07061c1aaa0c387064c1830e4c387060d18f1e8eaa9a96954993264cb97264eaaa938f1e9d1a3468ea958ac5ab158b5555555555550e0c3830e0c383aa0e1c1830e1c1830e0c38355463c7a3aa91d9eaa3750fa8bd5271e3d3a3468d1d5442e2951eae75555555555549a3264c9a3264eaaa89d555132744ea898b2613098b51e1c187061c187075550383d07061c1aaa0c387064c1830e4c387060d5478f5463c7a3a264c9c4c99787c5cbd132745e64e3c7a72e17165c2e2d1a3468e2e5e5555555555550e0c3830e5c387060c387065c1830e0c383818783830e0d54b971e3cb8f1e3cb9b2e9d18f1e8ea2f0f8b972e5cbd48ece9c78f4e5c2e2cb85c5a3468d1c5cbca8f573aaaaa4d26aaaaaaa932e4c993264c997268c993264c9a3264c993464d1932744e264c9972744c5930984c5a8f0e0c3830e5c387060c387065c1830e0c383818783830e0d55061c383260c187261c383079c58ad3e3c79faaaa91d9d5a552e5c993264c993aaaa4e3c7a73e8d19faaae2b162b16a3d55555547aaaaaa1c187061c18707541c383061c383061c18706aa83 25 33554431 10 1023
def hc_70_10 : Nat → Nat := unpackHintV5 0xefc910eb4d1fe4bda4df6157d5ca66cf2da7c5766ebfa973b9cd77b0525fa9ed999fd6869ba10d9499c28a8a8486590c7ec1e674fa726d85dd6615dc5f9d9e582ddc5319454617413f1dbe35766a2e6dc22689f918c3721179d2079e770001e7 0xf9f2e3c79b02022e5e2e42e3e7cf9f0aa858ba800000126934ba5c3830e0c3830e0cd9b2e5cd9f3e6c2165e00026a4c9aaa4d2606c78f2609132f2a00930e0c3834187061c19f3e7cfc7e3f238fa73e3cf8f3e9c0a162c5d0000000000027d51a7d6526a7c98007061c187061c1c0c3c1c383061c38306001d41d1b365cb973e7cb972f59c7c3ea363c79b2e5cb973e7cb9f8e2c58b0aa0000049a4d26930e0c3830e0c383a8d8f1e6cb972edcba32e5c01e0f00d89c001e0b000582c0460559e1f50faa820000b82c00000000233a3d2ea5c9a9726974b88004d98003830e0c387060c387060c3830e0c0e0003aa000ea0c78f1e3c7b787d59ecf0f1e9d39b4e6eace567ce0000019c338023d1e974bb9e73c974b8007061c187061c1d507069c3a706001d41d43d18f1e3c78f6e3c78f1e000b058003c1600f07803c011807e1f43eaacf545e0800001e0b0000000089478f51e4d1e8f4ba5c40026b2c001c383061c383061c187061c18706070001d50007506bd39b1e5c78f2e5cbd55672f1780fa3467cb972e5cd9b2e9d78b162ea800001269349a4c3830e0c3a7060d3870e0cb9b2e5cb97aa8bc7cf9f3e1400559c8bd00005c0ce000025d2e974bb325d2e001c187061c18707541c18706001d41a35e8d797365c7971e5cbd400f000462300f80017058002c17555678bd45e08000002e0b00000008ce974ba5d2ea5c9a97262001366000e0c3830e0c3830e1c1830e1c183038000ea8003a832e5cb972e6eb3d9e8bc7cf9f3e5cbc3ab3959f3800000670ce00974ba5d2ecc974b8007061c1872e0c3832f541c18706001d41972e5c7971e5cda3468d1d400f0198002c16001705808c460232a8bd17a2f554100000005c1600000119d2e9752e4d4b934ba5c40026cc001c187061cb870e0c1870e0cb83061c18706070001d5000750600f0004605500b000000008ceaa2001358003830e0c3830e0c0e000381878003a831e8e1e3c7d50f1f4bcdd555555505402c160b0580b1602c59123d1ea355aab26aac9b3202c3830e0c3830e0c387060c387060ea838030ea0c78f479c78f1e3c78f1e3d78faaaaaaaa0582c160b0162c058b0a233c3ea1f51faa4723a87c3eaa1f55010b91e8f51aad479351e3d99016b135a0e0c3830e0c3830e1c1830e1c183aa0e00ea0707a0ea0cd8f1e8f39ba87d46cda31e3c7d511540b0582c16519d26934da6c3830e0c3830e0cda31e3c78f479e366eaa878faaaaaaaa0a80582c160b0162c058b0a233c8f4da8d56aac9aab26cc80b0e0c3830e0c3830e1c1830e1c183aa0e00c3a83368c78f1e3d1e7368d18f1e3eaaaaaaa8160b0582c058b0162c288cf1ba87d47ea4751b93d5555010b91e9b51aad4d935364d99016b135a0e0c3830e0c3830e1c1830e1c183aa0e00ea0707a0ea0cd9b3f9e1e7cd9baaa1e3cfd1b366eaaaaaaa8160b0582c058b0162c891e9b4fa7d4f9353e4d990161c187061c187061c383061c38307541c018750751b4e3c7af366d1a74e8cda7aaaa8a0aa058b058b0162c058b0582c891e9b5364d4d9357afd990161c187061c383061c383061c18707541c01875063c79fcf0f1e3c78f1e3c78faaaaaaa2aa8160b0582c162c162c891e8f4fa7d1e8f6640587061c187061c187061c1d5070061d419f3e7d79f3e9cf8f3e3cfa7aaaaaaaa280160b058b058b0162c058b224faad469f5564d4f936640587061c187061c1870e0c1870e0c1d5070061d41af5f55540b0582c1614467aa1f5548e8085caaf599016b135a0e0c3830e0c383aa0e00ea0707a0ea0c78f1e3c78f1e3c78f1e3ea1f0fa3f672e5e8b972e3c78f1e7cf9f3e5c2e2cb85c5c5cbcae7547aaaaaaaaaaaa3cf8f1e3cf8f1e3cb8f1e3c78f1e5c7af1e3c78fa1e3c797a1e2c783c1e2d4787061c187061c1870e0c1870e0c1c0c3c1c18706aa1c383061c383063c78f1f5534aab43c78f1e5cb8f1f55543c78f1e6cd9b37546c362cd86c5aaaaaaaaaaaa87061c187061c1d5070e0c1870e0c187061c1aa8f1e3c7d547ecf550fa87d45ea878f1e3cfa3467eaa21714ae7547aaaaaaaaaaaa3d18f1e3d18f1f55555543c7d0faa1e2c783c1e2d4787061c187061c1d5540e0f41c18706aa1c383061c383063e1e3cbcc5e1f1b366cd9b366cdc5cbcaaaaaaaaa3c78f1e6c78f363e1e3c797878b1e3c78b51e1c187061c18707030f07061c1aa87061c18f1eaaa3c78f1f43c78f878f1f0f8b97a1e3e8bcc3c78f1e5c2e2cb85c59b366cdc5cbcaa8f55555555550e0c3830e1c1830e1c1830e0c383818783830e0d5478f1e3c78f1e3c78f2e3c78f1f50f87c5cb972e5ea3f671e3c78f2e17165c2e2cfa3467e2e5e573aa3d555555555551e5c78f1e3c78f2e3d18f1e3c78f463c78f463c7d0f1e3cbd0f163c1e0f16a3c3830e0c3970e1c1830e1c197060c3830e0e061e0e0c383550e1c1830e1c1831e3c78faaa9555a2e5c78f1e3c78faaaa1e3c78f366cd9baa361b166c362d551eaaaaa935555543830e0c3830e0ea8387060c387060c3830e0d5478f1e3eaaaa3f6787d43ea2f543c78f1e7cf9f3f5510b8a573aa3d55555926aaaaaa8f3e3c78f3e3c7d5555550f1f43ea878b1e0f078b51e1c187061c187075550383d07061c1aa870e0c1870e0c18f1e3c780280b163c78f1e3c58f1e3c79f3e7cf9b2e6e365cdc00000000000a28f55050055000e0c3830e0c3830e6c387060c387066c1830e0c3830055 24 16777215 10 1023
def hc_70_11 : Nat → Nat := unpackHintV5 0x7e430bbbc8d65d4128cdd37356b82c63295cb17b066ab7897e5535a4287a88136f3389665454752f8226451505fb4a7ca5963a64fb9b9e650cee3845cf2a02af4e112f6a10885bd63a028b1998da0b386504405701bc1900a5ee083537700e1b200001c3 0x363c78b366c58b162c58b1e3c58b162c58b370f97c8e7650502c160b058500b805848f4da8d56aac9aab26ab640587061c187061c1870e0c1870e0c1c0c3c1c01875066d18f1e3c7a3ce6d1a31e3c79b87cbe471b2f4ecbd02c160b0580b162c5802c5919c2859b162c58f162c59f162c5a3162c59b169c58b162c58b162c58b02a47a6d46ab5364d4d9355b202d45935162c3830e0c3830e0c387060c387060e061e0e00c387060c387060c3a83366e87c5cbd5502c1719c8d8b1e2cf8b462cf8b3e2c58b662d98b162c29269349a2c3830e0c3830e0ea363c79b2e5cb97465cbd59e1f50faa8160b0162c58b0b80b160b05919c2859b169c58b163c58f162c0058b162c58f0162c58b162c58b462c581523d2ea5c9a9726974bb3202d45935162c3830e0c387060c387060c3830e0e81d41c01870e0c1870e0c1875063c78fa878faaa162c160b8ce43c58f167c58b168c58b167c59f162c5b7170c58b16145cba4d26934583061c187061c1870750f463c78f1e3c78f1e3e1f43eaacf540f0162c058b162c160b0582c8ce142c780b162c5800b162c58b1e2c58b163c58f162c59f162c5a3162c0a9478f51e4d1e8f4ba5d99016a2c9a8b161c383061c383061c187061c18707541c01870e0c1870e0c1875068d7a35e5d7971e5c7972f555559e2f5178160b0582c058b162c2e02c5919c2858b162c78b162cf8b162c5a3168c58b00162c58b165c058b162c0a92e974ba5d4b9352e4d8bb480b5164d458b0e0c3830e0c3830e1c1830e1c183aa0e00c387060c387060c3a83368cb971f55550b160b05c672362c58b1e2c58b3e2d18b362cd8b162cd8b862c58b0a2e5d269349a2c3830e0c3830e0cb972e3cb8f2e8d1a34755545e8bd559c160b0b80b1602c58b160b05919c285b3162c58f162c5970162c58b00162c58b168c58b162d18b462c581525d2ea5c9a9726974bb3202d45935162c3830e0c3970e1c1830e1c197060c3830e0ea838030e1c1830e1c1830ea0cd9b163cd9b162c58b1e3c58b366cd9b87c7e3f1f2f47cbd02c1602c0580b1602c582c91e9b4fa7d4f9353e4d56c80b0e0c3830e0c3830e1c1830e1c1838187838030ea0c78f4e3c78f1e6d3a7370f8cf559ecf540b160b16440b0599e33c8f47a5d2e974bb3202c3830e0c3830e0c3830e0ea838030ea0c58b467d19f363c797365cd972e5d3975e055115672f17858b220582d269349a4cbc1c187061c187062c58b363c79b368d3a7466d39b4f0f829395338162c162c05c140b0582c91e9b5364d4d9359afd640587061c1870e0c1870e0c187061c1c0c3c1c018750745cf9f2e6c78f365cb972e7cf973eac0162eb38f87d4440b058b16449349a4d261c187061c187060e3e7cf9f2e5cb97a162e00aa2acf17a8bc0b059102c58bce17162c892e974ba5d2e976640587061c187061c187061c1d5070061d41972e5cb9f3e7cf972eaeaa2f0555670582c162c162c882092e974ba5d2e976640587061c1872e0c3832e1c18707541c01875067cf9f3e7d39f1e7c79f4e2c58b8fc7e47052b28160b058b058b0170502c93eab51a7d559353e4d56c80b0e0c3830e0c3830e1c1830e1c1838187838030ea0ea8160b0582c8ce142c58b163c58b162c58b462c58152aac80b5164d458b0e0c3830e0c3838187838030e1c1830e1c1830ea0c1e7c79b366e1f1f8fc0006cd80f1e0142c59b17400000000008f4da6d369b65364d4d93000e0c3830e0c38381878387060c387060c003a83366cd8f1e8f38f1e6cd8f1e3c01e01b000d8001b11808c4601f0dc3e365e8d97a472380580000000000046747a6d4d935364d369b10009a6d8003830e0c387066c1830e6c387060c3830e0c0e000381878003a831e3c1e3c78f87cbe4700f1e000006cdd0b163c5d000000000023d1ea359aed959935664c003830e0c3830e0e061e0e1c1830e1c183000ea0c78f479c78f1e3c78f1e3cd8f00783c01e008c03e000f0001e0f1f0f97c8e1e3e8797a01600000000000119d1e8f51add479351e3c40026bb6000e0c3830e0c3830e1c1830e1c183038000e061e000ea0c78f1e3c1e3d1e71f0f91c8e01e3c000d9b00a162c78ba000000200001e0b47a3d46a355b2ab26aac98007061c187061c1c0c3c1c383061c38306001d418f1e3c78f363c78f1e3c7a3ce000f078003c007803c04601f1e5e878fa1f0f91c8e01600000f058000000046751e3d479347a3d46a310009aad800387060c387060c3830e0c3830e0c0e000381878003a83363c786e1f2f91c0006cd8000f1f42c59b17400000000008f4da6d369b65364d4d93000e0c3830e0c38381878387060c387060c003a83363c785e1e5c7c5cb8001b338001f33800170580000001733808f4ba5d2e974b8800007061c187061c187061c181c00003a83366c78f1e3d1e7366cd8f1e3c01e0f00d89c0462300f8001b0003627370f97c8e365e3746cd97a016000001b05800000046747a6d369b5364d4d9310009a6d8003830e0c3830e0c387060c387060c0e000381878003a831e6c7af91c3c7c3cbc1b468d19b1e3d3c2c7c000000000a359a3d1ebb64da6c003830e0c3830e0e061e0e0d3874e0c003a83366c1e6cd800f1e06cd9b370f8fc7e3e5e8f97a000000000047a6d4fa9f53e4d4f935db0007061c187061c1870e0c1870e0c1c0c3c001d419b1e3cda7369e1f4ce0139b469d19b4f42c5a7174000000000008f4dacd7eb29b26a6c98007061c187061c1c0c3c1c3834e0c1874e1c38306001d419b366cdc3e365e365e078f1e3cd9b367e167e00000000047a6d369b4db26d36001c187061c19b0e6c1c0c3c1c18706001d419b366cdc3e365e366cd97cf1b363c78f1e7f3803c78010b3f00006c0ce000023d369b4da6d9369b000e0c3830e0c383818783830e0c003a83 25 33554431 10 1023
def hc_70_12 : Nat → Nat := unpackHintV5 0xd61a38cfe58dc90db6c3556ebd2d8abc2c40b65576b1693ba8723ea066039a15949259ef8b11d2851d7d7c2a3d7b6830766142705d81673e4861158a5aa99b5465914ff11d47a6133a1365342d792be2131ebf49163622089b67048106000120 0x58b166c78f369cd8f3e0f1e06d38f1e6cda73f1f371f468cf82c582c580b1602c582c160b05a3d36a6c9a9b26a34faa02c3830e0c387060c387060c3830e0c3830e0c38030ea0c79fce3c78f1e7c78f1e3c794003ddb31e5cb8f1e3c78f3e7c78f1f171f42c5802c160b058b169347a4d261c187061c187067c78f3f9cf9f1e3cd8f1e6ca83e007ddc73e5cb9b3e6c78f3f1f8f973f47cb97858b058b167c0582c162c5a4d26934987061c187061c18f2e5c78f1e3c8b9f2e2c78f1e5cf8b163c79fa1e5c79b858b162e1702c162c582c16974ba4d1e1c187061c187065cb971e3cb9722e6cb8f1e5cb973e2c5972e7e8f8f1e3e1f0b162c5c0b058b160b05a5d2e934987061c187a60c1d30e1c18b1e2c59fa85c0c18f1e3c78f1e2c78f1e550fa3f5540b0582c816442ca47a3d2e974ba5d990161c187061c187061c18707541c01875063e1e3c78f163c2e5cb82c160b0582c168f47a5d2e974ba02c3830e0c3830e0c3830e0c38030ea0ea1e3c78f1e3c79f1e3c78f1e3c58b162c58b163c78f1e2c78f2f9c8b97078b160b162f382c160b0582c168f47a3d1e974ba5d2e80b0e0c3830e0c3830e0c3830e0c3830e00c3a833e7cf9f2e5c7971e5ea2e5cb972ace5e2e5c802f0b160b0582c160b162f385c58b0582d2e974ba5d2e974ba5d0161c187061c187061c187061c187061c01875067cf9f3e7cf973e5cf85559eaa1f45e95c0b0580b0816442ca4ba5d2e974ba5da690161c187061c187061c18707541c01875068d1974e3cb8f4e145e0bc5e2f17858b160b0582c1602c580b160b1642d2e974ba5d4b9352e4d2ec80b0e0c3830e0c3830e1c1830e1c1838187838030ea0d1a3468c160b1602c588cce0b058b162c58f162c0170b162c5c2c58b551aa80b5164d458b0e0c3830e0c3830e0c3830e00c387060c387060c3a831e0f1e003c781b360015555555400000000008f47a8d5eacc9ab326cc001c187061c187061c383061c3830754001d418f1e8f38f1e3c78f1e3c79b1f555555540f007807c04600f078003c0020000000008ce00023d1ea357a8f26a3c7b3004c40003830e0c3830e0c387060c387060ea8006070000ea0cdc7e00050e1cd8f1e17a87d41b000f8000000000008f4ba5d2e974b8020007061c187061c187061c180070003a83363c786cd8000f1e00155555554000000001008f4da6d36a6c9a9b26cc001c187061c187061c383061c3830754001d419b363c78f1e8f39b366c78f1f55555551ba83600f00f808c03627000d800400000000119c00047a6d369b5364d4d9366009880007061c187061c1870e0c1870e0c1d5000c0e0001d419b360f366c0078f0366cdd55555555000000000023d369f4fa9f26a7c9b30007061c187061c1870e0c1870e0c1d5000750601b1e3cd9b469d3a3369eaaaaaaaa8000000000011e9b5364d4d9357afd9800387061c3830e1c1830e1c1830e0c383aa000ea0cf9f3e7cfa73e3cf8f3e9c0aaaaaaaaa000000000004faa8d4faaf26a7c9b30007061c187061c1870e0c1870e0c1d50007506bd7d555000f00046040000119c000557acc01310000e0c3830e0c383aa00181c0003a83366c58b162c58b163c79b162c58b1e3c58b370f8f94147e3f02c161402e0582c1648f4da9f26a7c9a7d3eab640587061c1870e0c1870e0c187061c1c0c3c1c01875066d18f1e8f38f1e6d18f1e3cdc3e365e9197a47238160b0162c058b0582c8ce142cd8b162c78b162cd8b462c58b162cf8b162c58b167c58b168c58b02a47a6d4d935364d46a355b202d45935162c3830e0c387068c1830e8c387060c3830e0e061e0e00c387060c387060c3a83362c78fce3cd8b165e2f02c58b3602e3390f163c59f168c59b166c58b166c5c3162c58524d26934587061c187061c18f163c78b162c58f1e2c5b3362c58b162c58f87cbe470f2828160b0582c2805c0b247a3d46ab5564d559355b202c3830e0c3830e0c387060c387060e061e0e00c3a831e3d1e71e3c78f1e3c78f1e3e1f2f91c3c7d0f2f40b0582c1602c580b164670a163c58b163c58b167c58b168c58b163c58f162c58b163c58b162c581523d1ea355a8f26a3c7aad9016a2c9a8b161c187061c187061c383061c38307030f070061c383061c383061d418f1e2c58b162c5a3362c58b162c58f1e2c7850f287c3e472381e02e0a8160b0582c8594aac9aab268f47a8d46ab6405870e0c1870e0c187061c187061c1c0c3c1c01875063c78f1e3d18f1e3c78f1e8f38f2f43c7d0f87c8e4703c058b0162c58b0582c160b233850b1e2c58b162c58f163c58b162c58f162c58f162c59f162c5a3162c0a9478f51e4d1e8f51a8d56c80b5164d458b0e1c1830e1c1830e0c3830e0c3838187838030e1c1830e1c1830ea0cd8f1e8f39b363c782c591b9dc6c59f160b362cd8b162c58b04da6d43830e0c387363c7a3ce6c58b163c58b166cd8f1e2c58b22373b888160b049a4d369b0e0c3830e0c383 24 16777215 10 1023
def hc_70_13 : Nat → Nat := unpackHintV5 0x813eee3e7f881e5eb84e92674746e093a1c06dc2a390d7827467fef0b2975a1882326b57ba656feefa7b2f352c1c5e88277a408ee11dada68dbbc6c6592132b79d414445e0a1583248e5f21f59468c53d64526c0c1e8aab0c0ecd83f484c110ba6000221 0x1b1e3cd8540003c797465cb971e5cbd11bb3978bc5cb97000000000047a5d2e9752e4d4b9352eb0007061c187061c1870e0c1870e0c1c0c3c001d419b463c7a33600f1e2c5a3166c79b1ebc79b4e8d1a3466d3a7939b800000460000008f4da751a8d4d935364d5780070e0c387061c187061c383061c383061c18706001d419b1e3cd80051b2e2c59b166cf943e91c8e1e3c00000000000011e9b4da6d4d935364d36c001c187061c187061c383061c38307030f00075075003c036001b0002e27363c79b366cda3368cd9b0170fb38f1f43c78f0b8012391c00000000008cce008f4da9b26a6c988004d369b4db0007061c1870e0c1870e0c181c00061c18707030f00075079d26e726b1b1e3c78f0a001e3c58b1e2c78f1f451f91c6cb800000001f3380000023d1ea34fa93526af6000e0c3830e0c3830e1c1830e1c18381878003a83a8001e0f0007800f0078f463c78f1e3d18f1e3c780b1e3cd8f1f50fb385c008fc8e00000000003e670051e3d479347a3c40026a34fabd800387060c387060c3830e0c0e00030e0c38381878003a83468d1a35e9cb8f5e3cba7a162d18b2f178bc5e465d1c00000000000025d2e974ba9726a5c9a5d978007061c187061c1870e0c1870e0c1c0c3c001d41803c0468d1a3016bd780048d1a3460000008cce00a2001351a8d578007061c181c00061c187061c18706001d41c3c7c6e8f8f1e7cf8f1e3c582cf99c160b1e2d98b1e2c78b0662e18b162cb8b2e2c58b8597858b49a4d268b0e0c3830e0c3831e3cfe71e3c78f1e3c78f3e3c78f1e3cf9f3e7c78f1f0f1f03c582c580b161f3380b162c583c058b0582c58f162c58b1e2c78b160000b162c58b1e02c58b162e162c58b858b168f47a7d3ea3c9a8f1eab55a02d45935162c3830e0c3830e0c387060c387060c3830e0c38030e1c1830e1c1830ea0cdd1b1f50f3e3cd9b3f1fb39b367c582cf99c160b0362d38b1e2c78b0762e18b162cb8b2e2c58b85c2cb8b2f0b16a9349aa4d161c187061c387061c19b3e3c78f1e7f39b3e7c78f1e6c78f367cfa33e7cf9b3e7e3e6e0f8b058b0162c3e670162c58b0f80b160b058b362d38b162c78b1e2c580002c58b162c780b162c58b858b162e162c5a3d36a7d4fa9b26a6c9aad5680b5164d458b0e0c3830e0c187060c387060c387060c3830e0c38030e1c1830e1c1830ea0e858b162c5c6c78f366cb823467c170f1e3e162e878fa3f2384e2c162c058b0162c160b05923d36b1c9abb26a34faed90161c187061c383061c383061c18707030f070061d41d46c78f366d19f3e8d19b3f0fb38f1f43c78f3f2384e2c162c058b0162c058b1199c1642cd8b4e2c58b1e2c78b162cb8b4e2c58b162e38b162c58b02858b165e858b168f4da9b26a6c9a8d3ebb6405a8b26a2c587061c1870e0c1870e0c187061c1c0c3c1c01870e0c1870e0c1875063c78f1f555542c58b163c78b16155155540b0582c888058b0a47a3d3e9f6653e4d4f9340587061c187061c1d5070e0c1870e0c1870061d418f1e3c7c3ecf55550fa3f51faa81e2c162c058b0f99c882858b20a163c58b163c58b02aaa85d5550b1742ea858b168f47a7d3eccb135a405a8b26a2c587061c187061c1d5540e0f41c01870e0c1870e0c1875063e1e3c7c2e3f1f81e2c162c058b0f99c582c858b162c58f179c580b162c780b858b162cb8b858b168f47a7d3ebb6405a2c9a2c587061c187061c1c0c3c1c0187060c383061d41d0b162e162c78f1e0f1e03c78f1e7cbd0b1743e171f8fc02c580b160b0582c160b253e4d4f9347a3d3e9f5db202c387060c387060c3830e0c3830e0e061e0e00c3a83a878f3e8c78f1e3c78f3e3c78f1e3c78f1f50fb39f8fc0f0162c058b162c1e2c162c058b0f99c1642c78b162c58b163c58f162c58b163c58b162c78b1e2c58142e162c5971742c58b51e3d479347a3d3e9f5db202d45935162c387060c387060c3830e0c3830e0e061e0e00c387060c387060c3a83a367cf9bace3e1f0f160b0582cd99c78b362c78b1e2cb8b2e2c58b362e38b162c2a858b49a4d268b0e0c3830e0c383cf9d269b1e3cdd543ecf551b2e2c58b162c58554555509c582c580b162333c4402c58523d36a34fb32935c64d0161c187061c18707541c383061c383061c01875066c78f37550fb3d5547ea475509c582c580b16233391042c2859b162c58f162c0aaaaaaa162e85d50b162d1e9b51a7d99626b480b5164d458b0e0c3830e0c383aaaa060e8387a0e00c387060c387060c3a833e7cf9f3e7cf8f3e3cf9fa8fc7e8fd9cf9fa3e7d187c582c580b161f3380b162c587c058b0590b3e2c58b1e2c58001542e0162c58ba170b162cb8ba162c5a7d3ea7d4fa9f26a7c9aad9016a2c9a8b161c187061c187061c383061c38307030f070061c383061c383061d419f3e7cfd55507c582c580b161f33910b3e2c58b1e2c58155542c58b264c993264d274c2c058b162c98b262c587061c187061c1d5070061c383061c383061c187067cf9f3e7cfd55547ecf1fa87d47ea83e2c162c058b0f99c882858b20a167c58b163c58b02aaa85d0050b1741542c58b4fa7d3e9f665a26cb480b5164d458b0e0c3830e0c383aaa81c1e838030e1c1830e1c1830ea0c161f1e3cf8023138f1e9c00fa3467c58b162c78b01600b162c5a3d4e00a34faa2d161c18706001c187061c187061c187061d418fce3f38b1e3cce3cf8f1e6c79b3e7cd9f3e7cf8f1e3c7b31e0b0599c599c582c582c582c169b4da7d3e8f47aad5680b0e0c3830e0c3830e0c3830e0c3830e00c3a831e3cf8f1e3c78f3e3c78f078f366cdd0b8dd9cfc7e058b058b0582c160b05923d1e9b4da7d3ebb640587061c187061c187061c1c0c3c1c018750742c58b858b2e3cb971e3cb9f363c79b2e5cb972f0b8d978bc02c580b160b0582c160b252e4d4b9347a5d2e974bb202c387060c387060c3830e0c3830e0e061e0e00c3a83 25 33554431 10 1023
def hc_70_14 : Nat → Nat := unpackHintV5 0xf2eacceb31eee3ddd5db9e10d481c7ca8e7dc48582bc8dfeb585c2ab4a8fa66938a0199497e20e8d62a0878d757f4a1179e5597449676db5a567fd6e6105be5a29b75561324d16133fd750386dda2fea2122576519c225108e4d080e20000203 0xd9b1e3c78f3f9c362700783c0161b366c78f1e0002c580f16006c78f367cf9f3e0401b366e366e000d87cce000006c16000008f4da6d36013105364d4d934da6c003830e0c3830e0c0060700e1c1830e1c1830e0c383000ea0c7e71f9c1e3c5e71e7c78f363cd9f3e6cfe73e7f39f1e3c78f000ce19c00001369b739f739f47a3d56ab000e0cf873e0c3830e0c3830e0c3830e0c003a830a00363c79b2e3cb971e3cb9f2e5e2365cb972f1f2e5e000000000047a5d4b9352e4d2e974bb0007061c1870e0c1870e0c187061c1c0c3c001d41806c78f369cd8f3e2c78f162cd8f1e6cda73f1f371f468cf8000000000023d36a6c9a9b26a34faad56001c187061c3834e0c1874e1c383061c187061c18706001d4185001b2e2c59b466c59b1e3cd800f1e043e3f238000000360000a6c9a9b268f4da6d369b6000e1c1830e1c1830e0c3830e0c38381878003a83a8d8f1e6cd9b367cda3366c3600f00b89c00360002c87d9c78fa1e3c79f91c04170000d800008cce0000023d36a6c9a9b269b4d804c4136c001c187061c383061c383061c1870600303840c3c001d41800f1e03c78f1f42c5d545050055000000000023d1ea7c9a9f269f4fb30007061c1870e0c1870e0c187061c1d500075063c78f1e0f007802c87d9eaaa808821f47ea3f4001410054000f0f99c00000020580023d1e9f4f804c4199626b4001c187061c1870600303855540e0f4001d4185000f1e3c78f1e3c58f1e2c58f88d970003f1f8000000000011e8f53e4d4f934fa7d56c001c187061c383061c383061c18707030f000750750f3e3c78f1e3cf8f1e3c783c000783c001e00f00583c79b1e3ea1f673f1f8082e000000f058003c3e67000001478f51e4d1e8f4fa7c02620bb6000e1c1830e1c1830e0c3830e0c38300181c2061e000ea0c36006c78f36001454040550006c003e67000047a6c011369b66000e0c383000e0c383aa000ea0cd97000363c79ba162eaaa02802a80036000008c00047a6d4d935364d369b66000e0c3830e1c1830e1c1830e0c383aa000ea0cd8f1e6c3600f0059550fb3d5011046e8fd52391d0005040150006c466700000000011e9b4da6c02620ccb135a000e0c3830e0c38300181c2aaa8183a0e1e8003a833e7cf9f3e7c3e00f00587cd9f1e7c79f3750000b1614007e3f47ece7cfd00501703e7d18007c3e67000003e0b000004fa7d3e9f0098829f26a7c9aad8003830e0c3830e0c0060700e1c1830e1c18381878003a833e7cf9f0f803c016555401100007c3e67000000993264c99349804c2614c001c187061c18706003038550007061c19f3e7cf87c01e00b2aaaa3f2300a0823750fa8fc001410b00a8003e1f33800000040b0004fa7d3e9f00988332d1365a000e0c3830e0c38300181c2aaa0707a000ea0c78f1e3c79fce3c7c2e163c7ab1ecc58b165c7971e3c79b1e07cf8f8bc000009349aa4d1e1c187061c187066c78f366c78f3f9e170b366d59b862c58b2e6cb9b366c78f03e7cbc5e000d82c001269349a4c3830e0c3830e0cb972e5cf9f3e7eace178b972e5cb97000bc15000000005c0ce25d2e974ba5d2e974b8007061c187061c187061c187061c180075065cf973e7cf9f3f42f3d9ece554ae8bc000019c3380025d2e974ba5d2ed34001c187061c187061c1870754001d41974f0c7971f0d3a34742c597958b2f17802f178000000000012e9752e4d4b934ba5d2ec001c187061c383061c383061c18707030f00075066c78f36003c0586c78f367d1a33e0000b162c5a31602c58b162d1e9b51a7c0156ab45a2c3830e0c3830e0c003830e0c383161c5830ea0d1a3001e00b11a30200001199c00000551a013105000e0c3830e0c38300181c03830e0c003a83a162c58b171b1e3cda3119f0365c5c3e162e878fa47238160b0162c058b0582c1648f4dab326acc9a8d46af640587061c1870e0c1870e0c187061c1c0c3c1c018750751b1e3cd9b468d1a3466d1c3ece3c7d0f1e3d1c8e0582c058b0162c46670162c1642cd8b162c78b162cb8b4e2c58b162d98b162c58b02858b165e858b168f4da9b26a6c9a8d46af6405a8b26a2c587061c1870e0c1870e0c187061c1c0c3c1c01870e0c1870e0c1875063e1e3c7c2e3f238160b01602c1642c58b163c58b6e2e162c597858b168f47add3eaf6405a2c9a2c587061c187061c1c0c3c1c0187060c383061d41d0b162e162c078f1e0f1e3c78f1ebcbd0b1743e171f91c02c580b160b0587c582c582c95b9356e4d1e8f51a7d5ec80b0e1c1830e1c1830e0c3830e0c3838187838030ea0ea1e3d1a31e3c78f1e3d18f1e3c78f1ebc78fa87d9cfc8e0162c058b0582c3e670162c1642c78b162c58b163c58f162c58b163c58b163c58b02858b165e858b16a3c7a8f268f47a8d3eaf6405a8b26a2c5870e0c1870e0c187061c187061c1c0c3c1c01870e0c1870e0c18750742c58b858b2e8c78f2e5cb8f363c79b2e5cb972f0b8d978bc02c580b160b0582c1602c252e4d4b9347a5d2e974bb202c387060c387060c3830e0c3830e0e061e0e00c3a83162c59b463c7a33603c7a30d8f363c79b369d3c9cdc8d1a3460b160b1602c580b1623160b160b05a3d36a6c9a9b26a351aaf40587061c1870e0c1870e0c187061c187061c1870061d41a3468d1974ebc7971ebd397918145e2f179197470b162c160b0582c058b0162c162c85a5d2e974ba9726a5c9a5d90161c187061c187061c383061c38307030f070061d41a3468d1af5e8d1a3460b0588cce02c582c162c58b163c58b005c2c58b170b162d546a355e80b5164d458b0e0c3830e0c3830e0c3830e00c387060c387060c3a83 24 16777215 10 1023
def hc_70_15 : Nat → Nat := unpackHintV5 0xf0fe90eb895de58182e0cd2ddb1d6cd2da11cd8d53bf538fb849c2ad72b6a4b62f951be78ec99486e5f97e5e2273ea9d6c35ed64a1e55bae3d52a2434aa9fe44e1723ebd8935864e3474442e8d7a2532571d120814ce11106d180512d7000144 0xb02e8c0000118f1e3c78f1e3c788c00463c78f1f505c0087c3e3e7cf9f3f51fb380000f338000000008004d1e8f5464d519351a7d56c0007000187061c187461c383061c383460c187061c1c0c3c001d418f163c7d55547ece5543ecf5000150003c0000080ce23d1e9f4fb32d32c001c187061c187075540ea000ea0e858baa1e3c78f0003e5ea8002aa000000000011e8f53e4d4f934fa7d98003830e0c387060c387060c3830e0ea8003a83036001f1e3c79b002aaa800000d99c000001369b4da6d98000e001c187061c1870754001d4180b0f8007c78f1e3c800aaaa00000799c00002600131e3c78f264d274c0007000187061c187061c1d50007061c180b03e8c000f8f1e3c79001555547ece100000543ea87c3ea3f5400003cce0000040b00010009a3d1e9f4fb32d1365a00038000c3830e0c3830e0eaaa0707a000ea0c0588c001e3c78f000878f1e3c0000799c0000400268f47aa8001c00061c187061c187061c18706001d419f1e3cf9f363c78f1e7cdd49e1f48ece8d1d23468c058b0799c3e2c162c058b0162c16400b3e2c58b168c5a3162c597162c58b162d78b5e2c58b1742c58b2f42c58b47a9d469f5564d4f9355b202d45935162c3830e0c3830e0c387060c387060e061e0e00c387062c1830e2c387060c3a83463c7a3aaaaa0aa8162c58b465c58baaaa05902c164402c58523d4ea351b32ab26aac9a02c3830e0c3830e0ea8387060c387060c38030ea0d18f1e8eaa4767aa8dd43ea475402c583cce23160b1644142c5905002d18b162d18b1755542eaaa858ba17542c58b47a9d46a366589ad202d45935162c3830e0c3830e0eaaa0707a0e00c387062c1830e2c387060c3a83460f1e3c78231e3d1d0b162e162d3c3e565e858ba470b8160b0162c058b0582c1648f53aab26aac9a8d46ab640587061c187561c383061c383560c187061c1c0c3c1c01875068cd8f1e8c78f1e8cda34e8c78f4752787c8d1a347523b380b160f3388c058b0162c58b118b058b059002d18b162c58b165c5a3162c58b168c58b162d18b462c5d0b858b165c5d0b162d1ea75464d519351a8d56c80b5164d458b0e0c3830e8c387060c387068c1830e0c3838187838030e1c18b060c38b0e1c1830ea0cd8f1e6eab39f8fc0b1e673e2c160b03e2cf8b3e2d18b2e2cb8b162cf8b5e2c58baa162d269349a2c3830e0c38b060c5870e0cf8f1e7eaaaa476782aa0f97162c58b162eaaa8058b0799e0f8b058b220162c291ea751a7d9955935564d0161c187061c18707541c383061c383061c01875067c78f3f555402c583cce1f160b164400b3e2c58b462c5d5550b162c98f1e4c99349d30b0162c58b262c98b161c187061c18707541c01870e0c583061c5870e0c187061c19f1e3cfd55548ecf1ba87d55402c583cce1f160b164410b0a0059f162c5a3162eaaaaaa858ba17542c58b47a9d469f665a26cb480b5164d458b0e0c3830e0c383aaa81c1e838030e1c18b060c38b0e1c1830ea0cf8f1e1f363c79f3742c58b1742cfc3e171fb39f3f47cfa30582c160b058b058b05923d3e9f4fa9f53eab640587061c187061c187061c1c0c3c1c01875068cd8f1e8cd9f1e3c468d5a787c7cf9f3e7e85c7ece0b0582c582c582c160b247a9d51aa355a7d56c80b0e0c3830e8c187068c3830e0e061e0e00c3a832e5c78f1e3cb9b3e3c79fa162c5c2c59787c5cb972e5e171f0582c058b0162c160b05923d2ea5c9a9726974ba5d90161c187061cb870e0c1870e0cb83061c18707030f070061d419f4e3c79f4e7c1e3c78f0162c5a71e3d39f468cf9f572b3f02c160b160b1602c580b160b05a3d4ea8d4faab26a7c9aad5680b0e0c3830e0c3830e1c1830e1c1830e0c3830e00c3a833e3c79f2e0f1e3c78173e5cbc3e171f2e5e2e5cb82c160b0580b1602c582c91e974ba5d4b9352e4d2ec80b0e0c3830e0c3830e1c1830e1c1838187838030ea0c87a72e5cb972e5d1974e5c5972e5c58b3746cb972e8cfc2c58b170b8160b162c160b4ba5d526930e0c3830e0c38321e9cb972e8cb972e5d397465cb97162cdd1b2e5cba34723858b162e0582c58b0582d2e9754b932eed4987061c187061c19f1e3cf9787c5cbc7cb9f2f9e3e6e87c7cd972e5e8f8b162c58b1740b0582c160b20162c058b47a5d2e974bb2973e4c9a7d4b9340587061c187061c1c0c3c1c383061c383061c01875062cb9b858ba17172ea8c78f46545cf8b2e8cfc6eaa2f502c8160b05910b291e974ba5d2e9759640587061c187061c187061c1d5070061d41972e3cb8f2e6cbe7463c7a3a887972e5c58b162c58b165cb972e2cb9f2f9c160b0b8b160b162c582c160b05a3d2ea5d4ba5d2e974ba02c3830e0c397061c1970e0c3830e0c3830e00c3a834e3c7a70a1f270ba32e8cba787c9cbc5e162c582c160b0580b1602c582c590b47a5d2e9752e4d4b9352eb202c3830e0c3830e0c387060c387060e061e0e00c3a834e3c7a74e3c7a70162c1e670582c582c1600b162c5a3162c5c2c58b170b162d1ea755405a8b26a2c587061c187061c187061c1870061c383160c187161c383061d418f0782c878f8dd1b0066ac2e5c01e3cf9f22e0f1e0f3e67000009a24d26030e07061c18f1e7f38f1e3c783c00783c0160f1e3c79b1e0002c580f16003c78f1e7cf9f3e8cf81003c78f878f8001e1f33800000f058000023d1ea7d4f804c41479351e3d56ab000e0c3830e0c38300181c0387060c387060c3830e0c003a831e3cd83c161ba363e87803b56172e01b367cf811700d9b0d9f338000004d126935018703830e0c387 24 16777215 10 1023
def hc_70_16 : Nat → Nat := unpackHintV5 0xe4c609df7155d23350cb01ccc13274ba01ccb17e21a37b819c71c29491f88a768781e22578ae4d70edf068821b603a125881ee546d054f19554749f446a82841e5313a35ec32e5d42b7dda2475c21ac26d19dc391551230f258b0759f30001d6 0x161f1e3cf807c4615404415523b3c6e4f50f87d0005040137aa0799c000000f80000023d4e0131051a7d99689b2d0007061c1800c0e01c187075550383d00075060b138f1e9c0118271e3d381000f338000000023d4e0131055000e0c38300181c03830e0c3830e0c003a831e3c78f1e3c78f1e3c78fa87c3e8fd9cf9fa3e7d183cce02c582c1602c580b160b20059f162c59f162c597162c58b162cf8b5e2c58b1742c58b2f42c58b47a3d3e9f53e4d4f9355b202d45935162c3830e0c3830e0c387060c387060e061e0e00c387060c387060c3a831e3c78faaaaa80a162c58b365c58baaaa07c0b160b059100b16148f47a6d36cca6c9a9b2680b0e0c3830e0c383aa0e1c1830e1c1830e00c3a831e3c78faa8fd9eaa1f50fa91d503cce02c582c164410b0a005a3162c5a3162eaaaaaa858ba17542c58b47a3d469f66589ad202d45935162c3830e0c3830e0eaaa0707a0e00c387060c387060c3a831f0f1e7e171b87c0b0580b0160b2162c58b362c59b170b162cbc2c58b4da6d369b4db202d164d162c3830e0c3830e0e061e0e00c3830e0c3a831e3c0783c78f1e3c7d0b162e162c7c3e365e858ba3f0b81e2c162c058b0162c160b05923d1ea6c9a9b269b4da6d90161c187061c383061c383061c18707030f070061d418f1e3c78f1e3c78f1e8c78f1e3ea1f0f8f9f3e7cfd47ece0f3380b1602c580b160b0582c80168c58b162c58b2e2d18b162c58b462c58b462c5d0b162cbd0b162d1e8f5464d519351a7d56c80b5164d458b0e0c3830e8c387060c387068c1830e0c3838187838030e1c1830e1c1830ea0c78f1e3eaaaaa028d97162c58b162eaaa820160b059100b16148f47a6d36cca6c9a9b2680b0e0c3830e0c383aa0e1c1830e1c1830e00c3a831e3c78faaaa0799c058b0582c880167c58b167c58baaaa162c58f1e3c7932693a61602c58b164c593162c3830e0c3830e0ea838030e1c1830e1c1830e0c3831e3c78faaaa8fd9e1f50fa8fd503cce02c582c1644142c5905002cf8b162cf8b1755555542c5d0baa162c5a3d1e9f4fb32d1365a405a8b26a2c587061c187061c1d5540e0f41c01870e0c1870e0c1875063c78f1e3c78f1e3c78f1f42c58b858b1f0f8b972e5cbc2e3e0b0580b1602c582c1602c247a3d4b9352e4d2e974bb202c3830e0c387060c387060c3830e0e061e0e00c3a831e3c78f1e3c78f01e0f1e2c58b1e3c78f3e8d19f36ae566e078b058b058b058b0162c058b0582d1e8f51a7d4d935364d56ab40587061c187061c1870e0c1870e0c187061c1870061d418f1e3c78f1e03c1e3cb9f2e3e1f0b8bc5cb970582c160b0162c058b05923d1e974ba9726a5c9a5d90161c187061c187061c383061c38307030f070061d418f1e3c78f1e3e1f172f172f0f878f1e3e8b972f42c58b1740b0582c160b20162c058b47a3d2e974bb29726a5c9a02c3830e0c3830e0e061e0e1c1830e1c1830e00c3a831e3c78f1f0f028bc7465d1c71f0f1e3e2f17858b160b0582c1602c580b160b1642d1e8f4ba5d4b9352e4d2ec80b0e0c3830e0c3830e1c1830e1c1838187838030ea0c78f1e3c78f1e3c1e670162c160b0582c0162c58b462c58b858b162e162c5a3d1eaa80b5164d458b0e0c3830e0c3830e0c3830e00c387060c387060c3a831e3c78b1e3c0f951f8fd50f87c007c03f17a07800002a9f49b03061c18707030f0f1e3c78f1e54003c58f1e151f8fc7cf9f3e5cbc7e3e0f00000549a4d2e97060dd870e0c39f060c3830e0c78f1e3c78f1e3c78f1e3c2a0001f0f8b97a23f672e5cb800000000023d1e974ba9726a5c9a5d8003830e0c3830e0c3970e1c1830e1c197060e061e000ea0f39349da4d478f1e2c78f0567cb973e0f0005526aa4d264d1e3c78f00545626ee004983061c187061c187063c78f1e3c78f1e2c58f163c7803c78f1e7d1a33e7e3f0003c0000000011e8f546a7d49a9f26a001c187061c1830e0c1870e0c1870e0c187061c180075063c78f1e3e1e3c78fa2e5cb8f87c5cbc5cb8140000000000008f47a5d2ea5cf93269f52e4d2ec001c187061c187061c383061c38307030f000750742c58f163e1e3c78f2e8e1c3465c7c3c78f802f178000000000011e8f52e4d4b934ba5d2ec001c187061c383061c383061c1870703061e06001d418f1e3c78f1e2c58f163c7973e5c7c3e28bd172e5c00000000011e8f4ba5d4b9352e4d2ec001c187061c187061c383061c38307030f000750602c3e001f1e3c78f03ebc00000b8f1e3c78f1e3c7d4170021f0fa3f673e7e8f9f4600003cce000000002001347a3d3e9f53e4d4f9358000e00030e0c3830e0c3830e1c1830e1c18381878003a831e3c0081e0a0c18f163c7d5515550faaa0007800000023d1eab4fb32cb0007061c187061c1d5503a8003a83a162ea878f1e3d197000aa000a8a00078000000023d1eaac9aab26a34fb30007061c1870e0c1870e0c187061c1d5000750602c11a3000463c78f1e4005551fb3d5040000150fa87d48ea80000799c00000000400268f47a8d3eccb135a00038000c3830e0c3830e0eaaa0707a000ea0c78f1e3c78f162c78b1e3c28007c3e3f451f2e0000003cce000000008f47a8d3eaac9aab26ab6000e0c3830e0c3830e1c1830e1c18381878003a83 24 16777215 10 1023
def hc_70_17 : Nat → Nat := unpackHintV5 0x7ec91fbd97735cfc73edfd2046bdf02b3cc88d812f4eb8f9e7590adca9c3b093e6bec934efa45faeb210f7b8f834127441f635c31798b28bcbd7a0659e5362948ea92be79887eb823cc5cc1ae6df0af69f44ba3041dd9fe0b68e10309aac0bab28000175 0x1b463c7a3366d1a31e3e91c6c79b4f0f91c8e369e93d1b1e3cda7368cda3361b166c362e3723d369d46a35364d4d9359369b0e0c3830e0c3830e1c1830e1c183818783830e0c3a832e5e1e5cdd0f8b976759ecf45eb3d567b3a71e3d3972e5cb9f66ccfd523d2e974ba5d2ecc974b87061c1872e0c3832e1c18707541c187061d41d45cb8f1e5c78f1e5cd974e5cb97465c7971e3c78f1e5cb974e8c78f465cb972e8cb97468cb97aaacf0fa87d17a2f55674e3c7a72e17165c2e2cb85c5970b8b468d1a3aa47a5d4b9352e4d4b9352e4d2e97664ba5c3830e0c387060c387060c3970e1c1830e1c197060c3830e0ea83830e0c3a831e3c7c3c7d550f1f5550faa8bd545e1e3c78f368cd9f2e17165c2e2ea8bc8f47a5d2ea5c9a9726b2c974b87061c187061c1870e0c1870e0c1d50783830e0c3a831e8c78f1f0f1e9c7d50facf567b3d567b38f1e2c78f166d19b3e6cd9b3767acf23c7a3c9a5d2e974bb9e73c974b87061c187061c187061c1d9eb3c1c187061d418f1e3c78f87d45cbc7b3d59e2f59eab3d9c78f1e3cb97165cb8b3eddb9faa2f23d1e97269726974bb9e73c974b87061c1872e0c187065c1830e0c383b3d6783830e0c3a83a878f2e8c78f1e3c78f1e3c78f2e3c78f1e3c78f1e3c7971e3d1a31e3c78f1e3d18f1e3c7d50fa1f55678bd17aab38f078b1e0f163c78f1e5c2e2cb85c59f468cfd5179478f51e4d1e8f52e4d4b934ba5d6592e970e1c1830e1c1830e0c3830e5c387060c387065c1830e0c383aa0f07061c1875068d1a31e8c7a3468d1a3aa91a3468ea47674623168c462d1a3468e9551935464d46a35943830e0c3a30e1c1830e1c1a3060c3830e0e061e0e0c3830ea0c7e7878fcf43e2f9eab3e7aa87d17a670f1e3c79f3e7cfb32e5d9d523d1e974ba5d2ed34974b87061c187061c187061c1d507061c1875063c79fce3c78f1e3c78f1e7c7d55547ecf5550faa1f543e1f51fa1f0faa87d5550f1e3c79f3e7cf8f078b1e0f175510b8a47a3d3e9f51e4d478f665a26cb4b75b87061c187061c1870e0c1870e0c1d5540e0f41c187061d419f1f9c7e78bd43f3d567cf46eaa2f4ce3e3c79f3e7f39f3f9db972ede2891e974be74be74ba5d69964ba5c3830e0c383061c1830e0c383aa0f07061c1875067cf8f1e3c79fce7cf9f1e3c7d55547ecf5551faa3727a87c3ea3f46e4f550f87d5547c78f3e7cfa33e7cf9f0f8b3e1f175510b8a47a7d3e8d3e7d4f9353e4d99689b2d29d6e1c187061c1830e0c1870e0c1870e0c1d5540e0f41c187061d418fce3f3c3c79bce3cf8f1e6c7d559eb3d5546cd9b366cf9b3e3c1e3c1f549b4da7d3e8f47b326d361c187061c187061c3830e1c1d507061c1875063c7c3c78faa1e3e8b972f5555555543c78f1e6cf9b3e6c3e2cd87c5d523d1e974ba9726a5c9b325d2e1c187061c187061c383061c38307541c187061d41d46c78f369cd8f3e3c79b4f5555555546d38f1e6cd86c59b0d8b368cd9faa47a6d4d935364d469f664da6c387061c3830e1c1830e1c1830e0c383aa0e0c3830ea0cf9f3e7cfa72e3cf8f2e9eaaaab3c8ea47373e7cfa3467cb8bc5af0b8baa4ba5d2e9752e4d4b93664ba5c3830e0c3830e0c387060c387060ea83830e0c3a831e3cfe71e3c78f1e3c78f3e3eaaaaaaa878f1e3cf9f3e7c783c58f078baa1e3c78f264d263c78f263c98f1f4c4c993261c187061c187061c383061c38307541c187061c187067cf8f1e3c79fce7cf9f1e3c7d55555551f1e3cf9f3e7cf9f0f8b3e1f17544c78f264c9a4c993264c993264e98993264c3830e0c3830e0c387060c387060ea83830e0c3830e0d1a3aaaa468ea8993264c99349d313264c987061c187061c1d507061c187061c1a347555523b3d50faaa91a3aa885c52a8d665a26cb4a1c187061c187075550383d07061c1875067c78f3e5cb8f1e3c7973614005e1e3c7c5cbc47cb972e00000000008f4ba5d2ea5c9a9726976000e0c3830e0c3830e1c1830e1c18381878003a833e9c78f3e9cf8b1e3c78f162c04e3c7a73e8d19f3ece667e0000000000047a9d469f5664d4f935000e0c3830e0c3830e1c1830e1c1830e0c383000ea0cf8f1e7cf9ba1f1f365cb972f0f8b978b9702800000000000011e974ba5d4b9352e4d2ec001c187061c187061c383061c38307030f000750742c58f938b868cb97470d38f1e9c02e9e1f272f178000000000014b9352e4d1e974ba5d2ec001c383061c383061c187061c18707030f00075067c78f3e5c58f1e3c78b165cf972f0f88bc5cb97000000000047a5d2e9752e4d4b934bb0007061c187061c1870e0c1870e0c1c0c3c001d4182c3e3c79f00f88c0f9b1e3c78f3e6c000b82f5e0152787c0417091d9d1a3a468d183cce0000007c0000011ea70098828d3eabc9a9f26d36000e0c38300181c03830e0c387060c387060e061e000ea0e858baa00465c118f1e8c2802aa28000000000155935564d1ea751a8d9800387060c387060c3830e0c3830e0ea8003a830588c78f4602311855011048ecf551ba87d0005040123aa0799c0000011800102c0011ea70098828d46ccb135a000e0c38300181c03830e0eaaa0707a000ea0d18f1e8d18b1e3c78f162c28013c3e471332e000000000000008f53a8d46aac9aab26ab6000e0c3830e0c3830e1c1830e1c18381878003a830588cd8f1e3c7a3360008c0ba300463c7a301188c2a4f0f8082e08d1b7468ea47670799c00000001182c0046008f53804c4151935464d46a355b0007061c1800c0e01d1870e0c1870e0d183061c18707030f000750742c5d501f2e007c78f3e14015550000003c0000f802b726adc9a3d4ea34fb300070e0c1870e0c187061c187061c1d500075060b0f8f1e7c03e230aa0220a80799c000000f80131e3c9804c2604c9a4e98003830e0c0060700e0c383aa000e0c383 25 33554431 10 1023
def hc_70_18 : Nat → Nat := unpackHintV5 0x8d9590454461a16d4d4ff8af87c66d7bc387edd64adee5a1616fcec0b5c488d9fcb96c829ef6009032e83605565f709c97a6497934a28b8c4fad66274265133b19897d8800b0839049ef952112f90d06e0c55dc961f42eb09c377835c6140ad40400015a 0x2a363c79b2e6cdc736acb9b87d9c78fa1e3c7978bc1b160b16171380b162c582c160b161785c2c585000b362c58b362c580b162c7d0b162d1e9752e6d4b9b4ba5d2ec80b5164d458b0e0c3830e1c1830e1c1830e0c3838187838030e1c1830e1c1830ea0e8d9b3e7cd9f8e6cd9b362c59f166cb9b2e2c58b367e397365c07d9c7c3c7d178bc1b000004da6d526930e0c3830e0c383005815402c59b1e3cd88c002e6cdb7371cb9b87d9c78fa078010f1e3cbc5e000d80000171380017011e9710009a9736a5cda5d2e976000e0c383038000c387060c387060c3830e0e061e000ea0ea363c79b2e5cbbf2eacb9787d9c78fa1e3c7978bc6c78f365cb97365cd972e6cd9b37172f2aa4d555269355526aaaaaad2a93364c993364c9a8f1eaa4c5930984c5a930e0c3830e1c1830e1c1830e0c383818783830e0d54387060c387060ea4e3c7a74e8d1a787d9c78fa1e3c7d271e3d3a70589c5d23d4ea4d53935594e87061c1870e0c1870e0c187061c1c0c3c1c187061d418f1e3c78f1e3c78f1e3c78f1f55555555550f1e3c79f468cf9f178b5e1f17548f47a8d3eabc9a9f26ccb743830e0c3830e0c387060c387060ea83830e0c3a831e3c78f87d9eaaaa1f5523aa878f1e3d7afaa885c523d1eaf599626b4a1c187061c187075550383d07061c1875063c78fa878f1f543ea1e3ea1f178bd178bc5ea919f0582cdb7367e2e5cba4d26974ba83061c187061c18707071e3c7c3c78f1e5cb978bcdcf9f56dcfa3d49a4d549a4c9a4d1e3c78f55478f1eac4cbc2c05a4c1830e0c3830e87061c18f1e3c78f1e3c7d0f878f1e3c78f87c7e471f4f543c78f1e7d1a33e7c6e2db87c5cde47a3d469f526a7c9acb743830e0c383061c1830e1c1830e1c183818783830e0c3a83a87a31e3c78f1e3c78f1e3c78f1f50fb3d0f078b1e0f163c78f1f4a3c7a8f268f47aaca1c383061c383061c187061c18707030f07061c18750750f1e3c797469d3a32e9eacf0fa87d543c78f1e5c362cd85c59b5e6ea91e8f52e4d4b934ba5d992e970e0c3830e1c1830e1c1830e0c383aa0e0c3830ea0cfa71e3cfa73e9c78f1e3cfa7aaaaaaaaaa938f1e9cfa346bcf9f178b5e1f17548f53aa353eabc9a9f26cca743830e0c3830e0c387060c387060ea83830e0c3a834e3c7a7aa87d9eaaaa91d549c78f4ebd7d5442e291ea757accb135a53a1c187061c1870755540c1d070f41c187061d418f1e7f38f1e3c78f1e7d78f1e3c78f1e3c7d43c78f1e7c78f2e3d3d50f87c3c78f1e3e1f47ece7cfd1f3e8c78f87d0f1e5e878f1e3cf9f3e7d19f3e1f167c3e2c783c58f078b97af91e8f53ea7d4f9353e4d479351e3d5ecb75b87061c187061c1870e0c1870e0c1870e0c1870e0c1c0c3c1c187061d419f3e3c78f1e7f39f367d38f1e3c79f1e7cdd47cf9f1e3c78f1e3c7d51f87c7cb9b4e7e1f47ece7cfd1f3e8cf978fd1f3e5e8f8f1e7cf9f3e7cf87c59f0f8b3e1f167c3e2e5ebe47a7d3e9f53e4d4f9353e4d4f9357b29d6e1c187061c187061c383061c383061c383061c38307030f07061c1875066d3a7363d78f369cd8f3f0f1f46d3c3d7c6d1d1f4747e471b1e3cd9b0d8b361b166d19b3f2f3723d36a6c9a9b26a34fabd9369b0e0c3830e1c1a7060c3a70e1c1830e0c383818783830e0c3a831e3c78f1e5c78f1e3c7e71f50f1e3e1f5672f172e3e20bc3c78f1e3c79f3e7cf972e5cb972e5cba3d1e974ba5d2e974ba5d2e1c187061c187061c187061c187061c187061d418f1e3c78f1e5d78f1e3c78f1f50f1e3c79f1e3cb8f4e3e1f47ece5cbd172e5c78f2e3c78f1e7cf9f3e5cb975e5d7972e3c1e2c783c5c5cbc8f47a5d2ea5cba972ea3c9a8f1e9764ba5c3830e0c3830e0c387060c387060c387060c387060e061e0e0c3830ea0cf8f1e7cb9b2f9c78f2e5cbd45e1e5c7d59cbc5cb8f882f172e7c78f3e7cf9f3e5cb972e6cb972e5cba3d2e974ba9752e974ba5d2e1c187061c187061c3830e1c187061c187061c1875067c78f3e5cd974e3c78f1e5d7d45cf972e7cb8f1e3c79787d1fb3972f45cb972e5cb9f1e3cf9f3e7cf972e5d797365cb970b8b2e1717172f23d2e974ba972ea5cba9726a5c9a5d92e970e0c3830e0c3830e1c1830e1c1830e1c1830e1c183818783830e0c3a83363c79b369d39f4e5e1f178bc5d39b1e3cd9b466cf970d8b361717172f23d2e974ba9726a5c9a5d92e970e0c3830e0c3830e1c1830e1c183818783830e0c3a832e6cbe787972e5e87c5cbd4255517aab3c5e8f8f1e7cb972e5cf9f3e7ea91e974ba5d2e97664ba5c3830e0c3830e0c3830e0ea83830e0c3a83a8f8f1e7cb972e5cf972e8d1972e5cd974e3c78f1e5c7972e5cb97463c78f1e5c7971e5cb974f5559e1f50faacf17a8bc9c78f4e5c2e2cb85c59f468cf970b8b2e1717548f4ba9726a5c9a5d2ea5c9a9726c5da4ba5c3830e0c387060c387060c3830e0c387060c387060e81d41c187061d418f2e3c78f1e3f3c3ea1e3ea12aa8bd559e2f43c78f1e5cb8b2e5c59f3e7cfd523d1e97269726974bb325d2e1c187061c1830e0c187061c1d507061c18750750f1e7d18f1e3c78f1e7c78f1e3c78f2e8c78f1e3c78f1e3c78f2e9c78f2ebc78f1e3c78f1e3ea87d0faab3d59e2f5178783c58f078b1e3c78f3e7cf9f2e17165c2e2ea9478f51e4d1e8f4ba5d4b9352e4d992e970e1c1830e1c1830e0c3830e0c3830e1c1830e1c183aa0e0c3830ea0cf9f3e7cb9b2e5cb9f2e5ea0f803c03e02c165e2f47ece5cbd172e5c0b800005c5e00000025d2e974ba972ea5cb804c412ec001c187061c187061c383061c3830600303840c3c001d419f3e7cf973e5cb973e5cbd45e2f47ece5cbd172e5c160b0582c058b162c2e2f0590b3e2c58b1e2c58b3e2c00597162c58b4ba5d2e9752e5d4b974bb202d45935162c3830e0c3830e0c387060c387060e061e0e00c387060c387060c3a833e7cf9f2e7cb972e7cb97a8bc5e8fd9cb97a2e5cb9f3e7cf9f3e7cf972e5d5975e5cbc5cbcaaa4d5549a4d55555499f263c98f264c99f26aa4cb93262c984c262d4987061c187061c1870e0c1870e0c1c0c3c1c18706aa1c383061c383068d1af1ebc7d5523b3a34748d1a3468c5e2d782e9546aaf26a4d650e0c3830e0c3830e1c1830e1c183818783830e0c3a83a8da31e3d19b368c78f468cd8faaaaaaaaa363c79b361b166c362cda3368ea91e9b5364d4d9351a8d99369b0e0c3830e1c1830e1c1830e0c383aa0e0c3830ea0d1a3468eaa4767aaaa1f523aa468d1a3aa885c52a8d46ccb135a50e0c3830e0c383aaa81c1e83830e0c3a83 25 33554431 10 1023
def hc_70_19 : Nat → Nat := unpackHintV5 0xde4a52d4c262cb565bc29a2fba7e07b0e267ac9d11a6f16b9da25492d6b391945090b03982e3747e392a7879706fae3369f96d62b5d154af824f355e4ec81b48a5893ddab338ed3b2bbb4d240deb164f700da62a000369 0x2e9e87c7d39f1e3cf9f1e5e1e3e8ba787c9cba3465e465d1c9c78f4ebc2e2cb8bc59f468cfc5cbc8f4ba9726a5c9a5d2e9764ba5c3830e0c387060c387060c3830e0e061e0e0c3830ea0d1a31e3d1e71e3d1a31e3c7a71e3d3a3468e468e468d1a34e3c7a74623168c462d1a3468d7af47a9d51935464d46a355ea743830e0c387068c1830e8c387060c3830e0c3830e0c3830e0c3a831e8c78f1e3c7e71e3d18f1e3c78f1e3cfa3467cda74f27370f1e3c79b466cf9b0d8b361b166cdaf47a3d469f5364d4d9355e9b4d87061c187061c1870e0c1870e0c187061c187061c1875063c78f1e3e1e3c78fa2e9e8bccc7c3c78f8bc5e1e3c78f1e3c7a3471c2e2cb91c5c5cbc8f47a5d2ea5c9a97269764ba5c3830e0c3830e0c387060c387060e061e0e0c3830ea0c78f479c78f1e3c78f1e3c78f1e3c7a3463c78f878f878f1e3d1a31e0f163c1e2d1e8f51aa3c9a8f1eaa1c187061c187061c383061c383061c187061c187061d418f1f43c78f8ba3a468cbc3c78f1e3c78f1f0f1e3e2f232e8e2e2f16bc2e2c78f1e3d1a3468e2e5e52e4d4b9347a3d2e974bb2f4ba5c387060c387060c3830e0c3830e0e060c3c0c3830e0c3a8300001e3c78f001e3c78f468d1a30047a3d46a355e001c187061c187061c187061d418f1e3c78f1e3c7a3468d18b162c58b162c58b162c5a3d1ea351aaf45a2c3830e0c3830e0c3830e0c3830e0c3a831e3c78f1e8c78f1e3c78f479c78f878f1f0f1e3c7a3468d18f1e0f163c1e3c58f1e3c7a3468d1af5ea3c7a8f268f47a8d46abd4387060c387060c3830e0c3830e0c3830e0c3830e0c3a83368c78f1e3d1e7368d18f1e3e37551faa8dc9eaaa3750fa87d48ea4f546c78f366d19b3e6d39b370cda7aa37442e291e9b51a7d4da9b4eb2cb135a4da6c3830e0c3830e0c387060c387060ea83d50383d07061c1875079e2e6c59b166c25e2c379e2e6c9a4d5655368c78f1e3d1e7366e878f366c78fa468cf8f368d18f1e3ea8d9b87c6cf9f91c7cd9b366cd974f51b939b1e3cd9b466cf9b1d8b360b369cd9b369e36ecd9b91e9b51a7d5d93526a6cba9b2eaed64da6c3830e0c3830e0c387060c387060c387060c387060e0e0c38783830e0c3a832f0f363e2edcd907c8160b2e6cbb72e5c08b805c2e00017012e9709a285c3830e0c061c0e1cbc3cd8f8bb72e6cbb72e5c162c5970b82cb85cdd0b3f42c000597165e162d2e9752e2d268b0e0c3830e1c3830e0d18f1e9cba3a1f27463c7d1787974f0f93978bc5d3a74e3c7a7468c2e2cb82e2e5e47a5d2e9752e4d4b9352eb25d2e1c187061c187061c383061c3830707061c3c1c187061d419b8fc6e1f0f91d46c59b16506c858b82362c163c582eaa166e02162e166ea162d526ca9345c1e061e0e1c3830e0cdc3cd8f918f366cf9f366cd8b362cd80b058b160b361b362c163c582cd8b362c58b02a85c2cb8b2f0b169349aaa4d161c187061c3870e1c187066cd8f1e3c7a3ce6cd9b1e3c79b1e3cd9f468cf9b366cd9b361b160b161b160b161b1380b162c582c586c58b362c580b162c78b1602c5800b858b166c5c2c58b47a6d369b5366d4d9b4da6d4116a2c9a8b161c187061c187061c383061c383061c187061c3807061c383061c383061d419b1e3d1e7366c78f362c59b3e2c59fa858b166ddc3365cb973743365cbc000000974ba4d261c187061c187079c585c0d8f1e8f39b879b1f231e0b0d82c1e00b0580bc5e6cd9f3e6cd85cb8141b0f8000b01d809349a04d503830e0c38030e1c386cd8f1e3c7a3ce00b00d802c01e6cd9b1e3c780b166c78f367d1a33e0011b366e19b366c0036001f0000036270011e9b4da6c40026a6cda9b369b4d88007061c187061c181c00061c383061c383061c1870607000ea0cdc7e370f87c5ea8d82c92693655926aa4d549aa3eaa266d56264d554580b49c1e061e0e87061c19b363c78f1e8f39b366c78f1e6c78f367d1a33e6cb9b365cd9b363c79b366cd9b366cd9b366cd9b366cd9b5549aaa4d5552693526aa93555549935551e3d549c4c993364e262c984c262d4987061c187061c1870e0c1870e0c187061c187061c1a1d54387060c387060d1a31e3c78f479d1a3463c78f4e3c7a7468d3c9e4e3c7a7468d382c4e2d1ea751aa4d5393553a1c187061c187061c383061c383061c187061c187061d41d46cd8f1e6cd972e8d3a3465cb9f4e6e1e3c78fa468d1a32e5cbc3ece3c7d0f1e3cb978b97878fa2e3e8d8f1e6cba7371cdb72e9cda3367cd8cc59b0f8b8b9791e9752efd4ba74ba5d4b9352e4d2ec974b87061c1870e0c1870e0c187061c1870e0c1870e0c1c0c3c1c187061d419f4e3c79f4e7e1e3c78fa3e9d3a787c7e470f1f4cc7d271e3d39f468cf9f198b661f173791ea751a7d599353e4d653a1c187061c187061c383061c38307030f07061c1875063c7d0f1e6e468d3d45cb97366c78f366cb97468d1a32e5d1a72e3e878fa87d9c78fa1e3c7972f172f1b118b3623166c78f365d39b566e3974e6d19b47172f29726a5c9a3d2ea5d5a974e974ba5d92e970e1c1830e1c1830e0c3830e1c1830e1c1830e0c383818783830e0c3a83 24 16777215 10 1023
def nh_70 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_70_19 (Nat.sub p 608)) (hc_70_18 (Nat.sub p 576)) (Nat.blt p 608)) (hc_70_17 (Nat.sub p 544)) (Nat.blt p 576)) (Bool.rec (hc_70_16 (Nat.sub p 512)) (hc_70_15 (Nat.sub p 480)) (Nat.blt p 512)) (Nat.blt p 544)) (Bool.rec (Bool.rec (Bool.rec (hc_70_14 (Nat.sub p 448)) (hc_70_13 (Nat.sub p 416)) (Nat.blt p 448)) (hc_70_12 (Nat.sub p 384)) (Nat.blt p 416)) (Bool.rec (hc_70_11 (Nat.sub p 352)) (hc_70_10 (Nat.sub p 320)) (Nat.blt p 352)) (Nat.blt p 384)) (Nat.blt p 480)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_70_9 (Nat.sub p 288)) (hc_70_8 (Nat.sub p 256)) (Nat.blt p 288)) (hc_70_7 (Nat.sub p 224)) (Nat.blt p 256)) (Bool.rec (hc_70_6 (Nat.sub p 192)) (hc_70_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 224)) (Bool.rec (Bool.rec (Bool.rec (hc_70_4 (Nat.sub p 128)) (hc_70_3 (Nat.sub p 96)) (Nat.blt p 128)) (hc_70_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (hc_70_1 (Nat.sub p 32)) (hc_70_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)) (Nat.blt p 320)
def f_70 : Nat → Nat × Nat := unpackForestF 0x9edaa80317e788bd3c3450062dce8db6744d93a2600062bcc6d2e704a73815398da3cda93e6d48731b459aa2ccd5156634973335d99d294ccd166348f3245998ca580314e5b8b72dc5996e2bcb696e5d8c32da5796cad802d7e596bc00b5b959a3cac52e558c200b57949b74a4d78016a72156b90ab1c851ba4d6892146b92da248518e428c524568909b7c8d5c2426cf2124f90921c8450c0169f2036e005a5c7158a3d8d11c36f8e6b8473582398e11c367005a3c6d1522cad71a4548b2b1c631a6318b31636e8b1af45b16e2d8a716138005a1c54d161e8b314461879aac4d1a21e69f12364879a5c455a21e68f0fb6487c9c43cd0c014bf07c5f86d2241f16e18ce10c26c83e2bc2a9121529107c5384da2c1e97a108bd0845283d2300296e0969704b47825a2c1516609296fcc6181e2cbf2db6058e0fcb4f80dab4035c2016f8fcb4b7feb83f2d1dfaae0fd37c7e9b63f44e1f968600a5778e2fbec911e38b6fa26c78e2bbe11b9f0488f814878e29bd8d75ec6aaf634578d2f3c9179e48b6f2453792293ccd39e46b4f235678d2300294de168ae4d6b77da2b9358ddc8d2ee355726373b5191c96deec354725b5bad1f1c96cee9b6c74daa392d8dc96bee8138725a9b971adcb8c6e5b4e72da1392d15c94c400a4f71d323811bdc4ae0e227c70233b84d55c04dce024600525b7cd15b6ac4de5686d9b7b7252db9286dc5706d9b3b6cd740148eda45564eb5b6515593ac6d826464e37b5c911938d6d5d706ad3e32719da78fcd413b69d2232718d938bed214864e29b26db99f8d2cfb6567daab269b994ad6ca56365235b2918d9969cca36a65e30328d99946bcca35264d2300290d916a8c4d6b63da731b1518d6a8c4d6362e2cb12db9896bc00a3f61d322dd5bd84adcc22545bab5b049f16eacebf3565f92b2fc9516eac6be5695ba37af55c56e8ceb745f5df392dd15d738b2b9b655cda7adc9b96f6deb7b5d5bdaaadc97801476b646854eb7ad516153ad6b447054eb3acb161656a8a9d6358ab4ac4d79538c4aed6e576b12bad1d5d276a9c5256e292a6dbd598c0a9b6755a392ad181536beaa45054dab8028dd514a8a4d6b5392b29c95149ac6a6459525372955a9494bc00a3349e2fa8c511278b6a1e7050cb624f15d4128893c534fcaa24ed7d3d26893b5b4eb382745b1276ae9c13449da9a6c5112769e9a13449da5a645712768e9813449da1a58d152c4b29625149caf251179288a49425349ca300256cf38be921443ce2da445b0f38ae9023747ca21e714d1d2a879b5f46c9a1e6d6d192d879b5745c9a1e6d4d148dc8a1443cda7a244d0f36968814443ab121c570f368e861343cda1a0cd75066aa833454192ea0c954f32bc7a45e3d22d9e914cf48a48034e3d1ad1e8d58f44be7a25b3ee301e895cf94b87a2533d1279e890cf447a7a2353cca300254cf12c86cc6f3bab81dc5f0d98ce76164365b79d44d0d96d67417c365b39cc4d0d96c672134365a59c4570d968e6fb5537d1d9b25b8da4de6d26b369339b498cd928c0094b2a2b595158cd52c85446f34ca21511acd0ae06817c2a23399c510a88c65445f2a229994590a86de641342a1b598c5f0a86ce621342a1b1950d7ca86a6601442a1a797c4d0a86965e15c2a1a39744d0a86865ac692d5aa96a8ecb54665416e2a5b5152d98a96bc54b522a53595d1c0a94ce54a5f2a52995293ca948654146004a194c5906dade51d6e28caa0db5ac9e8f84f37c279b813c5f06dace4d95626caa0db58c99ad236c6f25eb88db19c6d8be4a6721b62b9235a4912c836b6f23c9a0dadac8bae245c5f22cbe0dad9c8926836b6321caa0dad7c846fc421341b5ad9019c8808d84016c1b5ab8f91f87c6fc3e1341b5a98f4df86d6963bd721deb10dad1c728b23934f1c9218e48ec6d2dc3736f1b9ae8dcd546d2bc0093b1acaa09f5ac682ac3415413eb18cb5a4652c827b6f18c9a09edac602ac3015417ab88bc5f04f6ce2e13413db18b45504f6be2b47e159bf0ac4d04f6a629c5914d2189e5b850ad42825113caf0024cc4d2a818d6b12cbe06359c4928818c6b11cbe06319c318be221440c62d8845b0318ae201440c6298771643b6aa1db4f0eda18625b8376ba1bb550dda286257832ad6195670ca2f0651483128c0092b0bcb20055bc2d2a80156b0acbe00559c292a80156309ab484c590028de11c6e08ca20051ac20ae21017c00a3383b1b81d2880146300a2f834510028b60c16c00a2b82c510028a608c59045aa822d3c116860116e036b501b5980d68a0115e00eb58151c003ace01c5e00e2d80714c038a401b6a00db3004518012460003f 10 11
def ch_70 : Nat → Bool := dagCheckNodeV5 fullMask g_70 ep_70 5 31 bds_70 636 (dagTraceF fullMask rootStock 11 f_70) cur_70 nh_70
set_option maxHeartbeats 0 in
theorem rc_70 : dagCheckRootsV5 fullMask g_70 ep_70 5 31 636 bds_70 (dagTraceF fullMask rootStock 11 f_70) (cur_70 0) (nh_70 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_0 : treeBlockF 0 32 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_1 : treeBlockF 32 64 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_2 : treeBlockF 64 96 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_3 : treeBlockF 96 128 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_4 : treeBlockF 128 160 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_5 : treeBlockF 160 192 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_6 : treeBlockF 192 224 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_7 : treeBlockF 224 256 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_8 : treeBlockF 256 288 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_9 : treeBlockF 288 320 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_10 : treeBlockF 320 352 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_11 : treeBlockF 352 384 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_12 : treeBlockF 384 416 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_13 : treeBlockF 416 448 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_14 : treeBlockF 448 480 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_15 : treeBlockF 480 512 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_16 : treeBlockF 512 544 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_17 : treeBlockF 544 576 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_18 : treeBlockF 576 608 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_19 : treeBlockF 608 636 ch_70 = true := by decide +kernel
theorem nj_70_1 : ∀ i, 0 ≤ i → i < 64 → ch_70 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_70_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_70_1 h1 h2)
theorem nj_70_2 : ∀ i, 0 ≤ i → i < 96 → ch_70 i = true := block_join nj_70_1 (fun _ h1 h2 => treeBlockF_at nb_70_2 h1 h2)
theorem nj_70_3 : ∀ i, 0 ≤ i → i < 128 → ch_70 i = true := block_join nj_70_2 (fun _ h1 h2 => treeBlockF_at nb_70_3 h1 h2)
theorem nj_70_4 : ∀ i, 0 ≤ i → i < 160 → ch_70 i = true := block_join nj_70_3 (fun _ h1 h2 => treeBlockF_at nb_70_4 h1 h2)
theorem nj_70_5 : ∀ i, 0 ≤ i → i < 192 → ch_70 i = true := block_join nj_70_4 (fun _ h1 h2 => treeBlockF_at nb_70_5 h1 h2)
theorem nj_70_6 : ∀ i, 0 ≤ i → i < 224 → ch_70 i = true := block_join nj_70_5 (fun _ h1 h2 => treeBlockF_at nb_70_6 h1 h2)
theorem nj_70_7 : ∀ i, 0 ≤ i → i < 256 → ch_70 i = true := block_join nj_70_6 (fun _ h1 h2 => treeBlockF_at nb_70_7 h1 h2)
theorem nj_70_8 : ∀ i, 0 ≤ i → i < 288 → ch_70 i = true := block_join nj_70_7 (fun _ h1 h2 => treeBlockF_at nb_70_8 h1 h2)
theorem nj_70_9 : ∀ i, 0 ≤ i → i < 320 → ch_70 i = true := block_join nj_70_8 (fun _ h1 h2 => treeBlockF_at nb_70_9 h1 h2)
theorem nj_70_10 : ∀ i, 0 ≤ i → i < 352 → ch_70 i = true := block_join nj_70_9 (fun _ h1 h2 => treeBlockF_at nb_70_10 h1 h2)
theorem nj_70_11 : ∀ i, 0 ≤ i → i < 384 → ch_70 i = true := block_join nj_70_10 (fun _ h1 h2 => treeBlockF_at nb_70_11 h1 h2)
theorem nj_70_12 : ∀ i, 0 ≤ i → i < 416 → ch_70 i = true := block_join nj_70_11 (fun _ h1 h2 => treeBlockF_at nb_70_12 h1 h2)
theorem nj_70_13 : ∀ i, 0 ≤ i → i < 448 → ch_70 i = true := block_join nj_70_12 (fun _ h1 h2 => treeBlockF_at nb_70_13 h1 h2)
theorem nj_70_14 : ∀ i, 0 ≤ i → i < 480 → ch_70 i = true := block_join nj_70_13 (fun _ h1 h2 => treeBlockF_at nb_70_14 h1 h2)
theorem nj_70_15 : ∀ i, 0 ≤ i → i < 512 → ch_70 i = true := block_join nj_70_14 (fun _ h1 h2 => treeBlockF_at nb_70_15 h1 h2)
theorem nj_70_16 : ∀ i, 0 ≤ i → i < 544 → ch_70 i = true := block_join nj_70_15 (fun _ h1 h2 => treeBlockF_at nb_70_16 h1 h2)
theorem nj_70_17 : ∀ i, 0 ≤ i → i < 576 → ch_70 i = true := block_join nj_70_16 (fun _ h1 h2 => treeBlockF_at nb_70_17 h1 h2)
theorem nj_70_18 : ∀ i, 0 ≤ i → i < 608 → ch_70 i = true := block_join nj_70_17 (fun _ h1 h2 => treeBlockF_at nb_70_18 h1 h2)
theorem nj_70_19 : ∀ i, 0 ≤ i → i < 636 → ch_70 i = true := block_join nj_70_18 (fun _ h1 h2 => treeBlockF_at nb_70_19 h1 h2)
theorem nc_70 : ∀ i, 0 ≤ i → i < 636 → ch_70 i = true := nj_70_19
theorem lb_70 : LowerBin fullMask rootStock g_70 12 :=
  lowerDagV5 (kn_cons lb_65 (kn_cons lb_69 (kn_cons lb_63 (kn_cons lb_66 (kn_cons lb_67 (kn_cons lb_62 (kn_cons lb_61 (kn_cons lb_68 (kn_cons lb_53 (kn_cons lb_8 (kn_cons lb_4 (kn_cons lb_64 (kn_cons lb_19 (kn_cons lb_12 (kn_cons lb_31 (kn_cons lb_55 (kn_cons lb_42 (kn_cons lb_59 (kn_cons lb_7 (kn_cons lb_52 (kn_cons lb_28 (kn_cons lb_38 (kn_cons lb_34 (kn_cons lb_56 (kn_cons lb_54 (kn_cons lb_57 (kn_cons lb_35 (kn_cons lb_58 (kn_nil))))))))))))))))))))))))))))) rc_70 nc_70 (by decide +kernel)

def wg : List Gate := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.or, [2, 9]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [0, 12]⟩, ⟨GateOp.or, [4, 10]⟩, ⟨GateOp.and, [5, 13]⟩, ⟨GateOp.and, [8, 14]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.and, [11, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 3974684800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276677288 * 2 ^ 32 + 3974684800)) (13 - 1) := by
  rw [show canon fullMask (4276677288 * 2 ^ 32 + 3974684800) = g_70 by decide]
  exact lb_70

end PEqualNP.Outside.L_meta_48352

theorem PEqualNP.Outside.L_meta_48352 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677288 * 2 ^ 32 + 3974684800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 3974684800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_48352.table2_from_lowerBin (4276677288 * 2 ^ 32 + 3974684800) 13 PEqualNP.Outside.L_meta_48352.root_lb PEqualNP.Outside.L_meta_48352.wg 18 rfl PEqualNP.Outside.L_meta_48352.wfits PEqualNP.Outside.L_meta_48352.weval
